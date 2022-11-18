// pest. The Elegant Parser
// Copyright (c) 2018-2022 Dragoș Tiselice, Tomas Tauber
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.
//! # pest debugger
//!
//! This crate contains definitions for the debugger.

#![doc(
    html_logo_url = "https://raw.githubusercontent.com/pest-parser/pest/master/pest-logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/pest-parser/pest/master/pest-logo.svg"
)]
#![warn(missing_docs, rust_2018_idioms, unused_qualifications)]
use std::{
    collections::HashSet,
    fs::File,
    io::{self, Read},
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::Sender,
        Arc, Mutex,
    },
    thread::{self, JoinHandle},
};

use pest::{error::Error, Position};
use pest_meta::{optimizer::OptimizedRule, parse_and_optimize, parser::Rule};
use pest_vm::Vm;

#[derive(Debug, thiserror::Error)]
pub enum DebuggerError {
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),
    #[error("Missing filename")]
    MissingFilename,
    #[error("Open grammar first")]
    GrammarNotOpened,
    #[error("Open input first")]
    InputNotOpened,
    #[error("Run rule first")]
    RunRuleFirst,
    #[error("End-of-input reached")]
    EofReached,
    #[error("Invalid position: {0}")]
    InvalidPosition(usize),
    #[error("Grammar error: {0}")]
    IncorrectGrammar(String, Vec<Error<Rule>>),
    #[error("Previous parsing execution panic: {0}")]
    PreviousRunPanic(String),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    Breakpoint(String, usize),
    Eof,
    Error(String),
}

pub struct Context {
    handle: Option<JoinHandle<()>>,
    is_done: Arc<AtomicBool>,
    grammar: Option<Vec<OptimizedRule>>,
    input: Option<String>,
    breakpoints: Arc<Mutex<HashSet<String>>>,
}

const POISONED_LOCK_PANIC: &str = "poisoned lock";
const CHANNEL_CLOSED_PANIC: &str = "channel closed";

impl Context {
    fn file_to_string(path: &PathBuf) -> Result<String, DebuggerError> {
        let mut file = File::open(path)?;

        let mut string = String::new();
        file.read_to_string(&mut string)?;

        Ok(string)
    }

    pub fn load_grammar(&mut self, path: &PathBuf) -> Result<(), DebuggerError> {
        let grammar = Context::file_to_string(path)?;

        let file_name = path
            .file_name()
            .map(|string| string.to_string_lossy().into_owned())
            .ok_or(DebuggerError::MissingFilename)?;

        self.grammar = Some(Context::parse_grammar(&file_name, &grammar)?);

        Ok(())
    }

    pub fn load_grammar_direct(
        &mut self,
        file_name: &str,
        grammar: &str,
    ) -> Result<(), DebuggerError> {
        self.grammar = Some(Context::parse_grammar(file_name, grammar)?);

        Ok(())
    }

    pub fn load_input(&mut self, path: &PathBuf) -> Result<(), DebuggerError> {
        let input = Context::file_to_string(path)?;

        self.input = Some(input);

        Ok(())
    }

    pub fn load_input_direct(&mut self, input: String) {
        self.input = Some(input);
    }

    pub fn add_all_rules_breakpoints(&mut self) -> Result<(), DebuggerError> {
        let ast = self
            .grammar
            .as_ref()
            .ok_or(DebuggerError::GrammarNotOpened)?;
        let mut breakpoints = self.breakpoints.lock().expect(POISONED_LOCK_PANIC);
        for rule in ast {
            breakpoints.insert(rule.name.clone());
        }

        Ok(())
    }

    pub fn add_breakpoint(&mut self, rule: String) {
        let mut breakpoints = self.breakpoints.lock().expect(POISONED_LOCK_PANIC);

        breakpoints.insert(rule);
    }

    pub fn delete_breakpoint(&mut self, rule: &str) {
        let mut breakpoints = self.breakpoints.lock().expect(POISONED_LOCK_PANIC);

        breakpoints.remove(rule);
    }

    pub fn delete_all_breakpoints(&mut self) {
        let mut breakpoints = self.breakpoints.lock().expect(POISONED_LOCK_PANIC);

        breakpoints.clear();
    }

    pub fn list_breakpoints(&self) -> Vec<String> {
        let breakpoints = self.breakpoints.lock().expect(POISONED_LOCK_PANIC);
        let mut breakpoints: Vec<_> = breakpoints.iter().map(ToOwned::to_owned).collect();
        breakpoints.sort();
        breakpoints
    }

    fn handle(
        &self,
        ast: Vec<OptimizedRule>,
        rule: String,
        input: String,
        sender: Sender<Event>,
    ) -> JoinHandle<()> {
        let breakpoints = Arc::clone(&self.breakpoints);
        let is_done = Arc::clone(&self.is_done);
        let is_done_signal = Arc::clone(&self.is_done);

        let rsender = sender.clone();
        thread::spawn(move || {
            let vm = Vm::new_with_listener(
                ast,
                Box::new(move |rule, pos| {
                    if is_done_signal.load(Ordering::SeqCst) {
                        return true;
                    }
                    let lock = breakpoints.lock().expect(POISONED_LOCK_PANIC);

                    if lock.contains(&rule) {
                        rsender
                            .send(Event::Breakpoint(rule, pos.pos()))
                            .expect(CHANNEL_CLOSED_PANIC);

                        thread::park();
                    }
                    false
                }),
            );

            match vm.parse(&rule, &input) {
                Ok(_) => sender.send(Event::Eof).expect(CHANNEL_CLOSED_PANIC),
                Err(error) => sender
                    .send(Event::Error(error.to_string()))
                    .expect(CHANNEL_CLOSED_PANIC),
            };

            is_done.store(true, Ordering::SeqCst);
        })
    }

    fn parse_grammar(file_name: &str, grammar: &str) -> Result<Vec<OptimizedRule>, DebuggerError> {
        match parse_and_optimize(grammar) {
            Ok((_, ast)) => Ok(ast),
            Err(errors) => {
                let msg = format!(
                    "error parsing {:?}\n\n{}",
                    file_name,
                    errors
                        .iter()
                        .cloned()
                        .map(|error| format!(
                            "{}",
                            error.renamed_rules(|rule| match *rule {
                                Rule::grammar_rule => "rule".to_owned(),
                                Rule::_push => "PUSH".to_owned(),
                                Rule::assignment_operator => "`=`".to_owned(),
                                Rule::silent_modifier => "`_`".to_owned(),
                                Rule::atomic_modifier => "`@`".to_owned(),
                                Rule::compound_atomic_modifier => "`$`".to_owned(),
                                Rule::non_atomic_modifier => "`!`".to_owned(),
                                Rule::opening_brace => "`{`".to_owned(),
                                Rule::closing_brace => "`}`".to_owned(),
                                Rule::opening_paren => "`(`".to_owned(),
                                Rule::positive_predicate_operator => "`&`".to_owned(),
                                Rule::negative_predicate_operator => "`!`".to_owned(),
                                Rule::sequence_operator => "`&`".to_owned(),
                                Rule::choice_operator => "`|`".to_owned(),
                                Rule::optional_operator => "`?`".to_owned(),
                                Rule::repeat_operator => "`*`".to_owned(),
                                Rule::repeat_once_operator => "`+`".to_owned(),
                                Rule::comma => "`,`".to_owned(),
                                Rule::closing_paren => "`)`".to_owned(),
                                Rule::quote => "`\"`".to_owned(),
                                Rule::insensitive_string => "`^`".to_owned(),
                                Rule::range_operator => "`..`".to_owned(),
                                Rule::single_quote => "`'`".to_owned(),
                                other_rule => format!("{:?}", other_rule),
                            })
                        ))
                        .collect::<Vec<_>>()
                        .join("\n")
                );
                Err(DebuggerError::IncorrectGrammar(msg, errors))
            }
        }
    }

    pub fn run(&mut self, rule: &str, sender: Sender<Event>) -> Result<(), DebuggerError> {
        if let Some(handle) = self.handle.take() {
            if !(self.is_done.load(Ordering::Relaxed)) {
                self.is_done.store(true, Ordering::SeqCst);
                handle.thread().unpark();
            }
            handle
                .join()
                .map_err(|e| DebuggerError::PreviousRunPanic(format!("{:?}", e)))?;
        }

        self.is_done.store(false, Ordering::SeqCst);
        let ast = self
            .grammar
            .as_ref()
            .ok_or(DebuggerError::GrammarNotOpened)?;
        match self.input {
            Some(ref input) => {
                let rule = rule.to_owned();
                let input = input.clone();

                self.handle = Some(self.handle(ast.clone(), rule, input, sender));
                Ok(())
            }
            None => Err(DebuggerError::InputNotOpened),
        }
    }

    pub fn cont(&self) -> Result<(), DebuggerError> {
        if self.is_done.load(Ordering::SeqCst) {
            return Err(DebuggerError::EofReached);
        }

        match self.handle {
            Some(ref handle) => {
                handle.thread().unpark();
                Ok(())
            }
            None => Err(DebuggerError::RunRuleFirst),
        }
    }

    pub fn get_position(&self, pos: usize) -> Result<Position<'_>, DebuggerError> {
        match self.input {
            Some(ref input) => Position::new(input, pos).ok_or(DebuggerError::InvalidPosition(pos)),
            None => Err(DebuggerError::InputNotOpened),
        }
    }
}

impl Default for Context {
    fn default() -> Self {
        Self {
            handle: None,
            is_done: Arc::new(AtomicBool::new(false)),
            grammar: None,
            input: None,
            breakpoints: Arc::new(Mutex::new(HashSet::new())),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::sync::mpsc::channel;

    #[test]
    fn test_full_flow() {
        let mut context = Context::default();

        context
            .load_grammar_direct(
                "testgrammar",
                r#"alpha = { 'a'..'z' | 'A'..'Z' }
            digit = { '0'..'9' }
            
            ident = { !digit ~ (alpha | digit)+ }
            
            ident_list = _{ ident ~ (" " ~ ident)* }"#,
            )
            .expect("Error: failed to load grammar");
        context.load_input_direct("test test2".to_owned());

        let (sender, receiver) = channel();

        assert_eq!(context.list_breakpoints().len(), 0);
        context.add_breakpoint("ident".to_owned());
        assert_eq!(context.list_breakpoints().len(), 1);
        context
            .run("ident_list", sender)
            .expect("Error: failed to run rule");

        let event = receiver.recv().expect("Error: failed to receive event");
        assert_eq!(event, Event::Breakpoint("ident".to_owned(), 0));

        context.cont().expect("Error: failed to continue");

        let event = receiver.recv().expect("Error: failed to receive event");
        assert_eq!(event, Event::Breakpoint("ident".to_owned(), 5));
        context.cont().expect("Error: failed to continue");
        let event = receiver.recv().expect("Error: failed to receive event");

        assert_eq!(event, Event::Eof);
        context
            .add_all_rules_breakpoints()
            .expect("grammar is loaded");
        assert_eq!(context.list_breakpoints().len(), 4);
        context.delete_breakpoint("ident");
        assert_eq!(context.list_breakpoints().len(), 3);
        context.delete_all_breakpoints();
        assert_eq!(context.list_breakpoints().len(), 0);
    }

    #[test]
    pub fn test_errors() {
        let mut context = Context::default();

        assert!(context.load_input(&PathBuf::from(".")).is_err());
        let pest_readme = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../README.md"));
        let pest_grammar = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../meta/src/grammar.pest"
        ));

        assert!(context.load_grammar(&pest_readme).is_err());
        assert!(context.add_all_rules_breakpoints().is_err());
        assert!(context.cont().is_err());
        assert!(context.run("rule", channel().0).is_err());
        assert!(context.load_grammar(&pest_grammar).is_ok());
        assert!(context.run("rule", channel().0).is_err());
        assert!(context.get_position(0).is_err());
        context.load_input_direct("".to_owned());
        assert!(context.get_position(0).is_ok());
        assert!(context.get_position(1).is_err());
        let (sender, _receiver) = channel();
        assert!(context.run("ANY", sender).is_ok());
        while context.cont().is_ok() {}
        assert!(context.cont().is_err());
    }
}
