/*
 * CoreASMError.java 		$Revision: 94 $
 * 
 * Copyright (c) 2009 Roozbeh Farahbod
 *
 * Last modified on $Date: 2009-08-03 15:23:52 +0200 (Mo, 03 Aug 2009) $  by $Author: rfarahbod $
 * 
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 */


package org.coreasim.engine;

import java.util.Stack;

import org.coreasim.engine.interpreter.Node;
import org.coreasim.engine.interpreter.Interpreter.CallStackElement;
import org.coreasim.engine.parser.CharacterPosition;
import org.coreasim.engine.parser.Parser;
import org.coreasim.engine.parser.ParserException;

/**
 * Represents a general error in CoreASM engine. 
 *   
 * @author Roozbeh Farahbod
 *
 */

public class CoreASIMError extends CoreASIMIssue {

	private static final long serialVersionUID = 1L;
	
	public CoreASIMError(String msg, Throwable cause, CharacterPosition pos, Stack<CallStackElement> stack, Node node) {
		super(msg, cause, pos, stack, node);
	}
	
	public CoreASIMError(String msg, Stack<CallStackElement> stack, Node node) {
		this(msg, null, null, stack, node);
	}
	
	public CoreASIMError(Throwable cause, Stack<CallStackElement> stack, Node node) {
		this(null, cause, null, stack, node);
	}
	
	public CoreASIMError(String msg, CharacterPosition pos) {
		this(msg, null, pos, null, null);
	}
	
	public CoreASIMError(String msg, Node node) {
		this(msg, null, null, null, node);
	}
	
	public CoreASIMError(String msg) {
		this(msg, null, CharacterPosition.NO_POSITION, null, null);
	}
	
	public CoreASIMError(ParserException cause) {
		this(cause.msg, cause, cause.pos, null, null);
	}
	
	/**
	 * Creates and returns a string representation of this error.
	 */
	public String showError(Parser parser, Specification spec) {
		return showIssue(parser, spec);
	}
	
	public String showError() {
		return showError(parser, spec);
	}
	
}
