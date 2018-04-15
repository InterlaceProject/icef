/*
 * ASIMCreationRequest.java v1.0
 *
 * This file contains source code developed by the European
 * FP7 research project BIOMICS (Grant no. 318202)
 * Copyright (C) 2016 Daniel Schreckling
 *
 * Licensed under the Academic Free License version 3.0
 *   http://www.opensource.org/licenses/afl-3.0.php
 *
 *
 */

package org.coreasim.biomics;

import com.fasterxml.jackson.annotation.JsonProperty;

import org.coreasim.engine.absstorage.AgentCreationElement;

import com.fasterxml.jackson.annotation.JsonCreator;

public class ASIMCreationRequest {
    public String name;
    public String simulation;
    public String signature; 
    public String init; 
    public String program;
    public String policy;
    public boolean start;

    @JsonCreator
    public ASIMCreationRequest(@JsonProperty("name") String name, 
                               @JsonProperty("simulation") String simulation, 
                               @JsonProperty("signature") String signature,
                               @JsonProperty("init") String init,
                               @JsonProperty("program") String program,
                               @JsonProperty("policy") String policy,
                               @JsonProperty("start") boolean start) {
        this.name = name;
        this.simulation = simulation;
        this.signature = signature;
        this.init = init;
        this.program = program;
        this.policy = policy;
        this.start = start;
    }

    public ASIMCreationRequest(AgentCreationElement e, String simId) {
        simulation = simId;
        name = e.getName().toString();

        signature = e.getSignature() + "\\n";
        signature = e.getInitRule().getDeclarationNode().unparseTree() + "\\n\\n";
        signature += e.getInitRule().getDeclarationNode().unparseTree() + "\\n\\n";
        signature += e.getProgram().getDeclarationNode().unparseTree() + "\\n\\n";
        signature += e.getPolicy().getDeclarationNode().unparseTree() + "\\n\\n";

        init = e.getInitRule().getName();
        program = e.getProgram().getName();
        policy = e.getPolicy().getName();
        start = true;
    }
}
