include "taint-tracking.dfy"
include "security-types.dfy"

//////////////////////////////////////////////////////////////////
//
//  Our Main Executable Routines
//
//////////////////////////////////////////////////////////////////

// Two externally provided parsing routines
method {:extern} ParseFileNormal(filename:string) returns (d:Declarations, c:Command)
method {:extern} ParseFileSecTypes(filename:string) returns (d:SecDeclarations, c:Command)

// Given a MiniC file, run it through our dynamic taint-analysis engine
method RunCommandTaintAnalysis(filename:string, ghost io:IO) 
{
    var decls, cmd := ParseFileNormal(filename);

    if !CommandWellTyped(decls, cmd) {
        print("Sorry, the command is not well typed.\n");
    } else {
        // Establish default values: 
        // Booleans default to false, and Integers default to 0
        var store := map v | v in decls :: if decls[v].TBool? then B(false) else I(0);

        // Initially, all variables are untainted, as is the PC
        var vars_map := map v | v in decls :: false;
        var taint_state := TaintState(0xFFFF_FFFF, store, io, false, vars_map);

        // Run the program
        var result := EvalCommandTaint(decls, taint_state, cmd);

        // Process the results
        match result {
            case TTimeout => print "\nExecution timed out.  You probably have an infinite loop in your code.\n";
            case TLeak => print "\nYour program tried to leak a secret, but we caught you!\n";
            case TSuccess(_) => print "\nCongratulations, your program ran to completion.\n";
        }
    }
}

// Given a MiniC file with security types,
// check whether it can be properly typed at Low or High
// and then execute it
method RunCommandSecTypes(filename:string, ghost io:IO) 
{
    var decls, cmd := ParseFileSecTypes(filename);

    if CommandHasSecType(decls, cmd, Low) {
        print("Command is well typed at Low\n");
    } else if CommandHasSecType(decls, cmd, High) {
        print("Command is well typed at High\n");
    } else {
        print("Sorry, the command is not well typed.\n");
        return;
    }        

    // Establish an initial store mapping everything to false 
    var store := map v | v in decls :: B(false);
    var state := State(0xFFFF_FFFF, store, io);

    // Run the program
    var result := EvalCommand(state, cmd);

    // Process the results
    match result {
        case Timeout => print "\nExecution timed out.  You probably have an infinite loop in your code.\n";
        case Fail    => print "\nSorry, your program failed during execution.\n";
        case Success(_,_) => print "\nCongratulations, your program ran to completion.\n";
    }    
}
