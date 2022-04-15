## Code layout

The PDF handout explains most of the core Dafny files.  This code bundle
contains a few additional files of interest.

- `MiniC.g4` describes the grammar of MiniC in a format that [ANTLR](https://www.antlr.org/)
  recognizes and turns into a parser for us.  The output of ANTLR (i.e., our
  parser files) lives in the `parser` directory.

- `MiniC/AstBuilder.cs` maps the AST provided by ANTLR to a corresponding AST
  constructed out of the Dafny datatypes defined in `def.dfy`.

- `MiniC/Util.cs` provides a number of helpful utilities.  It also supplies the
  implementations of the {:extern} function methods defined in the Dafny source
  code.

- `main.dfy` defines two different ways of running a MiniC file, either by
  applying our security type system and then using the standard interpreter
  (`EvalCommand`) defined in our semantics, or by running it using the taint
  analysis engine (defined by `EvalCommandTaint`).

- `MiniC/Program.cs` ties everything together and contains the main entry point
  for the C# program.

- `MiniC/MiniC.{csproj,sln}` are the .NET equivalent of Makefiles.

- The `samples` directory holds various simple MiniC programs that you can try
  running with your implementation.

- If you decide to attempt the extra credit, you'll need to edit 
  `taint_leak_attack.py` and `taint-leak.mc`, and/or 
  `type_leak_attack.py` and `type-leak.mc`.
  

## Instructions for running a MiniC program

### Setup
Option 1:
  1) Install Dotnet SDK on your machine by following instructions provided in the link below:

      ```
      https://docs.microsoft.com/en-us/dotnet/core/install/
      ```

  2) Install Dafny 3.5.0 

      ```
      https://github.com/dafny-lang/dafny/releases/tag/v3.5.0
      ```


Option 2:
  1) Build the provided Docker image (following the directions in the Dockerfile)

  2) Start the Docker container (following the directions in the Dockerfile)

### Execution
Run your MiniC program.  Note: Make sure the ```out``` directory is in the same folder as your main.dfy

  1) Compile your Dafny code to C# (producing `main.cs`)
      ```
      dafny /compile:0 /spillTargetCode:3 main.dfy 
      ```

  2) Run the C# program
      ```
      dotnet run --project MiniC/MiniC.csproj (taint|sectype) [filename.mc]
      ```


