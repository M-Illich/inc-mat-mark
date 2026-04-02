# Evaluation of Delete/Rederive and Backward/Forward with Marking for Update Streams
This project allows for an evaluation of both Delete/Rederive and Backward/Forward with Marking, which are extensions of the classical [Delete/Rederive](https://doi.org/10.1145/170035.170066) (DRed)  and [Backward/Forward](https://doi.org/10.1609/aaai.v29i1.9409) (B/F) algorithms with focus on processing streams of updates for a materialized dataset in Datalog.
The general idea of the evaluated approach is that we mark facts that are deleted by the next update in the stream, which then allows us to reduce the number of performed rule applications during the processing of the next update.


# Prerequisites: 
- [Java v.25](https://www.oracle.com/java/technologies/downloads/)
- [SWI-Prolog v.10](https://www.swi-prolog.org/Download.html)


# General Information:
- Algorithms are implemented in Constraint Handling Rules (CHR) based on SWI-Prolog ([link](https://www.swi-prolog.org/pldoc/man?section=chr))
- For a given set of Datalog rules, we consider five CHR programs: DRed with(out) Marking, B/F with(out) Marking, and non-incremental materialization
- At the moment, Datalog rules have to be manually transformed into suitable CHR programs
- Java code is used to conduct the evaluation (based on `src/main/java/eval/Evaluation`) by providing an update stream over a local port, calling the tested algorithm, and reading the produced answer stream
- During the execution of a CHR program, we measure the needed CPU time, the number of applied rules for each algorithm phase, and the number of marked facts (if available)
