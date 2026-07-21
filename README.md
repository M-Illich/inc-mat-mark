# Evaluation of Delete/Rederive and Backward/Forward with Marking for Update Streams
This project allows for an evaluation of both Delete/Rederive and Backward/Forward with Marking, which are extensions of the classical [Delete/Rederive](https://doi.org/10.1145/170035.170066) (DRed)  and [Backward/Forward](https://doi.org/10.1609/aaai.v29i1.9409) (B/F) algorithms with focus on processing streams of updates for a materialized dataset in Datalog.
The general idea of the evaluated approach is that we mark facts that are added or deleted by the next update in the stream, so that we can directly perform some computations that are relevant for the the next update without introducing additional rule applications and, thus, reduce the overall processing time of the stream.
Tests are provided for both synthetic and real data to compare the marking approach with the classical algorithms based on the needed processing time, as well as the number of applied rule applications.
The selection and execution of the tests is done in the `Evaluation` class.

# Prerequisites: 
- [Java v22](https://www.oracle.com/java/technologies/downloads/) and [Maven v4](https://maven.apache.org/)
- [SWI-Prolog v9](https://www.swi-prolog.org/Download.html) or [Docker](https://www.docker.com)

# Preparations
1. Clone the repository
   ```
   git clone https://github.com/M-Illich/inc-mat-mark
   ```

2. Go to the root directory of the repository and install the maven project with the following command
    ```
    mvn clean package
    ```
	which will generate a `jar` file located in the same folder. 
	

# Option 1: Execution with SWI-Prolog
1. Ensure that SWI-Prolog is correctly installed with
	```
    swipl --version
    ```
	
2. Execute the `jar` file with 	
	```
    java -jar inc-mat-mark-1.0.jar A C K R
    ```
	with the following options:

	`A` (algorithm): `dred` or `bf`

	`C` (test case): `random`, `random-large`, `batch`, `overlap`, `scale-update`, `scale-data`, or `real`

	`K` (knowledge base): `path`, `sequence`, `claros`, `dbpedia`, `family`, `lubm`, `relations`, or `ways` (only with `C` = `real`)

	`R` (test run): `0`, `1`, or `2`, where each run uses a different, predefined update stream

4. Once the evaluation is finished, the measured statistics (time etc.) will be available in `csv`-files in the folder `results`.
	

# Option 2: Execution with Docker
1. Call
    ```
    docker build -t eval .
    ```
    which will build a docker image with the name tag `eval`.
	
2. Run an evaluation with
    ```
    docker run --name=eval_container -e ALGO=A -e CASE=C -e KB=K -e RUN=R eval
    ```
	where `A`,`C`, `K`, and `R` have to be replaced in the same way as explained above for the `jar` execution.
	
3. Copy measured results from docker container	
   ```
    docker cp eval_container:app/results .
    ```

----------------------------------------------------------------------------------------------

Copyright 2026 Moritz Illich

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
