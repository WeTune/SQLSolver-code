# SQLSolver
SQLSolver is an automated prover for the equivalence of two SQL queries.

## Codebase

This codebase includes the source code and the testing scripts.
```text
.
|-- common/            # Common utilities.
|-- lib/               # Required external library.
|-- runners/           # Click-to-run scripts for SQLSolver.
|-- sql/               # Data structures of SQL AST and query plan.
|-- stmt/              # Manager of queries from open-source applications.
|-- superopt/.../      # Core algorithm of SQLSolver.
    |-- constraint/    # Constraint enumeration.
    |-- fragment/      # Plan template enumeration.
    |-- liastar/       # Core algorithm of LIA*.
    |-- logic/         # SMT-based verifier.
    |-- optimizer/     # Rewriter.
    |-- uexpr/         # U-expression.
    |-- util/          # Tools.
|-- testbed/           # Evaluation framework.
|-- wtune_data/        # Data input/output directory.
```

## Environment setup

### Requirements

- Ubuntu (22.04.1 LTS is tested)
- Python 3
- Java 17
- Gradle 7.3.3
- z3 4.8.9 (SMT solver)
- antlr 4.8 (Generate tokenizer and parser for SQL AST)
- SQL Server 2019 (Optional; evaluate query performance)

The z3 and antlr libraries have been put in `lib/` off-the-shelf.

#### Install Python

Python is typically installed by default.
Type `python3 --version` to check whether Python 3 is installed.
In cases where it is not installed, use this following instruction:

```shell
sudo apt install python3
```

#### Install Java and Gradle

If you do not have Java or Gradle installed, you may refer to these instructions:

```shell
# Installing Java 17
sudo add-apt-repository ppa:linuxuprising/java
sudo apt update
sudo apt-get install -y oracle-java17-installer oracle-java17-set-default

# Installing Gradle 7.3.3
wget https://services.gradle.org/distributions/gradle-7.3.3-bin.zip -P /tmp
sudo unzip -d /opt/gradle /tmp/gradle-7.3.3-bin.zip
sudo touch /etc/profile.d/gradle.sh
sudo chmod a+wx /etc/profile.d/gradle.sh
sudo echo -e "export GRADLE_HOME=/opt/gradle/gradle-7.3.3 \nexport PATH=\${GRADLE_HOME}/bin:\${PATH}" >> /etc/profile.d/gradle.sh
source /etc/profile
```

#### Install SQL Server (Optional)

This step is only required if you intend to evaluate query performance before and after rewrites in the case study.

First, refer to [this site](https://learn.microsoft.com/en-us/sql/linux/sql-server-linux-setup-tools?view=sql-server-ver15&tabs=ubuntu-install#install-tools-on-linux) to install `sqlcmd`, which acts as a client.
In Ubuntu 20.04, the suggested sequence of instructions looks like this:

```shell
curl https://packages.microsoft.com/keys/microsoft.asc | sudo tee /etc/apt/trusted.gpg.d/microsoft.asc
curl https://packages.microsoft.com/config/ubuntu/20.04/prod.list | sudo tee /etc/apt/sources.list.d/mssql-release.list
sudo apt-get update
sudo apt-get install mssql-tools
echo 'export PATH="$PATH:/opt/mssql-tools/bin"' >> ~/.bashrc
source ~/.bashrc
```

In different releases of Ubuntu, replace "20.04" with the corresponding version number (e.g. "18.04" for Bionic and "16.04" for Xenial).

Then, pull the docker image of SQL Server 2019:

```shell
sudo docker pull mcr.microsoft.com/mssql/server:2019-latest
```

Finally, run a container using that docker image:

```shell
sudo docker run -e "ACCEPT_EULA=Y" -e "MSSQL_SA_PASSWORD=mssql2019Admin" \
   -p 1433:1433 --name sql1 --hostname sql1 \
   -d \
   mcr.microsoft.com/mssql/server:2019-latest
```

That also configures the password for the user "SA".
Note that you have to run that container again if you reboot your machine.

You can test whether you are able to connect SQL Server:

```shell
sqlcmd -U SA -p
# Then enter the password "mssql2019Admin"
# Once you connect SQL Server, type "exit" or "quit" to terminate the connection.
```

### Compilation

```shell
gradle compileJava
```

## Architecture

SQLSolver accepts two SQL queries as its input and outputs the verification result, which is either `EQ` or `NEQ`.
As shown in the following architecture, SQLSolver checks the equivalence of two given SQL queries through the following steps:

<div align="center">


<img alt="architecture" src="arch.jpg"/>
</div>

1. Address ORDER-BYs in the given SQL queries and output new SQL queries ([sortHandler](superopt/src/main/java/wtune/superopt/logic/OrderbySupport.java)) .
2. Translate each SQL query without ORDER-BYs to an algebra called U-expression ([translateQueryToUExpr](superopt/src/main/java/wtune/superopt/uexpr/UExprSupport.java)).
3. Translate the two U-expressions into a LIA formula, which is a FOL formula about integers. ([uexpToLiastar](superopt/src/main/java/wtune/superopt/logic/SqlSolverSupport.java))
4. Solve the LIA formula via an SMT solver.

## Usage

### Prepare table schemas and queries

First, include table schemas along with integrity constraints in a file.
The file should be a SQL file comprising `CREATE TABLE` statements written in MySQL grammar.
The file path should be `wtune_data/schemas/APP_NAME.base.schema.sql`
where `APP_NAME` is passed to CLI later as a parameter.

Then, prepare pairs of queries to be verified in another file.
The file should contain `2*N` lines, where `N` is a positive integer indicating that there are `N` pairs of queries in the file, and each line should contain exactly one query.
For each integer `i` in `[1, N]`, the queries at line `2*i-1` and line `2*i` constitute a pair, and the equivalence of those two queries is to be verified.

### Run in shell

```shell
python3 runners/run-sqlsolver.py [-time] [-app APP_NAME] [-input INPUT_FILE] [-rounds ROUNDS] [-target TARGET] [-skip SKIPPED_PAIR] [-out OUTPUT_FILE] [-tsv TIME_FILE] [-tsv_neq]
```

The script supports the following options:

* `-time`: Output the verification latency (milliseconds) for each pair of equivalent queries that can be proved by the prover. Each pair will be proved 5 times by default (which can be configured via the option `-rounds` described below). The script calculates the average verification latency for each pair.
* `-app APP_NAME`: Specify the app name, which indicates the schema name `wtune_data/schemas/APP_NAME.base.schema.sql`.
* `-input INPUT_FILE`: Specify the input file containing SQL queries.

Since SQLSolver may spend much time in proving some cases, the script supports the following options to skip some pairs and configure the repetition count:

* `-skip SKIPPED_PAIR`: Skip the pairs specified by `SKIPPED_PAIR`. For example, `-skip 220` skips the 220th pair.
* `-target TARGET`: Invoke the prover to verify only the pair with the specified identifier `TARGET`. For example, `-target 220` will ask the prover to verify only the 220th pair.
* `-rounds ROUNDS`: Each successfully verified pair is proved `ROUNDS` times if `-time` is set. The average verification latency is regarded as the running time of that pair.
  The default value of `ROUND` is 5.

To persist the output into a file, the script provides the following options:

* `-out OUTPUT_FILE`: Save results in a text file, namely `OUTPUT_FILE`.
* `-tsv`: Record verification time (milliseconds) in a file, where the n-th line contains the verification time of the n-th pair.
  By default, if a pair results in NEQ, its verification time is not recorded and corresponds to empty lines in the file.
  The default file name is `tmp_result.tsv`.
  This option is ignored if `-time` is not set.
* `-tsv_neq`: Record the verification time of all pairs in the file specified by `-tsv` even though some of them may result in NEQ.
  This option is ignored if `-time` is not set.

## Evaluation scripts

We have prepared some scripts to evaluate SQLSolver.

### Evaluate SQLSolver on test sets

The following command runs a script that evaluates SQLSolver on a set of equivalent query pairs.

```shell
# Run SQLSolver against tests
python3 runners/run-tests-sqlsolver.py -tests TEST_SET [-time] [-rounds ROUNDS] [-target TARGET] [-skip SKIPPED_PAIR] [-out OUTPUT_FILE] [-tsv TIME_FILE] [-tsv_neq]
```

The script supports almost the same options as `run-sqlsolver.py`
except that `-app` and `-input` are replaced with `-tests`.
The required option `-tests TEST_SET` specifies which test set is input to SQLSolver.
Possible values of `TEST_SET` include `calcite` (the test cases derived from Calcite), `spark` (the test cases derived from Spark SQL), `tpcc` (the test cases derived from TPC-C), and `tpch` (the test cases derived from TPC-H).
The app name and input file of each test set are listed below:

| Test set | App name     | Input file                               |
|----------|--------------|------------------------------------------|
| calcite  | calcite_test | wtune_data/calcite/calcite_tests         |
| spark    | calcite_test | wtune_data/db_rule_instances/spark_tests |
| tpcc     | tpcc         | wtune_data/prepared/rules.tpcc.spark.txt |
| tpch     | tpch         | wtune_data/prepared/rules.tpch.spark.txt |

### Discovery of rules
SQLSolver integrated into WeTune can help find 42 more useful rules than WeTune.
Run the first command and SQLSolver will prove the 35 useful rules discovered by WeTune, which are listed in the paper of WeTune.
The second command uses SQLSolver to prove the 42 rules that are discovered by integrating SQLSolver into WeTune.
```shell
# Invoke SQLSolver to prove 35 useful rules found by WeTune 
python3 runners/find-wetune-rules.py

# Invoke SQLSolver to prove 42 new rules
python3 runners/find-sqlsolver-rules.py
```

### Case Study
To demonstrate the performance improvement introduced by newly discovered rules,
we evaluate the average latency of the query example before and after rewrites.
```shell
# Automatically run the case study
python3 runners/run-useful-rewrite-example.py
```
