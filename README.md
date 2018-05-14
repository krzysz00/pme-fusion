# pme-fusion: Automatic generation of fusable loop invariants for algorithms expressed in FLAME notation

This library/program allow you to generate fusable loop invariants for
a series of operations expressible in FLAME notation if you specify
the partitioned matrix expressions (PMEs) (which can be used for
objects other than matrices).

## Installation
You do not need to take any action to install this program. If you do
choose to install it, move [gen_invariants.pl] and [pme_fusion.pl]
into the same directory.

## Usage
The syntax of the input format is located in [docs/pme_fusion.html].

The main library is in [pme_fusion.pl].

One (recommended) way to use the library is the [gen_invariants.pl]
script, which takes a list of PMEs, each expressed as a list of tasks
(see the [library documentation](doc/pme_fusion.pl) for details). The
tasks are read from the filename given to the script as an argument or
from standard input (if no arguments are passed). In either case, the
input must be terminated by a period (`.`) to satisfy the Prolog parser.

Another method is load the library into a Prolog program using
`use_module` and to then call the functions exported from it, such as
`gen_invariants/1`.

`gen_docs.pl` will recreate the documentation.

## Dependencies
This software is written to target
[SWI Prolog](http://www.swi-prolog.org/) version 7.6.4. It will likely
not function in other Prolog implementations or significantly older
versions of SWI Prolog.

## Examples
Examples of both methods can be found in the [`examples/`](examples/)
directory. The example input to the `gen_invariants.pl` script is
stored in a `.txt` file.

`examples/examples.pl` functions as a series of basic test cases.

`examples/common_task_lists.pl` contains functions that generate task
lists for several common operations.

## License
Copyright ⓒ 2018 Krzysztof Drewniak

This file is part of pme-fusion.

pme-fusion is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

pme-fusion is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with pme-fusion. If not, see <http://www.gnu.org/licenses/>.

