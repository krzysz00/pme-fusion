#!/usr/bin/env swipl
/*
 * Copyright ⓒ 2018 Krzysztof Drewniak
 *
 * This file is part of pme-fusion.

 * pme-fusion is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.

 * pme-fusion is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with pme-fusion. If not, see <http://www.gnu.org/licenses/>.
 */

:- initialization(main, main).

:- use_module(pme_fusion).

main(Argv) :-
    (Argv == [] -> current_input(InFile);
     [FileName|_] = Argv, open(FileName, read, InFile)),
    (read_term(InFile, Tasks, []), !; format("The input needs to be a list of lists of tasks, followed by a period.")),
    (gen_invariants(Tasks), !); format("The input needs to be a list of lists of tasks, followed by a period.").
