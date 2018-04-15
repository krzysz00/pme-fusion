:- use_module(pme_fusion).

meta_predicate exists_one(1, +).

exists_one(_, []) :- fail.
exists_one(P, [H|T]) :-
    (call(P, H), !);
    exists_one(P, T).

fill_blank_region_pme([], PME, NewPME) :- PME = NewPME.
fill_blank_region_pme([Id|Ids], PME, NewPME) :-
    (exists_one(=(Id-_), PME), !,
     fill_blank_region_pme(Ids, PME, NewPME));
    fill_blank_region_pme(Ids, [Id-[]|PME], NewPME).

fill_blank_regions(Ids, PMEs, NewPMEs) :-
    maplist(fill_blank_region_pme(Ids), PMEs, NewPMEs).

kalman_overwrite :-
    fill_blank_regions(
        [xt, xb, pt, pb, utl, utr, ubr],
        [[xt-[op([in(xt)], [out(xt)])],
          xb-[op([in(xb)], [out(xb)])]],

         [pt-[op([in(pt), out(xt)], [out(pt)])],
          pb-[op([in(pb), out(xb)], [out(pb)])]],

         %% [utl-[op([in(pt)], [out(utl)])],
         %%  utr-[fn([in(pt), out(utl)], [out(utr)])],
         %%  ubr-[fn([in(pb), out(utr)], [during(ubr, 0)]),
         %%       op([during(ubr, 0)], [out(ubr)])]],

         %% [utl-[op([in(utl)], [out(utl)])],
         %%  utr-[fn([any([in(utr), during(utr, 0, b)]), out(utl)], [during(utr, 0, a)]),
         %%       fn([any([in(utr), during(utr, 0, a)]), in(ubr)], [during(utr, 0, b)])],
         %%  ubr-[op([in(ubr)], [out(ubr)])]],

         %% [utl-[op([in(utl)], [during(utl, 0)]),
         %%       fn([in(utr), during(utl, 0)], [out(utl)])],
         %%  utr-[fn([in(ubr), in(utr)], [out(utr)])],
         %%  ubr-[op([in(ubr)], [out(ubr)])]],

         [xt-[op([in(xt), out(pt)], [out(xt)])],
          xb-[op([in(xb), out(pb)], [out(xb)])]],

         [pt-[op([in(pt)], [out(pt)])],
          pb-[op([in(pb)], [out(pb)])]]
        ], PMEs),
    test_pmes(PMEs).

kalman_long :-
    fill_blank_regions(
        [xt, xb, ytl, ytr, ybl, ybr, v0t, v0b,
         m1tl, m1tr, m1bl, m1br,
         m3tl, m3tr, m3br, utl, utr, ubr,
         v1t, v1b],
        [[xt-[op([in(xt)], [out(xt)])],
          xb-[op([in(xb)], [out(xb)])]],

         [ptl-[op([in(ptl), in(ptr), in(pbl)], [out(ytl)])],
          ptr-[op([in(ptr), in(ptl), in(pbr)], [out(ytr)])],
          pbl-[op([in(pbl), in(pbr), in(ptl)], [out(ybl)])],
          pbr-[op([in(pbr), in(pbl), in(ptr)], [out(ybr)])]],

         [xt-[op([in(xt)], [out(v0t)])],
          xb-[op([in(xb)], [out(v0b)])]],

         [ytl-[op([in(ytl), in(ybl)], [out(m1tl)])],
          ytr-[op([in(ytr), in(ybr)], [out(m1tr)])],
          ybl-[op([in(ytl), in(ytr)], [out(m1bl)])],
          ybr-[op([in(ytr), in(ybr)], [out(m1br)])]],

         [m1tl-[op([in(m1tl), in(m1bl)], [out(m3tl)])],
          m1tr-[op([in(m1tr), in(m1br)], [out(m3tr)])],
          m1br-[op([in(m1tr), in(m1br)], [out(m3br)])]],

         [m3tl-[noop([in(m3tl)], [out(m3tl)])],
          m3tr-[noop([in(m3tr)], [out(m3tr)])],
          m3br-[noop([in(m3br)], [out(m3br)])],
          utl-[op([out(m3tl)], [out(utl)])],
          utr-[fn([out(m3tr), out(utl)], [out(utr)])],
          ubr-[fn([out(m3br), out(utr)], [during(ubr, 0)]),
               op([during(ubr, 0)], [out(ubr)])]],

         [utl-[noop([in(utl)], [out(utl)])],
          utr-[noop([in(utr)], [out(utr)])],
          ubr-[noop([in(ubr)], [out(ubr)])],
          v0t-[op([out(utl), in(v0t)], [out(v1t)])],
          v0b-[fn([out(utl), out(utr), out(v1t)], [during(v1b, 0)]),
               op([out(ubr), during(v1b, 0)], [out(v1b)])]]
        ],
        PMEs),
    test_pmes(PMEs).
