let ints =
  Dsl.run
    (Dsl.U.compose
       (Dsl.U.pair Dsl.U.id
          (Dsl.U.compose
             (Dsl.U.compose
                (Dsl.U.pair
                   (Dsl.U.compose
                      (Dsl.U.compose
                         (Dsl.U.compose Dsl.U.one
                            (Dsl.U.compose Dsl.oned
                               (Dsl.U.discrete (fun () -> 0))))
                         Dsl.U.sweak)
                      (Dsl.U.scomposer Dsl.cons))
                   (Dsl.U.curry
                      (Dsl.U.compose
                         (Dsl.U.pair (Dsl.U.compose Dsl.U.fst Dsl.U.fst)
                            (Dsl.U.pair (Dsl.U.compose Dsl.U.fst Dsl.U.snd)
                               Dsl.U.snd))
                         (Dsl.U.compose
                            (Dsl.U.compose
                               (Dsl.U.pair
                                  (Dsl.U.pair Dsl.U.fst
                                     (Dsl.U.compose Dsl.U.snd Dsl.U.fst))
                                  (Dsl.U.compose Dsl.U.snd Dsl.U.snd))
                               (Dsl.U.pair
                                  (Dsl.U.compose Dsl.U.fst Dsl.U.fst)
                                  (Dsl.U.compose Dsl.U.snd Dsl.U.id)))
                            (Dsl.U.compose
                               (Dsl.U.pair
                                  (Dsl.U.compose Dsl.U.snd Dsl.U.snd) Dsl.U.
                                  id)
                               (Dsl.U.compose
                                  (Dsl.U.pair
                                     (Dsl.U.pair
                                        (Dsl.U.compose Dsl.U.snd Dsl.U.fst)
                                        Dsl.U.fst)
                                     (Dsl.U.compose Dsl.U.snd Dsl.U.snd))
                                  (Dsl.U.compose
                                     (Dsl.U.pair
                                        (Dsl.U.compose Dsl.U.fst Dsl.prod')
                                        (Dsl.U.compose Dsl.U.snd Dsl.U.id))
                                     (Dsl.U.compose Dsl.U.fst
                                        (Dsl.omega
                                           (Dsl.C.compose Dsl.eta
                                              (Dsl.value
                                                 (Dsl.U.compose
                                                    (Dsl.U.pair Dsl.U.id Dsl.U.one)
                                                    (Dsl.U.compose
                                                       (Dsl.U.pair
                                                          (Dsl.U.curry
                                                             (Dsl.U.compose
                                                                Dsl.U.snd
                                                                (Dsl.U.
                                                                   discrete
                                                                   succ)))
                                                          (Dsl.U.compose Dsl.U.fst
                                                             (Dsl.U.compose
                                                                (Dsl.omega
                                                                   Dsl.C.snd)
                                                                Dsl.varepsilon)))
                                                       Dsl.U.eval)))))))))))))
                Dsl.U.seval)
             (Dsl.U.scomposel (Dsl.U.pair Dsl.U.one Dsl.U.id))))
       (Dsl.U.compose
          (Dsl.U.pair (Dsl.U.compose Dsl.U.fst Dsl.U.fst)
             (Dsl.U.pair (Dsl.U.compose Dsl.U.fst Dsl.U.snd) Dsl.U.snd))
          (Dsl.U.compose (Dsl.U.compose Dsl.U.snd Dsl.U.snd) Dsl.fix)))
