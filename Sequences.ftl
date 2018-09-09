[read Sequences/Naturals.ftl]
[read Sequences/helper.ftl]

[sequence/-s]
[converge/-s]

Let n, m, k, N, N1, N2, N3 denote natural numbers.

Definition.
NAT is the set of natural numbers.

### Sequences

Definition Seq.
    A sequence f is a function such that every element of Dom(f) is a natural number and every
    natural number is an element of Dom(f) and for every n f[n] is a real number.

Axiom SequenceEq.
    Let a, b be sequences. a = b iff (for every n a[n] = b[n]).



### Convergence

Definition Convergence.
    Let a be a sequence. Let x be a real number. a converges to x iff for every positive real
    number eps there exists N such that for every n such that N < n dist(a[n],x) < eps.

Definition Conv.
    Let a be a sequence. a converges iff there exists a real number x such that a converges to x.

Let a is convergent stand for a converges.
Let a diverges stand for not (a converges).
Let a is divergent stand for a diverges.



### Range

Definition Range.
    Let a be a sequence. ran(a) = {a[n] | n is a natural number}. 

Definition RangeN.
    Let a be a sequence. ranN(a,N) = {a[n] | n is a natural number such that n =< N}.

Definition FiniteRange.
    Let a be a sequence. a has finite range iff there exists an N such that ran(a) = ranN(a,N).

Definition InfiniteRange.
    Let a be a sequence. a has infinite range iff not (a has finite range).



### Sequence 1/n converges to 0 and has infinite range

Lemma. 
    Let a be a sequence such that for every n
        ((If n = 0 then a[n] = 2) and (If n != 0 then a[n] = inv(n))).
    Then a converges to 0 and a has infinite range.
Proof.
    Let us show that a converges to 0.
        Let eps be a positive real number. 
        Take N such that 1 < N * eps (by ArchimedeanAxiom, OnePos).

        Let us show that for every n such that N < n dist(a[n],0) < eps.
            Assume N < n. Then n != 0.
            Let us show that inv(n) < eps.
                We have N * eps < n * eps (by ComMult, MultInvariance).
                Hence 1 < n * eps (by TransitivityOfOrder).

                inv(n) is positive.
                Hence inv(n) * 1 < inv(n) * (n * eps) (by MultInvariance).
                We have inv(n) * 1 = inv(n) (by One).
                inv(n) * (n * eps) .= (inv(n) * n) * eps (by AssMult)
                                   .= 1 * eps (by InvDummy)
                                   .= eps (by OneDummy).
            end.
            Hence dist(a[n],0) = inv(n) < eps.
        end.
    end.

    Let us show that a has infinite range.
        Assume the contrary.
        Take N such that ran(a) = ranN(a,N) (by FiniteRange).
        Then a[N + 1] is an element of ran(a) (by OneNat, AddClosedNat, Range).

        Let us show that a[N + 1] is not an element of ranN(a,N).
            Let us show that for every n such that n =< N a[n] != a[N + 1].
                Assume the contrary.
                Take n such that n =< N and a[n] = a[N + 1].
                Case n = 0.
                    We have 2 = inv(N + 1).

                    (2 * N) + 2 .= (2 * N) + (2 * 1) (by One)
                                .= 2 * (N + 1) (by Distrib)
                                .= inv(N + 1) * (N + 1)
                                .= 1 (by InvDummy).

                    We have (2 * N) + 2 > 1.
                    Contradiction.
                end.
                Case n != 0.
                    We have inv(n) = inv(N + 1).
                    Then inv(inv(n)) = inv(inv(N + 1)).

                    We have N + 1 != 0.
                    Hence n = N + 1 (by InvRule1).
                    Contradiction.
                end.
            end.
            Hence a[N + 1] is not an element of ranN(a,N) (by RangeN).
        end.

        Contradiction.
    end.
qed.



### Sequence (-1)^n diverges and has finite range.

Signature Parity.
    n is even is an atom.

Let n is odd stand for not (n is even).

Axiom ParityPlusOne.
    n is even iff n + 1 is odd.

Axiom ZeroEven.
    0 is even.

Lemma OneOdd.
    1 is odd.

Lemma.
    Let a be a sequence such that for every n (((n is even) => a[n] = 1) and ((n is odd) => a[n] = -1)).
    Then a diverges and a has finite range.
Proof.
    Let us show that a diverges.
        Assume the contrary.
        Take a real number x such that a converges to x.
        Take N such that for every n such that N < n dist(a[n],x) < 1 (by Convergence, OnePos).

        Let us show that dist(a[N + 1],a[N + 2]) = 2.
            Case N + 1 is even.
                Then (N + 2) is odd.
                Hence dist(a[N + 1],a[N + 2]) = dist(1,-1) = 2.
            end.
            Case N + 1 is odd.
                Then N + 2 is even.
                Hence dist(a[N + 1],a[N + 2]) = dist(-1,1) = 2.
            end.
        end.

        a[N + 1] is a real number and a[N + 2] is a real number.
        We have dist(a[N + 1],a[N + 2]) =< dist(a[N + 1],x) + dist(x,a[N + 2]) (by DistTriangleIneq).
        We have dist(x,a[N + 2]) = dist(a[N + 2],x) (by DistSymm).
        Hence dist(a[N + 1],a[N + 2]) =< dist(a[N + 1],x) + dist(a[N + 2],x).

        We have dist(a[N + 1],x) < 1 and dist(a[N + 2],x) < 1.
        Hence dist(a[N + 1],x) + dist(a[N + 2],x) < 1 + 1 (by AddInvariance).
        Hence dist(a[N + 1],a[N + 2]) < 2 (by MixedTransitivity).
        Hence 2 < 2.
        Contradiction.
    end.

    Let us show that a has finite range.
        Let us show that ran(a) = ranN(a,1).
            Let us show that every element of ranN(a,1) is an element of ran(a).
                Assume x is an element of ranN(a,1).
                Take n such that n =< 1 and a[n] = x (by OneNat, RangeN).
                Hence x is an element of ran(a) (by Range).
            end.

            Let us show that every element of ran(a) is an element of ranN(a,1).
                Assume x is an element of ran(a).

                Let us show that x = 1 or x = -1.
                    Take n such that a[n] = x (by Range).
                    n is even or n is odd.
                    Hence x = 1 or x = -1.
                end.

                We have a[0] = 1.
                We have a[1] = -1.

               Case x = 1.
                    Then x = a[0].
                    We have 0 =< 1.
                    Hence x is an element of ranN(a,1) (by ZeroNat, OneNat, RangeN).
                end.
                Case x = -1.
                    Then x = a[1].
                    We have 1 =< 1.
                    Hence x is an element of ranN(a,1) (by OneNat, RangeN).
                end.
            end.
        end.
    end.
qed.



### Neighborhood

Definition Neighb.
    Let eps be a positive real number. Let x be a real number.
    Neighb(x,eps) = {y | y is a real number such that dist(y,x) < eps}.

Theorem ConvNeighborhood.
    Let a be a sequence. Let x be a real number.
    a converges to x iff for every positive real number eps there exists a N
    such that for every n such that N < n a[n] is an element of Neighb(x,eps).
Proof.
    Let us show that (If a converges to x then for every positive real number eps there exists a N
    such that for every n such that N < n a[n] is an element of Neighb(x,eps)).
        Assume a converges to x.
        Let eps be a positive real number.
        Take N such that for every n such that N < n dist(a[n],x) < eps (by Convergence).
        Hence for every n such that N < n a[n] is an element of Neighb(x,eps) (by Neighb).
    end.
    
    Let us show that (If for every positive real number eps there exists a N such that
    for every n such that N < n a[n] is an element of Neighb(x,eps) then a converges to x).
        Assume for every positive real number eps there exists a N such that
            for every n such that N < n a[n] is an element of Neighb(x,eps).
        Let eps be a positive real number.
        Take N such that for every n such that N < n a[n] is an element of Neighb(x,eps).
        Hence for every n such that N < n dist(a[n],x) < eps (by Neighb).
    end.
qed.



### Limit is unique

Lemma DistEqual.
    Let x and y be real numbers. Assume for every positive real number eps dist(x,y) < eps.
    Then x = y.
Proof.
	Assume the contrary.
    Then there exists a positive real number eps such that eps < dist(x,y).
    A contradiction.
qed.

Theorem LimitUnique.
    Let a be a sequence. Let x, y be real numbers. Assume a converges to x and a converges to y.
    Then x = y.
Proof.
    Let us show that for every positive real number eps dist(x,y) < eps.
        Let eps be a positive real number.
        Take a positive real number halfeps such that halfeps = inv(2) * eps.

        Take N1 such that for every n such that N1 < n dist(a[n],x) < halfeps (by Convergence).
        Take N2 such that for every n such that N2 < n dist(a[n],y) < halfeps (by Convergence).

        For every n dist(x,y) =< dist(x,a[n]) + dist(a[n],y) (by DistTriangleIneq). 
        Take N3 such that N3 = max(N1,N2) + 1.
        Then N1 < N3 and N2 < N3.

        Hence dist(x,a[N3]) < halfeps and dist(a[N3],y) < halfeps (by DistSymm).
        Hence dist(x,a[N3]) + dist(a[N3],y) < halfeps + halfeps (by AddInvariance).
        Hence dist(x,y) < halfeps + halfeps (by MixedTransitivity).
        Hence dist(x,y) < eps (by TwoHalf).
    end.
    Therefore x = y (by DistEqual).
qed.



### A convergent sequence is bounded

Definition BoundedBy.
    Let a be a sequence. Let K be a real number. a is bounded by K iff
    for every n abs(a[n]) =< K.

Definition BoundedSequence.
    Let a be a sequence. a is bounded iff there exists a real number K such that
    a is bounded by K.

Signature MaxN.
    Let a be a sequence. maxN(a,N) is a real number such that
    (there exists n such that n =< N and maxN(a,N) = a[n]) and
    (for every n such that n =< N a[n] =< maxN(a,N)).

Theorem ConvergentImpBounded.
    Let a be a sequence. Assume that a converges. Then a is bounded.
Proof.
    Take a real number x such that a converges to x.
    Take N such that for every n such that N < n dist(a[n],x) < 1 (by Convergence, OnePos).

    Define b[k] = abs(a[k]) for k in NAT.
    Take a real number K such that K = max(1 + abs(x), maxN(b,N)).

    Let us show that a is bounded by K.
        Let us show that for every n abs(a[n]) =< K. 
            Let n be a natural number.
            We have n =< N or n > N.
            Case n =< N.
                We have abs(a[n]) = b[n] =< maxN(b,N) (by MaxN).
                We have maxN(b,N) =< K (by MaxIneqDummy).
                Therefore abs(a[n]) =< K (by LeqTransitivity).
            end.
            Case n > N.
                We have dist(a[n],x) < 1.
                We have 1 + abs(x) =< K (by MaxIneq).

                abs(a[n]) .= abs(a[n] + 0) (by Zero)
                          .= abs(a[n] + (x - x)) (by Neg)
                          .= abs(a[n] + ((-x) + x)) (by ComAdd)
                          .= abs((a[n] - x) + x) (by AssAdd).

                Hence abs(a[n]) =< abs(a[n] - x) + abs(x) (by AbsTriangleIneq).
                Hence abs(a[n]) =< dist(a[n],x) + abs(x).

                We have dist(a[n],x) + abs(x) < 1 + abs(x) (by MixedAddInvariance).
                Hence abs(a[n]) =< 1 + abs(x) (by MixedTransitivity).
                Therefore abs(a[n]) =< K (by LeqTransitivity).
            end.
        end.
        Hence a is bounded by K (by BoundedBy).
    end.
qed.

Definition LimitPointOfSet.
    Let E be a set. Assume every element of E is a real number. A limit point of E
    is a real number x such that for every positive real number eps there exists an element
    y of E such that y is an element of Neighb(x,eps) and y != x.

Theorem ConvLimitPoint.
    Let E be a set. Assume every element of E is a real number. Let x be a limit point of E.
    Then there exists a sequence a such that a converges to x and for every n a[n] is an element of E.
Proof.
    Let us show that for every n such that n > 0 there exists an element y of E such that
    y is an element of Neighb(x,inv(n)) and y != x.
        Assume n > 0.
        Then inv(n) is a positive real number.
        Take an element y of E such that y is an element of Neighb(x,inv(n))
            and y != x (by LimitPointOfSet).
    end.

    Define a[n] = Case n = 0 -> Choose an element y of E such that y is an element of
                                Neighb(x,1) and y != x in y,
                  Case n > 0 -> Choose an element y of E such that y is an element of
                                Neighb(x,inv(n)) and y != x in y
    for n in NAT.
    a is a sequence.

    Then for every n a[n] is an element of E.
    Let us show that a converges to x.
        Let eps be a positive real number.
        Take N such that 1 < N * eps (by ArchimedeanAxiom, OnePos).

        Let us show that for every n such that N < n dist(a[n],x) < eps.
            Assume N < n. Then n != 0.
            Then a[n] is an element of E such that a[n] is an element of Neighb(x,inv(n)).
            Hence dist(a[n],x) < inv(n).

            Let us show that inv(n) < eps.
                We have N * eps < n * eps (by ComMult, MultInvariance).
                Hence 1 < n * eps (by TransitivityOfOrder).

                inv(n) is positive.
                Hence inv(n) * 1 < inv(n) * (n * eps) (by MultInvariance).
                We have inv(n) * 1 = inv(n) (by One).
                inv(n) * (n * eps) .= (inv(n) * n) * eps (by AssMult)
                                   .= 1 * eps (by InvDummy)
                                   .= eps (by OneDummy).
            end.
            Hence dist(a[n],x) < eps (by TransitivityOfOrder).
        end.
    end.
qed.



### Sum and Product of Sequences

Definition SequenceSum.
    Let a,b be sequences. a +' b is a sequence such that for every n (a +' b)[n] = a[n] + b[n].

Definition SequenceProd.
    Let a,b be sequences. a *' b is a sequence such that for every n (a *' b)[n] = a[n] * b[n].

Definition SequenceConstSum.
    Let a be a sequence. Let c be a real number. c +'' a is a sequence such that for every n (c +'' a)[n] = c + a[n].

Definition SequenceConstProd.
    Let a be a sequence. Let c be a real number. c *'' a is a sequence such that for every n (c *'' a)[n] = c * a[n].

Definition SequenceDiv.
    Let a be a sequence. Assume for every n a[n] != 0. div(a) is a sequence such that for every n (div(a))[n] = inv(a[n]).


Theorem SumConv.
    Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
    Then a +' b converges to x + y.
Proof.
    Let eps be a positive real number.
    Take a positive real number halfeps such that halfeps = inv(2) * eps.

    Take N1 such that for every n such that N1 < n dist(a[n],x) < halfeps (by Convergence).
    Take N2 such that for every n such that N2 < n dist(b[n],y) < halfeps (by Convergence).
    Take N such that N = max(N1,N2).
    Then N1 =< N and N2 =< N.

    Let us show that for every n such that N < n dist((a +' b)[n],(x+y)) < eps.
        Assume N < n.
        We have dist(a[n],x) < halfeps.
        We have dist(b[n],y) < halfeps.

        abs((a[n] + b[n]) - (x + y)) .= abs((a[n] + b[n]) + ((-x) + (-y))) (by MinusRule1)
                                     .= abs((-x) + ((a[n] + b[n]) - y)) (by BubbleAdd)
                                     .= abs((-x) + (a[n] + (b[n] - y))) (by AssAdd)
                                     .= abs(((-x) + a[n]) + (b[n] - y)) (by AssAdd)
                                     .= abs((a[n] - x) + (b[n] - y)) (by ComAdd).

        We have abs((a[n] - x) + (b[n] - y)) =< abs(a[n] - x) + abs(b[n] - y)  (by AbsTriangleIneq).
        Hence abs((a[n] + b[n]) - (x + y)) =< dist(a[n],x) + dist(b[n],y).

        Hence dist(a[n],x) + dist(b[n],y) < halfeps + halfeps (by AddInvariance).
        Hence abs((a[n] + b[n]) - (x + y)) < halfeps + halfeps (by MixedTransitivity).
        Hence dist((a +' b)[n],(x + y)) < halfeps + halfeps.
        Hence dist((a +' b)[n],(x + y)) < eps (by TwoHalf).
    end.
qed.

Lemma ConstConv.
    Let c be a real number. Let cn be a sequence such that for every n cn[n] = c.
    Then cn converges to c.
Proof.
    Let eps be a positive real number.
    Let us show that for every n such that 0 < n dist(cn[n],c) < eps.
        Assume 0 < n.
        dist(cn[n],c) = dist(c,c) = 0 (by IdOfInd).
        Hence dist(cn[n],c) < eps.
    end.
qed.

Theorem SumConstConv.
    Let a be a sequence. Let x,c be real numbers. Assume a converges to x.
    Then c +'' a converges to c + x.
Proof.
    Define cn[n] = c for n in NAT.
    cn is a sequence.
    Let us show that c +'' a = (cn +' a).
        Let us show that for every n (c +'' a)[n] = (cn +' a)[n].
            Let n be a natural number.
            (c +'' a)[n] .= c + a[n]
                         .= cn[n] + a[n]
                         .= (cn +' a)[n].
        end.
        Hence c +'' a = (cn +' a) (by SequenceEq).
    end.

    cn converges to c (by ConstConv).
    Then c +'' a converges to c + x (by SumConv).
qed.


Theorem ProdConstConv.
    Let a be a sequence. Let x,c be real numbers. Assume a converges to x.
    Then c *'' a converges to c * x.
Proof.
    Case c = 0.
        We have c * x = 0.
        Let us show that for every n (c *'' a)[n] = 0. 
            (c *'' a)[n] .= c * a[n]
                  .= 0 * a[n]
                  .= 0 (by ZeroMult).
        end.
        Hence c *'' a converges to c * x (by ConstConv).
    end.
    Case c != 0.
        Let eps be a positive real number. 
(1)     Take a positive real number invEps such that invEps = inv(abs(c)) * eps.
        Take N such that for every n such that N < n dist(a[n],x) < invEps (By Convergence).

        Let us show that for every n such that N < n dist(c * a[n],c * x) < eps.
            Assume N < n.
            abs((c * a[n]) - (c * x)) .= abs((c * a[n])+  ((-1) * (c * x))) (by MinusRule4) 
                                      .= abs((c * a[n]) + (((-1) * c) * x)) (by AssMult)
                                      .= abs((c * a[n]) + ((c * (-1)) * x)) (by ComMult)
                                      .= abs((c * a[n]) + (c * ((-1) * x))) (by AssMult)
                                      .= abs((c * a[n]) + (c * (-x))) (by MinusRule4)
                                      .= abs(c * (a[n] - x)) (by Distrib)
                                      .= abs(c) * abs(a[n] - x) (by AbsMult).
            abs(c) * dist(a[n],x) < abs(c) * invEps (by AbsPos, MultInvariance).
            Hence abs((c * a[n]) - (c * x)) < abs(c) * invEps.

            abs(c) * invEps .= abs(c) * (inv(abs(c)) * eps) (by 1)
                            .= (abs(c) * inv(abs(c))) * eps (by AssMult)
                            .= 1 * eps (by Inverse)
                            .= eps (by OneDummy).

            Hence dist(c * a[n],c * x) < eps.
        end.
    end.
qed.


Lemma ConstMultSum.
    Let a,b be sequences. Let x,y be real numbers such that for every n b[n] = y * (a[n] + (-x)). Assume a converges to x.
    Then b converges to 0.
Proof.
    Define sum[k] = (-x) + a[k] for k in NAT.
    sum is a sequence.
    Let us show that sum converges to 0.
    Proof.
        We have sum = (-x) +'' a.
        Hence sum converges to (-x) + x (by SumConstConv).
        (-x) + x = 0 (by ComAdd, Neg).
    qed.
    Let us show that for every n b[n] = y * sum[n].
    Proof.
        b[n] .= y * (a[n] + (-x))
             .= y * ((-x) + a[n]) (by ComAdd)
             .= y * sum[n].
    qed.
    Hence b = y *'' sum (by SequenceEq).
    Hence b converges to 0 (by ProdConstConv, ComMult, ZeroMult).
qed.


Theorem ProdConv.
    Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
    Let a *' b be a sequence such that for every natural number n (a *' b)[n] = a[n] * b[n].
    Then a *' b converges to x * y.
Proof.
#Strategie: zerteile (s[n]*t[n]) - (x*y) = ((s[n] - x)*(t[n] - y)) + ((x*(t[n] - y)) + (y*(s[n] - x))) in Teilfolgen und zeige erst die Konvergenz der Teile um daraus die Konvergenz des Ganzen zu folgern.
    (1) Define s1[k] = (a[k] - x) * (b[k] - y) for k in NAT.
    Let us show that s1 converges to 0.
    proof.
        Assume eps is a positive real number. 
        Take a positive real number rooteps such that rooteps = sqrt(eps) (by Sqrt).
        Take N1 such that for every n such that N1 < n dist(a[n],x) < rooteps (by Convergence).
        Take N2 such that for every n such that N2 < n dist(b[n],y) < rooteps (by Convergence).
        Take N such that N = max(N1,N2).
        Let us show that for every n such that N < n dist(s1[n],0) < eps.
        Proof.
            Assume N < n.
            dist(a[n],x) < rooteps and dist(b[n],y) < rooteps.
            dist(a[n],x), dist(b[n],y) and rooteps are nonnegative.
            Then dist(a[n],x) * dist(b[n],y) < eps (by NonNegMultInvariance).
            Hence abs(a[n] - x) * abs(b[n] - y) < eps.
            Hence abs((a[n] - x) * (b[n] - y)) < eps (by AbsMult).
            Hence abs(((a[n] - x) * (b[n] - y)) - 0) < eps (by Zero, NegOfZero).
        qed.
    qed.
    (2) Define s2[k] = (x * (b[k] + (-y))) + (y * (a[k] + (-x))) for k in NAT.
    Let us show that s2 converges to 0.
    Proof.
        (3) Define s2a[k] = y * (a[k] + (-x)) for k in NAT.
        (4) Define s2b[k] = x * (b[k] + (-y)) for k in NAT.
        s2a, s2b are sequences.
        Define sum1[k] = a[k] + (-x) for k in NAT.
        Define sum2[k] = b[k] + (-y) for k in NAT.
        sum1, sum2 are sequences.
        sum1 = (-x) +'' a and sum2 = (-y) +'' b (by ComAdd, SequenceEq).
        sum1, sum2 converge to 0 (by SumConstConv, Neg, ComAdd).
        We have s2a = y *'' sum1 and s2b = x *'' sum2 (by SequenceEq).
        s2a, s2b converge to 0 (by ConstMultSum). 
        Let us show that for every n s2[n] = s2b[n] + s2a[n].
        Proof.
            s2[n] .= (x * (b[n] + (-y))) + (y * (a[n] + (-x))) (by 2)
                  .= s2b[n] + s2a[n] (by 3, 4).
        qed.
        Hence s2 converges to 0 (by SumConv).
    qed.
    (5) Define s3[k] = (a[k] * b[k]) - (x * y) for k in NAT.
    Let us show that s3 converges to 0.
    proof.
        Let us show that for every n s3[n] = s1[n] + s2[n].
        Proof.
            s3[n] .= (a[n] * b[n]) - (x * y) (by 5)
                  .= ((a[n] - x) * (b[n] - y)) + ((x * (b[n] - y)) + (y * (a[n] - x))) (by Identity1)
                  .= s1[n] + s2[n] (by 1, 2).
        qed.
        Hence s3 = s1 +' s2 (by SequenceEq).
        Therefore the thesis (by SumConv, Zero).
    qed. 
    Let eps be a positive real number.
    Take N such that for every n such that N < n dist(s3[n],0) < eps (by Convergence).
    Let us show that for every n such that N < n dist(a[n] * b[n],x * y) < eps.
    Proof.
        Assume N < n.
        dist(s3[n],0) .= dist((a[n] * b[n]) - (x * y),0) (by 5)
                      .= abs(((a[n] * b[n]) - (x * y)) - 0) (by DistDefinition)
                      .= abs((a[n] * b[n]) - (x * y)) (by NegOfZero, Zero)
                      .= dist(a[n] * b[n],x * y) (by DistDefinition).
    qed.
qed.

    

Theorem DivConv.
    Let a be a sequence. Let x be a real number such that x != 0. Assume a converges to x. 
    Assume for every n a[n] != 0.
    Let div(a) be a sequence such that for every natural number n (div(a))[n] = inv(a[n]).
    Then div(a) converges to inv(x).
Proof.
    Let eps be a positive real number.

    abs(x) != 0.
    2, inv(2), abs(x), abs(x) * abs(x), -abs(x), ((-1) * inv(2)) * abs(x), (inv(2) * abs(x)) + (-abs(x)) are real numbers.
    We have pos(2) and pos(inv(2)) and pos(abs(x)) and pos(abs(inv(x))) and pos(inv(2) * eps) and pos(abs(x) * abs(x)) and pos((inv(2) * eps) * (abs(x) * abs(x))) and
            pos(inv(2) * abs(x)) and pos(eps * (abs(x) * abs(x))) and pos(inv(2) * abs(inv(x))) and pos((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))).
                                                                                
   
    Take a natural number m such that for every n such that m < n dist(a[n],x) < inv(2) * abs(x) (by Convergence).
    Let us show that for every n such that m < n inv(2) * abs(x) < abs(a[n]).
    Proof. 
        Assume m < n.
        a[n], abs(a[n]), -abs(a[n]), abs(x) - abs(a[n]), x - a[n], abs(x - a[n]), a[n] - x, abs(a[n] - x), abs(x) + (-abs(a[n])), (abs(x) + (-abs(a[n]))) + (-abs(x)) are real numbers.
        Let us show that abs(x) - abs(a[n]) < inv(2) * abs(x).
        Proof.
            abs(x) - abs(a[n]) =< abs(x - a[n]) (by AbsTriangleIneq2).
            abs(x - a[n]) = abs(-(x - a[n])) = abs(a[n] - x) (by AbsPosNeg, MinusRule1, MinusRule2, ComAdd).
            abs(a[n] - x) < inv(2) * abs(x) (by DistDefinition).
            Hence the thesis (by MixedTransitivity).
        qed.

        Let us show that -abs(a[n]) < (-inv(2)) * abs(x).
            (abs(x) - abs(a[n])) + (-abs(x)) < (inv(2) * abs(x)) + (-abs(x)) (by MixedAddInvariance). 
            (abs(x) - abs(a[n])) + (-abs(x)) = -abs(a[n]) (by AssAdd, Neg, ComAdd, Zero).

            -abs(a[n]) < (inv(2) * abs(x)) + (-abs(x)) (by AssAdd, Neg, Zero).
            (inv(2) * abs(x)) + (-abs(x)) .= (inv(2) * abs(x)) + ((-1) * abs(x)) (by MinusRule4)
                                          .= (inv(2) + (-1)) * abs(x) (by DistribDummy)
                                          .= ((1 * inv(2)) + (-(1 * inv(1)))) * abs(x) (by OneDummy, Inverse)
                                          .= ((1 * inv(2)) + ((-1) * inv(1))) * abs(x) (by OneDummy, MinusRule4)
                                          .= ((1 * inv(2)) + ((-1) * inv(1))) * abs(x) (by MinusRule4)
                                          .= (((1 * 1) + (2 * (-1))) * inv(2 * 1)) * abs(x) (by InvAdd)
                                          .= ((1 + ((-1) * 2)) * inv(2)) * abs(x) (by One, ComMult).
            1 + ((-1) * 2) .= 1 + -(1 * 2) (by MinusRule5)
                           .= -(2 - 1) (by OneDummy, MinusRule3)
                           .= -1.
        qed.

        Therefore abs(a[n]) > -((-inv(2)) * abs(x)) (by OrdMirror, MinusRule2).
        -((-inv(2)) * abs(x)) = abs(x) * inv(2) (by MinusRule5, MinusRule2, ComMult).
        Therefore abs(a[n]) > abs(x) * inv(2) (by TransitivityOfOrder).
    qed.
   
    Take N1 such that for every n such that N1 < n dist(a[n],x) < (inv(2) * eps) * (abs(x) * abs(x)) (by Convergence). 
    Take N2 such that N2 = max(N1,m).
    Let us show that for every n such that N2 < n dist(inv(a[n]),inv(x)) < eps.
    Proof.
        Assume N2 < n.
        Then we have N1 < n and m < n.
        Let us show that dist(inv(a[n]),inv(x)) < ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (1 * inv(abs(a[n]))).
        Proof.
            dist(inv(a[n]),inv(x)) .= abs(inv(a[n]) - inv(x)) (by DistDefinition)
                                   .= abs((1 * inv(a[n])) - (1 * inv(x))) (by OneDummy)
                                   .= abs((1 * inv(a[n])) + ((-1) * inv(x))) (by MinusRule5)
                                   .= abs(((1 * x) + (a[n] * (-1))) * inv(a[n] * x)) (by InvAdd)
                                   .= abs((x + ((-1) * a[n])) * inv(a[n] * x)) (by OneDummy, ComMult)
                                   .= abs((x - a[n]) * inv(a[n] * x)) (by MinusRule4)
                                   .= abs(x - a[n]) * abs(inv(a[n]) * inv(x)) (by AbsMult, InvRule2)
                                   .= abs(inv(a[n]) * inv(x)) * abs(x - a[n]) (by ComMult).
            We have pos(abs(inv(a[n]) * inv(x))) (by AbsPos, InvNotZero, NoZeroDivisors).
            abs(x - a[n]) = dist(a[n],x) (by DistDefinition, DistSymm).
            abs(inv(a[n]) * inv(x)) * abs(x - a[n]) < abs(inv(a[n]) * inv(x)) * ((inv(2) * eps) * (abs(x) * abs(x))) (by MultInvariance, DistDefinition).
            abs(inv(a[n]) * inv(x)) * ((inv(2) * eps) * (abs(x) * abs(x))) .= (abs(inv(a[n])) * abs(inv(x))) * ((inv(2) * eps) * (abs(x) * abs(x))) (by AbsMult)
                                                                    .= ((inv(2) * eps) * (abs(x) * abs(x))) * (abs(inv(a[n])) * abs(inv(x))) (by ComMult)
                                                                    .= (inv(2) * (eps * (abs(x) * abs(x)))) * (abs(inv(a[n])) * abs(inv(x))) (by AssMult)
                                                                    .= ((eps * (abs(x) * abs(x))) * inv(2)) * (abs(inv(a[n])) * abs(inv(x))) (by ComMult)
                                                                    .= (eps * (abs(x) * abs(x))) * (inv(2) * (abs(inv(a[n])) * abs(inv(x)))) (by AssMult)
                                                                    .= (eps * (abs(x) * abs(x))) * (inv(2) * (abs(inv(x)) * abs(inv(a[n])))) (by ComMult)
                                                                    .= (eps * (abs(x) * abs(x))) * ((inv(2) * abs(inv(x))) * abs(inv(a[n]))) (by AssMult)
                                                                    .= ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * abs(inv(a[n])) (by AssMult)
                                                                    .= ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * inv(abs(a[n])) (by AbsInv)
                                                                    .= ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (1 * inv(abs(a[n]))) (by OneDummy).
        qed.

        (eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x))), 1 * inv(abs(a[n])), 2 * inv(abs(x)), dist(inv(a[n]),inv(x)),
        ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (1 * inv(abs(a[n]))), ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (2 * inv(abs(x))) are real numbers.

        Let us show that ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (1 * inv(abs(a[n]))) < eps.
        Proof. 
            Let us show that 1 * inv(abs(a[n])) < 2 * inv(abs(x)).
            Proof.
                We have abs(a[n]) > abs(x) * inv(2).
                Hence abs(a[n]) * inv(1) > abs(x) * inv(2) (by InvOne, One).
                We have (pos(abs(a[n])) and pos(1)) and (pos(abs(x)) and pos(2)).
                (abs(a[n]) != 0 and 1 != 0) and (abs(x) != 0 and 2 != 0).
                Then 1 * inv(abs(a[n])) < 2 * inv(abs(x)) (by InvSwapIneq).
            qed.

            ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (1 * inv(abs(a[n]))) < ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (2 * inv(abs(x))) (by MultInvariance).
            ((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))) * (2 * inv(abs(x))) .= ((eps * (abs(x) * abs(x))) * (inv(abs(x)) * inv(2))) * (2 * inv(abs(x))) (by ComMult, AbsInv)
                                                                                     .= (((eps * (abs(x) * abs(x))) * inv(abs(x))) * inv(2)) * (2 * inv(abs(x))) (by AssMult)
                                                                                     .= ((eps * (abs(x) * abs(x))) * inv(abs(x))) * (inv(2) * (2 * inv(abs(x)))) (by AssMult)
                                                                                     .= (eps * ((abs(x) * abs(x)) * inv(abs(x)))) * ((inv(2) * 2) * inv(abs(x))) (by AssMult)
                                                                                     .= (eps * ((abs(x) * abs(x)) * inv(abs(x)))) * inv(abs(x)) (by InvDummy, OneDummy)
                                                                                     .= (eps * (abs(x) * (abs(x) * inv(abs(x))))) * inv(abs(x)) (by AssMult)
                                                                                     .= (eps * abs(x)) * inv(abs(x)) (by Inverse, One)
                                                                                     .= eps * (abs(x) * inv(abs(x))) (by AssMult)
                                                                                     .= eps (by Inverse, One).
        qed.
        Hence the thesis (by TransitivityOfOrder).
    qed.
qed.
   


### Subsequences

Definition IndexSeq.
    An index sequence is a sequence i such that (for every n i[n] is a natural number) and (for every n i[n] < i[n + 1]).

Definition SubSeq.
    Let a be a sequence and i be an index sequence. Subseq(a,i) is a sequence such that for every n
    Subseq(a,i)[n] = a[i[n]].

Definition ConvSubSeq.
    Let a be a sequence. a has some convergent subsequence iff there exists an index sequence i such that Subseq(a,i) converges.


Axiom IndSucc.
    n -<- n + 1.

Axiom IndPrec.
    Assume n != 0. Then there exists m such that n = m + 1.

Axiom IndNonNeg.
    n -<- 0 for no n.

Axiom IndPlusOne.
    Assume n < m. Then n + 1 =< m.

Lemma SubSeqLeq.
    Let a be a sequence. Let i be an index sequence. Then for every n n =< i[n].
Proof by induction. Let n be a natural number.
    Case n = 0. Obvious. 
    Case n != 0.
        Take m such that n = m + 1. Then m =< i[m]. 
        We can show by induction that i[k] + 1 =< i[k + 1] for every k. Obvious.
    end.
qed.

Lemma LimitSubSeq.
    Let a be a sequence. Let x be a real number. a converges to x iff for every index sequence i Subseq(a,i) converges to x.
Proof.
    Let us show that if a converges to x then for every index sequence i Subseq(a,i) converges to x.
        Assume a converges to x.
        Let i be an index sequence.
        Let eps be a positive real number.
        Take N such that for every n such that N < n dist(a[n],x) < eps (by Convergence).

        Let us show that for every n such that N < n dist(Subseq(a,i)[n],x) < eps.
            Let n be a natural number such that N < n.
            Then n =< i[n] (by SubSeqLeq).
            Hence N < i[n] (by MixedTransitivity).
            Hence dist(Subseq(a,i)[n],x) = dist(a[i[n]],x) < eps.
        end.
    end.

    Let us show that if for every index sequence i Subseq(a,i) converges to x then a converges to x.
        Assume for every index sequence i Subseq(a,i) converges to x.
        Define i[k] = k for k in NAT.
        i is an index sequence.
        Subseq(a,i) converges to x.
        For every n a[n] = Subseq(a,i)[n].
        Hence a = Subseq(a,i) (by SequenceEq).
        Hence a converges to x.
    end.
end.



### Cauchy

Axiom BolzanoWeierstrass.
    Let a be a bounded sequence. Then a has some convergent subsequence.

Definition Cauchy.
    A cauchy sequence is a sequence a such that for every positive real number eps there exists N such that
    for every n,m such that (N < n and N < m) dist(a[n],a[m]) < eps.

Lemma CauchyBounded.
    Let a be a cauchy sequence. Then a is bounded.
Proof.
    Take N such that for every n,m such that (N < n and N < m) dist(a[n],a[m]) < 1 (by Cauchy, OnePos).
    N + 1 is a natural number and N < N + 1.
    Hence for every n such that N < n dist(a[n],a[N + 1]) < 1.

    Define b[k] = abs(a[k]) for k in NAT.

    maxN(b,N), 1, a[N + 1], abs(a[N + 1]), 1 + abs(a[N + 1]) are real numbers.
    Take a real number K such that K = max(1 + abs(a[N + 1]), maxN(b,N)).

    Let us show that a is bounded by K.
        Let us show that for every n abs(a[n]) =< K. 
            Let n be a natural number.
            a[n], abs(a[n]), b[n], dist(a[n],a[N + 1]), a[n] - a[N + 1], dist(a[n],a[N + 1]) + abs(a[N + 1]) are real numbers.

            We have n =< N or n > N.
            Case n =< N.
                We have abs(a[n]) = b[n] =< maxN(b,N) (by MaxN).
                We have maxN(b,N) =< K (by MaxIneqDummy).
                Therefore abs(a[n]) =< K (by LeqTransitivity).
            end.
            Case n > N.
                We have dist(a[n],a[N + 1]) < 1.
                We have 1 + abs(a[N + 1]) =< K (by MaxIneq).

                abs(a[n]) .= abs(a[n] + 0) (by Zero)
                          .= abs(a[n] + (a[N + 1] - a[N + 1])) (by Neg)
                          .= abs(a[n] + ((-a[N + 1]) + a[N + 1])) (by ComAdd)
                          .= abs((a[n] - a[N + 1]) + a[N + 1]) (by AssAdd).

                We have abs((a[n] - a[N + 1]) + a[N + 1]) =< abs(a[n] - a[N + 1]) + abs(a[N + 1]) (by AbsTriangleIneq).
                Hence abs(a[n]) =< abs(a[n] - a[N + 1]) + abs(a[N + 1]).
                Hence abs(a[n]) =< dist(a[n],a[N + 1]) + abs(a[N + 1]).

                We have dist(a[n],a[N + 1]) + abs(a[N + 1]) < 1 + abs(a[N + 1]) (by MixedAddInvariance).
                Hence abs(a[n]) =< 1 + abs(a[N + 1]) (by MixedTransitivity).
                Therefore abs(a[n]) =< K (by LeqTransitivity).
            end.
        end.
        Hence a is bounded by K (by BoundedBy).
    end.
qed.

Lemma CauchyConvSubSeq.
    Let a be a cauchy sequence such that a has some convergent subsequence. Then a converges.
Proof.
    Take a index sequence i such that Subseq(a,i) converges.
    Take a real number x such that Subseq(a,i) converges to x.

    Let us show that a converges to x.
        Let eps be a positive real number.
        Take a positive real number halfeps such that halfeps = inv(2) * eps.

        Take N1 such that for every n,m such that (N1 < n and N1 < m) dist(a[n],a[m]) < halfeps (by Cauchy).
        Take N2 such that for every n such that N2 < n dist(Subseq(a,i)[n],x) < halfeps (by Convergence).
        Take N such that N = max(N1,N2).
        Then N1 =< N and N2 =< N.

        Let us show that for every n such that N < n dist(a[n],x) < eps.
            Assume N < n. Hence N1 < n and N2 < n (by MixedTransitivity).
            We have n =< i[n] (by SubSeqLeq). Hence N1 < i[n] (by MixedTransitivity).
            a[n], a[i[n]], dist(a[n],a[i[n]]), dist(a[n],x), a[n] - a[i[n]], a[i[n]] - x, dist(a[n],a[i[n]]) + dist(a[i[n]],x) are real numbers.

            We have Subseq(a,i)[n] = a[i[n]].
            We have dist(a[n],a[i[n]]) < halfeps.
            We have dist(a[i[n]],x) < halfeps.

            dist(a[n],x) .= abs(a[n] - x) (by DistDefinition)
                         .= abs((a[n] + 0) - x) (by Zero)
                         .= abs((a[n] + (a[i[n]] - a[i[n]])) - x) (by Neg)
                         .= abs((a[n] + ((-a[i[n]]) + a[i[n]])) - x) (by ComAdd)
                         .= abs(((a[n] - a[i[n]]) + a[i[n]]) - x) (by AssAdd)
                         .= abs((a[n] - a[i[n]]) + (a[i[n]] - x)) (by AssAdd).

            We have abs((a[n] - a[i[n]]) + (a[i[n]] - x)) =< abs(a[n] - a[i[n]]) + abs(a[i[n]] - x) (by AbsTriangleIneq).
            Hence dist(a[n],x) =< abs(a[n] - a[i[n]]) + abs(a[i[n]] - x).
            Hence dist(a[n],x) =< dist(a[n],a[i[n]]) + dist(a[i[n]],x).

            We have dist(a[n],a[i[n]]) + dist(a[i[n]],x) < halfeps + halfeps (by AddInvariance).
            Hence dist(a[n],x) < halfeps + halfeps (by MixedTransitivity).
            Hence dist(a[n],x) < eps (by TwoHalf).
        end.
    end.
qed.

Theorem RComplete.
    Let a be a sequence. a is a cauchy sequence iff a converges.
Proof.
    Let us show that (If a converges then a is a cauchy sequence).
        Assume a converges.
        Take a real number x such that a converges to x.
        Let eps be a positive real number.
        
        Take a positive real number halfeps such that halfeps = inv(2) * eps.
        Take N such that for every n such that N < n dist(a[n],x) < halfeps (by Convergence).

        Let us show that for every n,m such that (N < n and N < m) dist(a[n],a[m]) < eps.
            Assume N < n and N < m.
            We have dist(a[n],x) < halfeps.
            We have dist(a[m],x) < halfeps.

            We have dist(a[n],a[m]) =< dist(a[n],x) + dist(x,a[m]) (by DistTriangleIneq).
            Hence dist(a[n],a[m]) =< dist(a[n],x) + dist(a[m],x) (by DistSymm).
            We have dist(a[n],x) + dist(a[m],x) < halfeps + halfeps (by AddInvariance).
            Hence dist(a[n],a[m]) < halfeps + halfeps (by MixedTransitivity).
            Hence dist(a[n],a[m]) < eps (by TwoHalf).
       end.
    end.

    Let us show that (If a is a cauchy sequence then a converges).
        Assume a is a cauchy sequence.
        Then a is bounded (by CauchyBounded).
        Therefore a has some convergent subsequence (by BolzanoWeierstrass).
        Hence a converges (by CauchyConvSubSeq).
    end.
qed.



### Monotonic Sequences

Definition MonInc.
    Let a be a sequence. a is monotonically increasing iff (for every n,m such that n =< m a[n] =< a[m]).
Definition MonDec.
    Let a be a sequence. a is monotonically decreasing iff (for every n,m such that n =< m a[n] >= a[m]).

Definition Mon.
    Let a be a sequence. a is monotonic iff a is monotonically increasing or a is monotonically decreasing.

Definition UpperBoundSeq.
    Let a be a bounded sequence. Let K be a real number. K is upper bound of a iff (for every n a[n] =< K).

Definition LeastUpperBoundSeq.
    Let a be a bounded sequence. LeastUpper(a) is a real number K such that (K is upper bound of a) and 
    (for every real number L such that L is upper bound of a K =< L).

Definition LowerBoundSeq.
    Let a be a bounded sequence. Let K be a real number. K is lower bound of a iff (for every n a[n] >= K).

Definition GreatestLowerBoundSeq.
    Let a be a bounded sequence. GreatestLower(a) is a real number K such that (K is lower bound of a) and
    (for every real number L such that L is lower bound of a L =< K).

Lemma MonIncCon.
    Let a be a monotonically increasing bounded sequence. Then a converges.
Proof.
    For every n a[n] =< LeastUpper(a) (by UpperBoundSeq, LeastUpperBoundSeq).
    Let us show that for every positive real number eps there exists N such that (LeastUpper(a) - eps) < a[N].
        Assume the contrary.
        Take a positive real number eps such that for every N not((LeastUpper(a) - eps) < a[N]).

        Let us show that for every n a[n] =< (LeastUpper(a) - eps).
            Let n be a natural number.
            We have not((LeastUpper(a) - eps) < a[n]).
            Therefore (LeastUpper(a) - eps) >= a[n] (by NotRuleOrder).
            Hence a[n] =< (LeastUpper(a) - eps).
        end.
        Hence (LeastUpper(a) - eps) is upper bound of a (by UpperBoundSeq).

        LeastUpper(a) - (LeastUpper(a) - eps) .= LeastUpper(a) + (-LeastUpper(a) + eps) (by MinusRule1, MinusRule2)
                                              .= (LeastUpper(a) - LeastUpper(a)) + eps (by AssAdd)
                                              .= 0 + eps (by Neg)
                                              .= eps + 0 (by ComAdd)
                                              .= eps (by Zero).

        Hence (LeastUpper(a) - eps) < LeastUpper(a).
        Hence not((LeastUpper(a) - eps) >= LeastUpper(a)) (by NotRuleOrder).
        Contradiction (by LeastUpperBoundSeq).
    end.

    Let us show that a converges to LeastUpper(a).
        Let eps be a positive real number.
        Take N such that (LeastUpper(a) - eps) < a[N].

        Let us show that for every n such that N < n dist(a[n],LeastUpper(a)) < eps.
            Assume N < n.
            Hence a[N] =< a[n] (by MonInc).
            We have a[n] =< LeastUpper(a).
            Hence dist(a[n],LeastUpper(a)) = abs(LeastUpper(a) - a[n]) = LeastUpper(a) - a[n].

            We have (LeastUpper(a) - eps) + eps < a[N] + eps (by MixedAddInvariance).
            We have ((LeastUpper(a) - eps) + eps) - a[N] < (a[N] + eps) - a[N] (by MixedAddInvariance).

            ((LeastUpper(a) - eps) + eps) - a[N] .= (LeastUpper(a) + (-eps + eps)) - a[N] (by AssAdd)
                                                 .= (LeastUpper(a) + (eps - eps)) - a[N] (by ComAdd)
                                                 .= (LeastUpper(a) + 0) - a[N] (by Neg)
                                                 .= LeastUpper(a) - a[N] (by Zero).

            (a[N] + eps) - a[N] .= (eps + a[N]) - a[N] (by ComAdd)
                                .= eps + (a[N] - a[N]) (by AssAdd)
                                .= eps + 0 (by Neg)
                                .= eps (by Zero).

            Hence LeastUpper(a) - a[N] < eps.
            
            We have LeastUpper(a) - a[n] =< LeastUpper(a) - a[N].
            Hence dist(a[n],LeastUpper(a)) < eps (by MixedTransitivity).
        end.
    end.
qed.

Theorem MonCon.
    Let a be a monotonic sequence. a converges iff a is bounded.
Proof.
    We have (If a converges then a is bounded) (by ConvergentImpBounded).

    Assume a is bounded.
    Case a is monotonically increasing.
        Then a converges (by MonIncCon). 
    end.
    Case a is monotonically decreasing.
        Let us show that (-1) *'' a is monotonically increasing.
            Assume n =< m.
            Then a[n] >= a[m] (by MonDec).
            Then -a[n] =< -a[m] (by OrdMirrorLeq).
            
            ((-1) *'' a)[n] .= (-1) * a[n]
                            .= -a[n] (by MinusRule4).
            ((-1) *'' a)[m] .= (-1) * a[m]
                            .= -a[m] (by MinusRule4).

            Hence ((-1) *'' a)[n] =< ((-1) *'' a)[m].
        end.

        Let us show that (-1) *'' a is bounded.
            Take a real number K such that for every n abs(a[n]) =< K (by BoundedSequence).

            Let us show that for every n abs(((-1) *'' a)[n]) =< K.
                abs(((-1) *'' a)[n]) .= abs((-1) * a[n]) (by SequenceConstProd)
                                     .= abs(-a[n]) (by MinusRule4)
                                     .= abs(a[n]) (by AbsPosNeg).
                Hence abs(((-1) *'' a)[n]) =< K.
            end.

            Hence (-1) *'' a is bounded by K (by BoundedBy).
        end.

        Hence (-1) *'' a converges (by MonIncCon).
        Take a real number x such that (-1) *'' a converges to x (by Conv).

        Let us show that (-1) *'' ((-1) *'' a) = a.
            Let us show that for every n ((-1) *'' ((-1) *'' a))[n] = a[n].
                Let n be a natural number.
                ((-1) *'' ((-1) *'' a))[n] .= (-1) * ((-1) *'' a)[n] (by SequenceConstProd)
                                           .= (-1) * ((-1) * a[n]) (by SequenceConstProd)
                                           .= -(-a[n]) (by MinusRule4)
                                           .= a[n] (by MinusRule2).
            end.
            Hence (-1) *'' ((-1) *'' a) = a (by SequenceEq).
        end.

        Then (-1) *'' ((-1) *'' a) converges to (-1) * x (by ProdConstConv).
        Hence a converges (by Conv).
    end.
qed.

Definition PosInf.
    Let a be a sequence. a converges to positive infinity iff for every real number K there exists N such that
    for every n such that N < n a[n] >= K.

Definition NegInf.
    Let a be a sequence. a converges to negative infinity iff for every real number K there exists N such that
    for every n such that N < n a[n] =< K.

# limsup liminf

Let b denote a real number. 
Let A, B, S denote a set.


Definition BoundedAboveBy.
    Let S be a set. Assume every element of S is a real number. Let b be a real number. S is bounded above by b iff for every real number x such that x is an element of S x =< b.

Definition BoundedAbove.
    Let S be a set. Assume every element of S is a real number. S is bounded above iff there exists a real number b such that S is bounded above by b.

Definition BoundedBelowBy.
    Let S be a set. Assume every element of S is a real number. Let b be a real number. S is bounded below by b iff for every real number x such that x is an element of S x >= b.

Definition BoundedBelow.
    Let S be a set. Assume every element of S is a real number. S is bounded below iff there exists a real number b such that S is bounded below by b.

Definition Sup. 
    Let S be a set. Assume every element of S is a real number. 
    Assume that S is bounded above. Let a be a real number such that S is bounded above by a. 
    sup(S) = a iff for every real number b such that b < a S is not bounded above by b.

Definition Inf.
    Let S be a set. Assume every element of S is a real number. 
    Assume that S is bounded below. Let a be a real number such that S is bounded below by a. 
    inf(S) = a iff for every real number b such that b > a S is not bounded below by b.

Definition LimSup.
    Let a be a sequence. Let E be a set such that E = { x | x is a real number and there exists an index sequence i such that Subseq(a,i) converges to x }. limsup(a) = sup(E) iff E is bounded above.

Definition LimInf.
    Let a be a sequence. Let E be a set such that E = { x | x is a real number and there exists an index sequence i such that Subseq(a,i) converges to x }. limsup(a) = inf(E) iff E is bounded below.



###Eindeutigkeit von Sup und Inf?



#Theorem LimSupInE.
#    Let a be a sequence. 
#    Let E be a set such that E = { x | x is a real number and there exists an index sequence i such that Subseq(a,i) converges to x }. 
#    Assume E is bounded above and E is bounded below.
#    Then limsup(a) is an element of E.
#Proof.
#    ### +inf, -inf umgegangen durch bounded above / below
#    Assume E is bounded above and E is bounded below.
    

     

           






