[prove off]
[read Sequences/Naturals.ftl]
[prove on]
#[prove off][check off]
[prove on][check on]
[sequence/-s]
[converge/-s]

Let NAT denote the set of natural numbers.
Let REAL denote the set of real numbers.
Let n, m, N, N1, N2, N3 denote natural numbers.

[prove off]
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

Signature Limit.
    Let a be a sequence. Assume a converges. lim a is a real number such that a converges to lim a.



### Limit is unique

Lemma DistEqual.
    Let x and y be real numbers. Assume for every positive real number eps dist(x,y) < eps.
    Then x = y.
Proof.
	Assume the contrary.
    Then there exists a positive real number eps2 such that eps2 < dist(x,y).
    A contradiction.
qed.

Lemma LimitUnique.
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

        halfeps + halfeps .= (1 * halfeps) + (1 * halfeps) (by OneDummy)
                          .= (1 + 1) * halfeps (by DistribDummy)
                          .= 2 * (inv(2) * eps)
                          .= (2 * inv(2)) * eps (by AssMult)
                          .= 1 * eps (by Inverse)
                          .= eps (by OneDummy).

        Hence dist(x,y) < eps.
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

Signature MaxAbsN.
    Let a be a sequence. maxN(a,N) is a real number such that
    (there exists n such that n =< N and maxN(a,N) = a[n]) and
    (for every n such that n =< N a[n] =< maxN(a,N)).

Lemma MaxIneqDummy.
    Let a,b be real numbers. b =< max(a,b).

Lemma MixedAddInvariance.
    Let a,b,c,d be real numbers. a < c /\ b =< d => a + b < c + d.

Lemma ConvergentImpBounded.
    Let a be a sequence. Assume that a converges. Then a is bounded.
Proof.
    Take a real number x such that a converges to x.
    Take N such that for every n such that N < n dist(a[n],x) < 1 (by Convergence, OnePos).

    [prove off]Take a sequence b such that for every n b[n] = abs(a[n]).[prove on]
    #Define b[k] = abs(a[k]) for k in NAT.
    Take a real number K such that K = max(1 + abs(x), maxN(b,N)).

    Let us show that a is bounded by K.
        Let us show that for every n abs(a[n]) =< K. 
            Let n be a natural number.
            We have n =< N or n > N.
            Case n =< N.
                We have abs(a[n]) = b[n] =< maxN(b,N) (by MaxAbsN).
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
        Assume eps is a positive real number. 
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



### Sequence (-1)^n has finite range.

Axiom EvenOrOdd.
    There exists N such that n = 2 * N or n = (2 * N) + 1.

Lemma.
    Let a be a sequence such that for every n (a[2 * n] = 1 and a[(2 * n) + 1] = -1).
    Then a has finite range.
Proof.
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
                Take N such that n = 2 * N or n = (2 * N) + 1 (by EvenOrOdd).
                Then x = 1 or x = -1.
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
        Hence ranN(a,1) = ran(a).
    end.
qed.


### Neighborhood

Definition Neighb.
    Let eps be a positive real number. Let x be a real number.
    Neighb(x,eps) = {y | y is a real number such that dist(y,x) < eps}.

Lemma ConvNeighborhood.
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

Definition LimitPointOfSet.
    Let E be a set. Assume every element of E is a real number. A limit point of E
    is a real number x such that for every positive real number eps there exists an element
    y of E such that y is an element of Neighb(x,eps) and y != x.

#Lemma ConvLimitPoint.
#    Let E be a subset of REAL. Let x be a limit point of E. Then there exists a sequence a
#    such that a converges to x and for every n a[n] is an element of E.
#Proof.
#    Let us show that for every n such that n > 0 there exists an element y of E such that
#    y is an element of Neighb(x,inv(n)) and y != x.
#        Assume n > 0.
#        Then inv(n) is a positive real number.
#        Take an element y of E such that y is an element of Neighb(x,inv(n))
#            and y != x (by LimitPointOfSet).
#    end.
#
#    Define a[n] = Case n = 0 -> Choose an element y of E such that y is an element of
#                                Neighb(x,1) and y != x in y,
#                  Case n > 0 -> Choose an element y of E such that y is an element of
#                                Neighb(x,inv(n)) and y != x in y
#    for n in NAT.
#
#    Then for every n a[n] is an element of E.
#    Let us show that a converges to x.
#        Let eps be a positive real number.
#        Take N such that 1 < N * eps (by ArchimedeanAxiom, OnePos).
#
#        Let us show that for every n such that N < n dist(a[n],x) < eps.
#            Assume N < n. Then n != 0.
#            Then a[n] is an element of E such that a[n] is an element of Neighb(x,inv(n)).
#            Hence dist(a[n],x) < inv(n).
#
#            Let us show that inv(n) < eps.
#                We have N * eps < n * eps (by ComMult, MultInvariance).
#                Hence 1 < n * eps (by TransitivityOfOrder).
#
#                inv(n) is positive.
#                Hence inv(n) * 1 < inv(n) * (n * eps) (by MultInvariance).
#                We have inv(n) * 1 = inv(n) (by One).
#                inv(n) * (n * eps) .= (inv(n) * n) * eps (by AssMult)
#                                   .= 1 * eps (by InvDummy)
#                                   .= eps (by OneDummy).
#            end.
#            Hence dist(a[n],x) < eps (by TransitivityOfOrder).
#        end.
#    end.
#qed.

[prove on]


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


Lemma SumConv.
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

        halfeps + halfeps .= (1 * halfeps) + (1 * halfeps) (by OneDummy)
                          .= (1 + 1) * halfeps (by DistribDummy)
                          .= 2 * (inv(2) * eps)
                          .= (2 * inv(2)) * eps (by AssMult)
                          .= 1 * eps (by Inverse)
                          .= eps (by OneDummy).

        Hence dist((a +' b)[n],(x + y)) < eps.
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

Lemma SumConstConv.
    Let a be a sequence. Let x,c be real numbers. Assume a converges to x.
    Then c +'' a converges to c + x.
Proof.
    # Define cn[n] = c for n in NAT.
    # b is a sequence.
    [prove off]Take a sequence cn such that for every n cn[n] = c.[prove on]

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

Lemma ProdConstConv.
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


#[prove off]
Lemma MinusRule5.
    Let a,b be real numbers. 
    Then (a * (-b)) = -(a * b) and ((-b) * a) = -(b * a).
Proof.
        (1) a * (-b) .= a * ((-1)*b) (by MinusRule4)
                     .= (a * (-1)) * b (by AssMult)
                     .= ((-1) * a) * b (by ComMult)
                     .= (-1) * (a * b) (by AssMult)
                     .= -(a * b) (by MinusRule4).

        ((-b) * a) .= -(b * a) (by ComMult, 1).
qed.

Lemma MinusRule6.
    Let a,b be real numbers. 
    Then ((-a) * (-b)) = a * b.
Proof.
    ((-a) * (-b)) .= -(a * (-b)) (by MinusRule5)
                  .= -(-(a * b)) (by MinusRule5)
                  .= a * b (by MinusRule2).
qed.

Lemma Binomi1.
    Let a,b,c,d be real numbers.
    Then (a + b) * (c + d) = ((a * c) + (b * c)) + ((a * d) + (b * d)) .
Proof.
    (a + b) * (c + d) .= ((a + b) * c) + ((a + b) * d) (by Distrib)
                      .= ((a * c) + (b * c)) + ((a * d) + (b * d)) (by DistribDummy).
qed.

Lemma Binomi2.
    Let a,b,c,d be real numbers.
    Then (a - b) * (c - d) = ((a * c) - (b * c)) + (-(a * d) + (b * d)).
Proof.
    (a - b) * (c - d) .= ((a * c) + ((-b) * c)) + ((a * (-d)) + ((-b) * (-d))) (by Binomi1)
                      .= ((a * c) - (b * c)) + (-(a * d) + (b * d)) (by MinusRule5, MinusRule6).
qed.

Lemma Identity1.
    Let a,b,c,d be real numbers. 
    Then (a * b) - (c * d) = ((a - c) * (b - d)) + ((c * (b - d)) + (d * (a - c))).
Proof.
    ((a - c)*(b - d)) + ((c*(b - d)) + (d*(a - c))) 
        .= (((a * b) - (c * b)) + (-(a * d) + (c * d))) + ((c * (b - d)) + (d * (a - c))) (by Binomi2)
        .= (((a * b) - (c * b)) + (-(a * d) + (c * d))) + (((c * b) + (c * (-d))) + ((d * a) + (d * (-c)))) (by Distrib)
        .= (((a * b) - (c * b)) + (-(a * d) + (c * d))) + (((c * b) + (-(c * d))) + ((d * a) + (-(d * c)))) (by MinusRule5)
        .= ((c * b) + (-(c * d))) + ((((a * b) - (c * b)) + (-(a * d) + (c * d))) + ((d * a) + (-(d * c)))) (by BubbleAdd)
        .= ((c * b) + (-(c * d))) + (((a * b) - (c * b)) + ((-(a * d) + (c * d)) + ((a * d) + (-(c * d))))) (by AssAdd, ComMult)
        .= ((c * b) + (-(c * d))) + (((a * b) - (c * b)) + ((-(a * d) + (c * d)) + (-(-((a * d) + (-(c * d))))))) (by MinusRule2)
        .= ((c * b) + (-(c * d))) + (((a * b) - (c * b)) + ((-(a * d) + (c * d)) + (-(-(a * d) + (c * d))))) (by ComAdd, MinusRule3)
        .= ((c * b) + (-(c * d))) + (((a * b) - (c * b)) + 0) (by Neg)
        .= ((-(c * d)) + (c * b)) + (-(c * b) + (a * b)) (by ComAdd, Zero)
        .= (-(c * d)) + ((c * b) + (-(c * b) + (a * b))) (by AssAdd)
        .= (-(c * d)) + (((c * b) -(c * b)) + (a * b)) (by AssAdd)
        .= -(c * d) + (0 + (a * b)) (by Neg)
        .= -(c * d) + ((a * b) + 0) (by ComAdd)
        .= -(c * d) + (a * b) (by Zero)
        .= (a * b) - (c * d) (by ComAdd).
qed.

#[exit]
#[prove off]

Signature Sqrt.
Let x be a positive real number. sqrt(x) is a positive real number.

Axiom Wurz.
Let x be a positive real number. sqrt(x)*sqrt(x) = x.

Lemma ConstMultSum.
    Let a,b be sequences. Let x,y be real numbers such that for every n b[n] = y * (a[n] + (-x)). Assume a converges to x.
    Then b converges to 0.
Proof.
    [prove off]Take a sequence sum such that for every n sum[n] = (-x) + a[n]. [prove on]
    sum converges to 0 (by SumConstConv, ComAdd, Neg).
    Let us show that for every n b[n] = y * sum[n].
    Proof.
        b[n] .= y * (a[n] + (-x))
             .= y * ((-x) + a[n]) (by ComAdd)
             .= y * sum[n].
    qed.
    Hence b = y *'' sum (by SequenceEq).
    Hence b converges to 0 (by ProdConstConv, ComMult, ZeroMult).
qed.


Lemma ProdConv.
    Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
    Let a *' b be a sequence such that for every natural number n (a *' b)[n] = a[n] * b[n].
    Then a *' b converges to x * y.
Proof.
#Strategie: zerteile (s[n]*t[n]) - (x*y) = ((s[n] - x)*(t[n] - y)) + ((x*(t[n] - y)) + (y*(s[n] - x))) in Teilfolgen und zeige erst die Konvergenz der Teile um daraus die Konvergenz des Ganzen zu folgern.
    [prove off] (1) Take a sequence s1 such that for every n s1[n] = (a[n] - x) * (b[n] - y). [prove off]
    Let us show that s1 converges to 0.
    proof.
        Assume eps is a positive real number. 
        Take a positive real number Eps such that Eps = sqrt(eps) (by Sqrt).
        Take N1 such that for every n such that N1 < n dist(a[n],x) < Eps (by Convergence).
        Take N2 such that for every n such that N2 < n dist(b[n],y) < Eps (by Convergence).
        Take N such that N = max(N1,N2).
        Let us show that for every n such that N < n dist(s1[n],0) < eps.
        Proof.
            Assume N < n.
            dist(a[n],x) < Eps and dist(b[n],y) < Eps.
            dist(a[n],x), dist(b[n],y) and Eps are nonnegative.
            Then dist(a[n],x) * dist(b[n],y) < eps (by NonNegMultInvariance, Wurz).
            Hence abs(a[n] - x) * abs(b[n] - y) < eps.
            Hence abs((a[n] - x) * (b[n] - y)) < eps (by AbsMult).
            Hence abs(((a[n] - x) * (b[n] - y)) - 0) < eps (by Zero, NegOfZero).
        qed.
    qed.
    [prove off] (2) Take a sequence s2 such that for every n s2[n] = (x * (b[n] + (-y))) + (y * (a[n] + (-x))). [prove on]
    Let us show that s2 converges to 0.
    proof.
        [prove off] Take sequences s2a, s2b such that for every n s2b[n] = x * (b[n] + (-y)) and s2a[n] = y * (a[n] + (-x)). [prove on]
        s2a, s2b converge to 0 (by ConstMultSum). 
        Let us show that for every n s2[n] = s2b[n] + s2a[n].
        Proof.
            s2[n] .= (x * (b[n] + (-y))) + (y * (a[n] + (-x)))
                  .= s2b[n] + s2a[n].
        qed.
        Hence s2 converges to 0 (by SumConv).
    qed.
    [prove off] (3) Take a sequence s3 such that for every n s3[n] = (a[n] * b[n]) - (x * y). [prove on]
    Let us show that s3 converges to 0.
    proof.
        Let us show that for every n s3[n] = s1[n] + s2[n].
        Proof.
            s3[n] .= (a[n] * b[n]) - (x * y) (by 3)
                  .= ((a[n] - x) * (b[n] - y)) + ((x * (b[n] - y)) + (y * (a[n] - x))) (by Identity1)
                  .= s1[n] + s2[n] (by 1, 2).
        qed.
        Therefore s3 converges to 0 (by SumConv).
    qed. 
    Let eps be a positive real number.
    Take N such that for every n such that N < n dist(s3[n],0) < eps (by Convergence).
    Let us show that for every n such that N < n dist(a[n] * b[n],x * y) < eps.
    Proof.
        Assume N < n.
        dist(s3[n],0) .= dist((a[n] * b[n]) - (x * y),0) (by 3)
                      .= abs(((a[n] * b[n]) - (x * y)) - 0) (by DistDefinition)
                      .= abs((a[n] * b[n]) - (x * y)) (by NegOfZero, Zero)
                      .= dist(a[n] * b[n],x * y) (by DistDefinition).
    qed.
qed.



[prove on]
Lemma AbsTriangleIneq2.
    Let x,y be real numbers. Then abs(x) - abs(y) =< abs(x - y).
Proof.
    abs(x) .= abs(x + ((-y) + y)) (by Zero, Neg, ComAdd)
           .= abs((x + (-y)) + y) (by AssAdd).
    abs((x + (-y)) + y) =< abs(x - y) + abs(y) (by AbsTriangleIneq).
    Hence abs(x) =< abs(x + (-y)) + abs(y).
    abs(x) + (-abs(y)) =< (abs(x - y) + abs(y)) + (-abs(y)) (by LeqAddInvariance).
    (abs(x - y) + abs(y)) + (-abs(y)) = abs(x - y) (by AssAdd, Neg, Zero).
    Hence abs(x) - abs(y) =< abs(x - y) (by LeqTransitivity).
qed.   



Lemma InvAdd.
    Let a,b,c,d be real numbers. Assume (a != 0 and b != 0) and (c != 0 and d != 0). 
    Then (a * inv(b)) + (c * inv(d)) = ((a * d) + (b * c)) * inv(b * d).
Proof.
    (a * inv(b)) + (c * inv(d)) .= ((a * inv(b)) * 1) + (1 * (c * inv(d))) (by One, OneDummy)
                                .= ((a * inv(b)) * (d * inv(d))) + ((b * inv(b)) * (c * inv(d))) (by Inverse)
                                .= (a * (inv(b) * (d * inv(d)))) + (b * (inv(b) * (c * inv(d)))) (by AssMult)
                                .= (a * ((inv(b) * d) * inv(d))) + (b * ((inv(b) * c) * inv(d))) (by AssMult)
                                .= (a * ((d * inv(b)) * inv(d))) + (b * ((c * inv(b)) * inv(d))) (by ComMult)
                                .= (a * (d * (inv(b) * inv(d)))) + (b * (c * (inv(b) * inv(d)))) (by AssMult)
                                .= ((a * d) * (inv(b) * inv(d))) + ((b * c) * (inv(b) * inv(d))) (by AssMult)
                                .= ((a * d) * inv(b * d)) + ((b * c) * inv(b * d)) (by InvRule2)
                                .= ((a * d) + (b * c)) * inv(b * d) (by DistribDummy).
qed.



Lemma InvCanc.
    Let a, b be real numbers. Assume a != 0 and b != 0.
    Then (a * inv(b)) * (b * inv(a)) = 1.
Proof.
    (a * inv(b)) * (b * inv(a)) .= ((a * inv(b)) * b) * inv(a) (by AssMult)
                                .= (a * (inv(b) * b)) * inv(a) (by AssMult)
                                .= (a * 1) * inv(a) (by InvDummy)
                                .= a * inv(a) (by One)
                                .= 1 (by Inverse).
qed.


Lemma NegMultInvariance.
Let x, y, z be real numbers.
(x < y /\ z < 0) => z * x > z * y.
Proof.
    Assume x < y /\ z < 0.
    Therefore pos(-z).    
    Hence (-z) * x < (-z) * y.
    Hence -((-z) * x) > -((-z) * y) (by OrdMirror).
    -((-z) * x) .= (-(-z)) * x (by MinusRule5)
                .= z * x (by MinusRule2).
    -((-z) * y) .= (-(-z)) * y (by MinusRule5)
                .= z * y (by MinusRule2).
qed.


Lemma InvSwapIneq.
    Let a, b, c, d be positive real numbers. Assume (a != 0 and b != 0) and (c != 0 and d != 0). 
    If a * inv(b) < c * inv(d) then b * inv(a) > d * inv(c).
Proof.
    Assume a * inv(b) < c * inv(d).
    We have pos(b * inv(a)) and pos(d * inv(c)).
    (b * inv(a)) * (a * inv(b)) < (b * inv(a)) * (c * inv(d)) (by MultInvariance).
    (b * inv(a)) * (a * inv(b)) = 1 (by InvCanc).
    Hence 1 < (b * inv(a)) * (c * inv(d)).
    (d * inv(c)) * 1 < (d * inv(c)) * ((b * inv(a)) * (c * inv(d))) (by MultInvariance).
    d * inv(c) < (d * inv(c)) * ((b * inv(a)) * (c * inv(d))) (by One).
    (d * inv(c)) * ((b * inv(a)) * (c * inv(d))) .= ((b * inv(a)) * (c * inv(d))) * (d * inv(c)) (by ComMult)
                                                 .= (b * inv(a)) * ((c * inv(d)) * (d * inv(c))) (by AssMult)
                                                 .= (b * inv(a)) * 1 (by InvCanc)
                                                 .= b * inv(a) (by One).   
qed.



Lemma AbsInv.
    Let x be a real number. Assume x != 0. Then abs(inv(x)) = inv(abs(x)).
Proof.
    We have pos(abs(inv(x))) and pos(inv(abs(x))).
    pos(1) (by OnePos).
    (1) Hence ( abs(inv(x)) = abs(abs(inv(x))) and inv(abs(x)) = abs(inv(abs(x))) ) and abs(1) = 1 (by AbsValue).
    abs(inv(x)) .= abs(abs(inv(x))) (by 1)
                .= abs(abs(inv(x)) * 1) (by One)
                .= abs(abs(inv(x)) * (abs(x) * inv(abs(x)))) (by Inverse)
                .= abs((abs(inv(x)) * abs(x)) * inv(abs(x))) (by AssMult)
                .= abs(abs(inv(x) * x) * inv(abs(x))) (by AbsMult)
                .= abs(abs(1) * inv(abs(x))) (by InvDummy)
                .= abs(1 * inv(abs(x))) (by 1) 
                .= abs(inv(abs(x))) (by OneDummy)
                .= inv(abs(x)) (by 1).    
qed.


Lemma InvOne.
    inv(1) = 1.
Proof.
    1 .= 1 * inv(1) (by Inverse)
      .= inv(1) (by OneDummy).
qed.   
    

Lemma DivConv.
    Let a be a sequence. Let x be a real number such that x != 0. Assume a converges to x. 
    Assume for every n a[n] != 0.
    Let div(a) be a sequence such that for every natural number n (div(a))[n] = inv(a[n]).
    Then div(a) converges to inv(x).
Proof.
    Let eps be a positive real number.
    inv(2) * abs(x) is a positive real number.	
    Take a natural number m such that for every n such that m < n dist(a[n],x) < inv(2) * abs(x) (by Convergence).
    Let us show that for every n such that m < n inv(2) * abs(x) < abs(a[n]).
    Proof. 
        Assume m < n.
        Let us show that abs(x) - abs(a[n]) < inv(2) * abs(x).
        Proof.
            abs(x) - abs(a[n]) =< abs(x - a[n]) (by AbsTriangleIneq2).
            abs(x - a[n]) .= abs(-(x - a[n])) (by AbsPosNeg)
                          .= abs(-x - (-a[n])) (by MinusRule1)
                          .= abs(-x + a[n]) (by MinusRule2)
                          .= abs(a[n] - x) (by ComAdd).
            abs(a[n] - x) < inv(2) * abs(x) (by DistDefinition).
            Hence the thesis (by MixedTransitivity).
        qed.
        Let us show that -abs(a[n]) < ((-1) * inv(2)) * abs(x).
            (abs(x) + (-abs(a[n]))) + (-abs(x)) < (inv(2) * abs(x)) + (-abs(x)) (by MixedAddInvariance). 
            (abs(x) + (-abs(a[n]))) + (-abs(x)) .= abs(x) + ((-abs(a[n])) + (-abs(x))) (by AssAdd)
                                                .= abs(x) + ((-abs(x)) + (-abs(a[n]))) (by ComAdd)
                                                .= (abs(x) + (-abs(x))) + (-abs(a[n])) (by AssAdd)
                                                .= (-abs(a[n])) (by Neg, ComAdd, Zero).
            -abs(a[n]) < (inv(2) * abs(x)) + (-abs(x)) (by AssAdd, Neg, Zero).
            (inv(2) * abs(x)) + (-abs(x)) .= (inv(2) * abs(x)) + ((-1) * abs(x)) (by MinusRule4)
                                          .= (inv(2) + (-1)) * abs(x) (by DistribDummy)
                                          .= ((1 * inv(2)) + (-(1 * inv(1)))) * abs(x) (by OneDummy, Inverse)
                                          .= ((1 * inv(2)) + ((-1) * inv(1))) * abs(x) (by OneDummy, MinusRule4)
                                          .= ((1 * inv(2)) + ((-1) * inv(1))) * abs(x) (by MinusRule4)
                                          .= (((1 * 1) + (2 * (-1))) * inv(2 * 1)) * abs(x) (by InvAdd)
                                          .= ((1 + ((-1) * 2)) * inv(2)) * abs(x) (by One, ComMult).
            1 + ((-1) * 2) .= 1 + -(1 * 2) (by MinusRule5)
                           .= 1 + -2 (by OneDummy)
                           .= -(2 - 1) (by MinusRule3)
                           .= -1.
        qed.
        Therefore abs(a[n]) > -(((-1) * inv(2)) * abs(x)) (by OrdMirror, MinusRule2).
        -(((-1) * inv(2)) * abs(x)) .= ((-(-1)) * inv(2)) * abs(x) (by MinusRule5)
                                    .= (1 * inv(2)) * abs(x) (by MinusRule2)
                                    .= inv(2) * abs(x) (by OneDummy)
                                    .= abs(x) * inv(2) (by ComMult).
        Therefore abs(a[n]) > abs(x) * inv(2) (by TransitivityOfOrder).
    qed.
    Let us show that pos((inv(2) * eps) * (abs(x) * abs(x))).
    Proof.
        pos(inv(2)) (by PosTwo, InvMono).
        pos(eps).
        pos(inv(2) * eps) (by MultClosed).
        abs(x) != 0.
        pos(abs(x) * abs(x)) (by PosSquare).
        Hence the thesis (by MultClosed).
    qed.    
    Take an N1 such that for every n such that N1 < n dist(a[n],x) < (inv(2) * eps) * (abs(x) * abs(x)) (by Convergence). 
    Take an N2 such that N2 = max(N1,m).
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
            We have pos((eps * (abs(x) * abs(x))) * (inv(2) * abs(inv(x)))).
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
    A index sequence is a sequence i such that (for every n i[n] is a natural number) and (for every n i[n] < i[n+1]).

Definition SubSeq.
    Let a be a sequence and i be a index sequence. Subseq(a,i) is a sequence such that for every  n
    Subseq(a,i)[n] = a[i[n]].

# Mit Topologie Gruppe absprechen? (Closed/Compact)

### Cauchy

Definition Cauchy.
    A cauchy sequence is a sequence a such that for every positive real number eps there exists N such that
    for every n,m such that (N < n and N < m) dist(a[n],a[m]) < eps.

Lemma CauchyInR.
    Let a be a sequence. a is a cauchy sequence iff a is convergent.
Proof.
    Let us show that ((a is convergent) => (a is a cauchy sequence)).
        Assume a is convergent.
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
        
            halfeps + halfeps .= (1 * halfeps) + (1 * halfeps) (by OneDummy)
                              .= (1 + 1) * halfeps (by DistribDummy)
                              .= 2 * (inv(2) * eps)
                              .= (2 * inv(2)) * eps (by AssMult)
                              .= 1 * eps (by Inverse)
                              .= eps (by OneDummy).

            Hence dist(a[n],a[m]) < eps.
       end.
    end.

    [prove off]
    Let us show that ((a is a cauchy sequence) => (a is convergent)).
    
    end.
    [prove on]
qed.



### Monotonic Sequences

Definition MonInc.
    Let a be a sequence. a is monotonically increasing iff (for every n,m such that n =< m a[n] =< a[m]).

Definition MonDec.
    Let a be a sequence. a is monotonically decreasing iff (for every n,m such that n =< m a[n] >= a[m]).

Definition Mon.
    Let a be a sequence. a is monotonic iff a is monotonically increasing or a is monotonically decreasing.

Definition UpperBound.
    Let a be a bounded sequence. Let K be a real number. K is upper bound of a iff (for every n a[n] =< K).

Definition LeastUpperBound.
    Let a be a bounded sequence. LeastUpper(a) is a real number K such that (K is upper bound of a) and 
    (for every real number L such that L is upper bound of a K =< L).

Definition LowerBound.
    Let a be a bounded sequence. Let K be a real number. K is lower bound of a iff (for every n a[n] >= K).

Definition GreatestLowerBound.
    Let a be a bounded sequence. GreatestLower(a) is a real number K such that (K is lower bound of a) and
    (for every real number L such that L is lower bound of a L =< K).

Lemma NotRuleOrder.
    Let a,b be real numbers. a < b iff not(a >= b).

Lemma MonIncCon.
    Let a be a monotonically increasing bounded sequence. Then a converges.
Proof.
    For every n a[n] =< LeastUpper(a) (by UpperBound, LeastUpperBound).
    Let us show that for every positive real number eps there exists N such that (LeastUpper(a) - eps) < a[N].
        Assume the contrary.
        Take a positive real number eps such that for every N not((LeastUpper(a) - eps) < a[N]).

        Let us show that for every n a[n] =< (LeastUpper(a) - eps).
            Let n be a natural number.
            We have not((LeastUpper(a) - eps) < a[n]).
            Therefore (LeastUpper(a) - eps) >= a[n] (by NotRuleOrder).
            Hence a[n] =< (LeastUpper(a) - eps).
        end.
        Hence (LeastUpper(a) - eps) is upper bound of a (by UpperBound).

        LeastUpper(a) - (LeastUpper(a) - eps) .= LeastUpper(a) + (-LeastUpper(a) + eps) (by MinusRule1, MinusRule2)
                                              .= (LeastUpper(a) - LeastUpper(a)) + eps (by AssAdd)
                                              .= 0 + eps (by Neg)
                                              .= eps + 0 (by ComAdd)
                                              .= eps (by Zero).

        Hence (LeastUpper(a) - eps) < LeastUpper(a).
        Hence not((LeastUpper(a) - eps) >= LeastUpper(a)) (by NotRuleOrder).
        Contradiction (by LeastUpperBound).
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

Lemma MonCon.
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

# Define limsup liminf?

Let b denote a real number. 
Let A, B, S denote a set.


Definition BoundedAboveBy.
Let S be a set. Assume every element of S is a real number. Let b be a real number. S is bounded above by b iff for every real number x such that x is an element of S x =< b.

#Let b is an upper bound of S stand for S is bounded above by b.

Definition BoundedAbove.
Let S be a set. Assume every element of S is a real number. S is bounded above iff there exists a real number b such that S is bounded above by b.

Definition BoundedBelowBy.
Let S be a set. Assume every element of S is a real number. Let b be a real number. S is bounded below by b iff for every real number x such that x is an element of S x >= b.

#Let b is an lower bound of S stand for S is bounded below by b.

Definition BoundedBelow.
Let S be a set. Assume every element of S is a real number. S is bounded below iff there exists a real number b such that S is bounded below by b.

Definition Sup. 
Let S be a set. Assume every element of S is a real number. 
Assume that S is bounded above. Let a be a real number such that S is bounded above by a. 
sup(S) = a iff for every real number b such that b < a S is not bounded above by b.


#Let a is the least upper bound of S stand for a = sup(S).

Definition Inf.
Let S be a set. Assume every element of S is a real number. 
Assume that S is bounded below. Let a be a real number such that S is bounded below by a. 
inf(S) = a iff for every real number b such that b > a S is not bounded below by b.

#Let a is the least lower bound of S stand for a = inf(S).

Definition LimSup.
Let a be a sequence. Let E be a set such that E = { x | x is a real number and there exists an index sequence i such that Subseq(a,i) converges to x }. limsup(a) = sup(E) iff E is bounded above.

Definition LimInf.
Let a be a sequence. Let E be a set such that E = { x | x is a real number and there exists an index sequence i such that Subseq(a,i) converges to x }. limsup(a) = inf(E) iff E is bounded below.


###Eindeutigkeit von Sup und Inf?






