[prove off]
[read Forster/Naturals.ftl]
[read ramsey/sets.ftl]
#[read nats.ftl]
#[read ramsey/utils.ftl]
[prove on]
#[prove off]
#[check off]
[prove on][check on]
[sequence/-s]

Let NAT denote the set of natural numbers.
Let REAL denote the set of real numbers.
Let n, N, N1, N2, N3 denote natural numbers.



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
    Let p be a sequence. Let x, y be real numbers. Assume p converges to x and p converges to y.
    Then x = y.
Proof.
    Let us show that for every positive real number Eps dist(x,y) < Eps.
        Let eps be a positive real number.
        Take a positive real number halfeps such that halfeps = inv(2) * eps.

        Take N1 such that for every n such that N1 < n dist(p[n],x) < halfeps (by Convergence).
        Take N2 such that for every n such that N2 < n dist(p[n],y) < halfeps (by Convergence).

        For every n dist(x,y) =< dist(x,p[n]) + dist(p[n],y) (by DistTriangleIneq). 
        Take N3 such that N3 = max(N1,N2) + 1.
        Then N1 < N3 and N2 < N3.

        Hence dist(x,p[N3]) < halfeps and dist(p[N3],y) < halfeps (by DistSymm).
        Hence dist(x,p[N3]) + dist(p[N3],y) < halfeps + halfeps (by AddInvariance).
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



### Range

Definition Range. 
    Let a be a sequence. ran a = {a[n] | n is a natural number}. 

Definition FinRange.
    Let a be a sequence. a has finite range iff ran a is finite.

Definition InfinRange.
    Let a be a sequence. a has infinite range iff ran a is not finite.



### A convergent sequence is bounded

Definition BoundedBy.
    Let a be a sequence. Let K be a real number. a is bounded by K iff
    for every n abs(a[n]) =< K.

Definition BoundedSequence.
    Let a be a sequence. a is bounded iff there exists a real number K such that
    a is bounded by K.

Signature MaxAbsN.
    Let a be a sequence. Let N be a natural number. maxN(a,N) is a real number such that
    (there exists a natural number n such that n =< N and maxN(a,N) = abs(a[n])) and
    (for every natural number n such that n =< N abs(a[n]) =< maxN(a,N)).

Lemma ConvergentImpBounded.
    Let a be a sequence. Assume that a converges. Then a is bounded.
Proof.
    Take a real number x such that a converges to x.
    Take N such that for every n such that N < n dist(a[n],x) < 1 (by Convergence, OnePos).

    #Define b[k] = abs(a[k]) for k in NAT.
    Take a real number K such that K = max(abs(x) + 1, maxN(a,N)).

    Let us show that a is bounded by K.
        Let n be a natural number.
        Case n =< N.
            We have abs(a[n]) =< maxN(a,N) (by MaxAbsN).
            We have maxN(a,N) =< K.
            Therefore abs(a[n]) =< K (by LeqTransitivity).
            end.
        Case n > N.
            We have dist(a[n],x) < 1.
            We have abs(x) + 1 =< K.

            abs(a[n]) .= abs(a[n] + 0) (by Zero)
                      .= abs(a[n] + (x - x)) (by Neg)
                      .= abs(a[n] + ((-x) + x)) (by ComAdd)
                      .= abs((a[n] - x) + x) (by AssAdd).

            Hence abs(a[n]) =< abs(a[n] - x) + abs(x) (by AbsTriangleIneq).
            Hence abs(a[n]) =< dist(a[n],x) + abs(x).

            We have dist(a[n],x) + abs(x) < 1 + abs(x) (by MixedAddInvariance).
            Hence abs(a[n]) =< 1 + abs(x) (by MixedTransitivity).
            Therefore abs(a[n]) =< K.
        end.
    end.
qed.



### Sequence 1/n converges to 1

Lemma. 
    Let a be a sequence such that for every n such that n != 0 a[n] = inv(n).
    Then a converges to 0.
Proof.
    Assume eps is a positive real number. 
    Take N such that 1 < N * eps (by ArchimedeanAxiom, OnePos).

    Let us show that for every n such that N < n dist(a[n],0) < eps.
        Assume N < n. Then n != 0.
        Let us show that inv(n) < eps.
            We have N * eps < n * eps (by ComMult, MultInvariance).
            Hence 1 < n * eps (by TransitivityOfOrder).
            Therefore inv(n) * 1 < inv(n) * (n * eps).
            We have inv(n) * 1 = inv(n).
            inv(n) * (n * eps) .= (inv(n) * n) * eps (by AssMult)
                               .= 1 * eps (by InvDummy)
                               .= eps (by OneDummy).
        end.
    end.
qed.



### Neighborhood

Definition Neighb.
    Let eps be a positive real number. Let x be a real number.
    Neighb(x,eps) = {y| y is a real number such that dist(x,y) < eps}.

Definition LimitPointOfSet.
    Let E be a set. Assume that every element of E is a real number. A limit point of E
    is a real number x such that for every positive real number eps there exists an element
    q of E such that q is an element of Neighb(x,eps) and q != x.

#Definition BlobSet.
#    Let a be a sequence. Let x be a real number. Let eps be a positive real number.
#    Blob(x,eps) = { n | a[n] does not belong to Neighb(x,eps)}.


#Lemma ConvNeighborhood.
#(a converges to x) iff for every positive real number eps Blob(x,eps) is a finite set.
#Proof.



### Sum and Product of Sequences

Definition SequenceSum.
    Let a,b be sequences. a +' b is a sequence such that for every n (a +' b)[n] = a[n] + b[n].

Definition SequenceProd.
    Let a,b be sequences. a *' b is a sequence such that for every n (a *' b)[n] = a[n] * b[n].

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
    Let ca be a sequence such that for every n ca[n] = c + a[n].
    Then ca converges to c + x.
Proof.
    # Define cn[n] = c for n in NAT.
    # b is a sequence.
    [prove off]Take a sequence cn such that for every n cn[n] = c.[prove on]

    Let us show that ca = (cn +' a).
        Let us show that for every n ca[n] = (cn +' a)[n].
            Let n be a natural number.
            ca[n] .= c + a[n]
                  .= cn[n] + a[n]
                  .= (cn +' a)[n].
        end.
    end.

    cn converges to c (by ConstConv).
    Then ca converges to c + x (by SumConv).
qed.

Lemma ProdConstConv.
    Let a be a sequence. Let x,c be real numbers. Assume a converges to x.
    Let ca be a sequence such that for every natural number n ca[n] = c * a[n].
    Then ca converges to c * x.
Proof.
    Case c = 0.
        We have c * x = 0.
        Let us show that for every n ca[n] = 0. 
            ca[n] .= c * a[n]
                  .= 0 * a[n]
                  .= 0 (by ZeroMult).
        end.
        Hence ca converges to c * x (by ConstConv).
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
[exit]

#[prove off]
Lemma MinusRule5.
    Let a,b be real numbers. 
    Then (a * (-b)) = -(a * b) and ((-a) * b) = -(a * b).
Proof.
    a * (-b) = a * ((-1)*b) (by MinusRule4).
    a * ((-1) * b) = (a * (-1)) * b (by AssMult).
    (a * (-1)) * b = ((-1) * a) * b (by ComMult).
    ((-1) * a) * b = (-1) * (a * b) (by AssMult).
    (-1) * (a * b) = -(a * b).
    Hence (a * (-b)) = -(a * b).

    ((-a) * b) = (b * (-a)) (by ComMult).
    (b * (-a)) = -(b * a).
    -(b * a) = -(a * b) (by ComMult).
qed.

Lemma MinusRule6.
    Let a,b be real numbers. 
    Then ((-a) * (-b)) = a * b.
Proof.
    ((-a) * (-b)) = -(a * (-b)) (by MinusRule5).
    -(a * (-b)) = -(-(a * b)) (by MinusRule5).
    -(-(a * b)) = a * b (by MinusRule2).
qed.

Lemma SwapRuleLeq.
    Let a,b be real numbers. Assume not(a < b). Then a >= b.




Lemma Binomi1.
    Let a,b,c,d be real numbers.
    Then (a + b) * (c + d) = ((a * c) + (b * c)) + ((a * d) + (b * d)) .
Proof.
    (a + b) * (c + d) = ((a + b) * c) + ((a + b) * d) (by Distrib).
    ((a + b) * c) + ((a + b) * d) = ((a * c) + (b * c)) + ((a * d) + (b * d)) (by DistribDummy).
qed.

Lemma Binomi2.
    Let a,b,c,d be real numbers.
    Then (a - b) * (c - d) = ((a * c) - (b * c)) + (-(a * d) + (b * d)).
Proof.
    (a - b) * (c - d) = (a + (-b)) * (c + (-d)).
    (a + (-b)) * (c + (-d)) = ((a * c) + ((-b) * c)) + ((a * (-d)) + ((-b) * (-d))) (by Binomi1).
    ((a * c) + ((-b) * c)) + ((a * (-d)) + ((-b) * (-d))) = ((a * c) - (b * c)) + (-(a * d) + (b * d)) (by MinusRule5, MinusRule6).
qed.

Lemma Identity1.
    Let a,b,c,d be real numbers. 
    Then (a*b) - (c*d) = ((a - c) * (b - d)) + ((c * (b - d)) + (d * (a - c))).
Proof.
    ((a - c)*(b - d)) + ((c*(b - d)) + (d*(a - c))) = (((a*b) - (c*b)) + (-(a*d) + (c*d))) + ((c*(b - d)) + (d*(a - c))) (by Binomi2).
    (((a*b) - (c*b)) + (-(a*d) + (c*d))) + ((c*(b - d)) + (d*(a - c))) = (((a*b) - (c*b)) + (-(a*d) + (c*d))) + ((c*(b + (-d))) + (d*(a + (-c)))).
    (((a*b) - (c*b)) + (-(a*d) + (c*d))) + ((c*(b + (-d))) + (d*(a + (-c)))) = (((a*b) - (c*b)) + (-(a*d) + (c*d))) + (((c*b) + (c*(-d))) + ((d*a) + (d*(-c)))) (by Distrib).
    (((a*b) - (c*b)) + (-(a*d) + (c*d))) + (((c*b) + (c*(-d))) + ((d*a) + (d*(-c)))) = (((a*b) - (c*b)) + (-(a*d) + (c*d))) + (((c*b) + (-(c*d))) + ((d*a) + (-(d*c)))) (by MinusRule5).
    (((a*b) - (c*b)) + (-(a*d) + (c*d))) + (((c*b) + (-(c*d))) + ((d*a) + (-(d*c)))) = ((c*b) + (-(c*d))) + ((((a*b) - (c*b)) + (-(a*d) + (c*d))) + ((d*a) + (-(d*c)))) (by BubbleAdd).
    ((c*b) + (-(c*d))) + ((((a*b) - (c*b)) + (-(a*d) + (c*d))) + ((d*a) + (-(d*c)))) = ((c*b) + (-(c*d))) + (((a*b) - (c*b)) + ((-(a*d) + (c*d)) + ((a*d) + (-(c*d))))) (by AssAdd, ComMult).
    ((c*b) + (-(c*d))) + (((a*b) - (c*b)) + ((-(a*d) + (c*d)) + ((a*d) + (-(c*d))))) = ((c*b) + (-(c*d))) + (((a*b) - (c*b)) + ((-(a*d) + (c*d)) -(-((a*d) + (-(c*d)))))) (by MinusRule2). 
    ((c*b) + (-(c*d))) + (((a*b) - (c*b)) + ((-(a*d) + (c*d)) - (-(a*d) + (c*d))))  = ((c*b) + (-(c*d))) + (((a*b) - (c*b)) + 0) (by Neg).
    ((c*b) + (-(c*d))) + (((a*b) - (c*b)) + 0) = ((-(c*d)) + (c*b)) + (-(c*b) + (a*b)) (by ComAdd).
    ((-(c*d)) + (c*b)) + (-(c*b) + (a*b)) = (-(c*d)) + ((c*b) + (-(c*b) + (a*b))) (by AssAdd).
    (-(c*d)) + ((c*b) + (-(c*b) + (a*b))) = (-(c*d)) + (((c*b) -(c*b)) + (a*b)) (by AssAdd).
    (-(c*d)) + (((c*b) -(c*b)) + (a*b)) = (-(c*d)) + (0 + (a*b)) (by Neg).
    (-(c*d)) + (0 + (a*b)) = -(c*d) + (a*b).
    -(c*d) + (a*b) = (a*b) - (c*d) (by ComAdd).
qed.
#[prove on]


[prove off]
Lemma ProdConv.
    Let s,t be sequences. Let x,y be real numbers. Assume s converges to x and t converges to y.
    Let s *' t be a sequence such that for every natural number n (s *' t)[n] = s[n]*t[n].
    Then s *' t converges to x * y.
#Proof.
#Strategie: zerteile (s[n]*t[n]) - (x*y) = ((s[n] - x)*(t[n] - y)) + ((x*(t[n] - y)) + (y*(s[n] - x))) in Teilfolgen und zeige erst die Konvergenz der Teile um daraus die Konvergenz des Ganzen zu folgern.
#    Let a be a sequence such that for every natural number n a[n] = (s[n]-x)*(t[n]-y).
#    Let us show that a converges to 0.
#    proof.
#        Assume eps is a positive real number. 
#        Take a positive real number Eps such that Eps = sqrt(eps) (by Sqrt).
#        Take a natural number N1 such that for every natural number n such that N1 < n dist(s[n],x) < Eps (by Convergence).
#        Take a natural number N2 such that for every natural number n such that N2 < n dist(t[n],y) < Eps (by Convergence).
#        Take a natural number N such that N = max(N1,N2).
#        Assume n is a natural number such that N < n.
#        dist(a[n],0) < eps.
#        Proof.
#            Then dist(s[n],x) < Eps and dist(t[n],y) < Eps.
#            dist(s[n],x), dist(t[n],y) and Eps are nonnegative.
#            Then dist(s[n],x)*dist(t[n],y) < eps (by NonNegMultInvariance, Wurz).
#            Hence abs(s[n]-x)*abs(t[n]-y) < eps.
#            Hence abs((s[n]-x)*(t[n]-y)) < eps (by AbsMult).
#            Hence abs(((s[n]-x)*(t[n]-y)) - 0) < eps (by Zero, NegOfZero).
#        qed.
#        Hence a converges to 0.
#    qed.
#    Let b be a sequence such that for every natural number n b[n] = (x*(t[n] - y)) + (y*(s[n] - x)).
#    Let us show that b converges to 0.
#    proof.
#        Let bs and bt be sequences such that for every natural number n bt[n] = x*(t[n] + (-y)) and bs[n] = y*(s[n] + (-x)).
#        bt converges to 0 and bs converges to 0 (by SumConv, ProdConstConv). 
#        We have b = bt +' bs.
#        Hence b converges to 0 (by SumConv).
#    qed.
#    Let c be a sequence such that for every natural number n c[n] = (s[n]*t[n]) - (x*y).
#    Let us show that c converges to 0.
#    proof.
#        Assume eps is a positive real number.
#        Take a positive real number Eps such that Eps = eps * inv(2).
#        Take a natural number N such that for every natural number n such that N < n a[n] < Eps (by Convergence).
#        Assume n is a natural number such that N < n.
#        We have (s[n]*t[n]) - (x*y) = ((s[n] - x)*(t[n] - y)) + ((x*(t[n] - y)) + (y*(s[n] - x))) (by Identity1).
#        Hence we have c = a +' b.
#        Therefore c converges to 0 (by SumConv).
#    qed. 
#    Hence s *' t converges to x*y.
#qed.
[prove on]



### Subsequences

Definition IndexSeq.
A index sequence is a sequence i such that (for every natural number n i[n] is a natural number) and (for every natural number n i[n] < i[n+1]).

Definition SubSeq.
Let a be a sequence and i be a index sequence. Subseq(a,i) is a sequence such that for every natural number n Subseq(a,i)[n] = a[i[n]].

# Mit Topologie Gruppe absprechen? (Closed/Compact)

### Cauchy

Definition Cauchy.
A cauchy sequence is a sequence a such that for every positive real number eps there exists a natural number N such that
for every natural numbers n,m such that N < n and N < m dist(a[n],a[m]) < eps.

Axiom CauchyInR.
Let a be a sequence. a is a cauchy sequence iff a is convergent.


### Monotonic Sequences

Definition MonInc.
Let a be a sequence. a is monotonically increasing iff (for every natural number n a[n] =< a[n+1]).

Definition MonDec.
Let a be a sequence. a is monotonically decreasing iff (for every natural number n a[n] >= a[n+1]).

Definition Mon.
Let a be a sequence. a is monotonic iff a is monotonically increasing or a is monotonically decreasing.

Definition UpperBound. Let a be a bounded sequence. Let K be a real number. K is upper bound of a iff (for every natural number n a[n] =< K).

Definition LeastUpperBound. Let a be a bounded sequence. LeastUpper(a) is a real number K such that (K is upper bound of a) and (for every real number L such that L is upper bound of a K =< L).

Definition LowerBound. Let a be a bounded sequence. Let K be a real number. K is lower bound of a iff (for every natural number n a[n] >= K).

Definition GreatestLowerBound. Let a be a bounded sequence. GreatestLower(a) is a real number K such that (K is lower bound of a) and (for every real number L such that L is lower bound of a L =< K).

#[prove off]
Lemma MonCon.
Let a be a monotonic sequence. Then a converges iff a is bounded.
Proof.
    If a converges then a is bounded (by ConvergentImpBounded).
    Let us show that if a is bounded then a converges.
        Assume a is bounded.

        Case a is monotonically increasing.
            For every natural number n a[n] =< LeastUpper(a).
            Let us show that for every positive real number eps there exists a natural number n such that (LeastUpper(a) - eps) < a[n].
                Assume not (for every positive real number eps there exists a natural number n such that (LeastUpper(a) - eps) < a[n]).
                Take a positive real number eps such that for every natural number n not((LeastUpper(a) - eps) < a[n]).
                Hence for every natural number n a[n] =< (LeastUpper(a) - eps).
                Proof.
                    Let n be a natural number.
                    We have not((LeastUpper(a) - eps) < a[n]).
                    Therefore (LeastUpper(a) - eps) >= a[n] (by SwapRuleLeq).
                    Hence a[n] =< (LeastUpper(a) - eps).
                end.
                Hence (LeastUpper(a) - eps) is upper bound of a (by UpperBound).
                We have (LeastUpper(a) - eps) < LeastUpper(a).
                Contradiction.
            end.
        end.
        Case a is monotonically decreasing.

        end.
    end.
qed.
[prove on]

Definition PosInf.
Let a be a sequence. a converges to positive infinity iff for every real number K there exists a natural number N such that for every natural number n such that N < n a[n] >= K.

Definition NegInf.
Let a be a sequence. a converges to negative infinity iff for every real number K there exists a natural number N such that for every natural number n such that N < n a[n] =< K.

# Define limsup liminf?




