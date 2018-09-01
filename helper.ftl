[read Sequences/Naturals.ftl]

Let n,m denote natural numbers.
Let a,b,c,d denote real numbers.



Lemma MaxIneqDummy.
    Let a,b be real numbers. Then b =< max(a,b).



Lemma NotRuleOrder.
    a < b iff not(a >= b).

Lemma MixedAddInvariance.
    a < c /\ b =< d => a + b < c + d.



Lemma TwoHalf.
    (inv(2) * a) + (inv(2) * a) = a.



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



Signature Sqrt.
    Let x be a positive real number. sqrt(x) is a positive real number such that sqrt(x) * sqrt(x) = x.

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
