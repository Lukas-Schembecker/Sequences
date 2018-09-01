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

