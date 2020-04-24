Require Export Lra.
Require Export LUB_spec.
Require Export LaugwitzSchmieden.
Require Export w.
Require Export Numbers.
Require Export QArith.
Require Export QArith.Qabs.
Require Export Qring.
Require Export inverse_lemma.
Require Export Init.Nat.
Require Export definition.
Require Export Bridges_order2_LS.

Module mHRwElie(N:Num_w).


Import LSw.
Module Export HH := lub_spec(LSw).

Axiom wgt0 : forall n : nat, (0 < w n)%Z.
 
Lemma wge0 : forall n : nat, (0 <= w n)%Z.
Proof. intro. apply le_IZR. apply Rlt_le.
apply IZR_lt. apply wgt0. Qed. 
 

Definition equalQlim (q1 q2 : (nat -> Q)) : Prop := 
forall n : nat, exists M : nat, forall m : nat,  
(m > M)%nat ->  inject_Z (Z.of_nat n) * Qabs (q1 m + - q2 m)<= 1.

Definition equalw (a1 a2 : A) : Prop :=
forall n : nat, exists N : nat, forall m : nat, 
(m > N)%nat -> (Z.of_nat n * Z.abs (a1 m + - a2 m) <= w m)%Z.

Definition lew (a1 a2 : A) : Prop :=
forall n : nat, exists N : nat, forall m : nat,
(m > N)%nat -> (Z.of_nat n * (a1 m + - a2 m) <= w m)%Z.

Definition leQlim (q1 q2 : (nat -> Q)) : Prop :=
forall n : nat, exists M : nat, forall m : nat,  
(m > M)%nat ->  inject_Z (Z.of_nat n) *(q1 m + - q2 m)<= 1.

Definition pentiereQ (q : Q) : Z :=
match q with
| a # b => a / (Z.pos b)
end.

Definition resteentiereQ (q : Q) : Q :=
match q with
| a # b => inject_Z (a mod (Z.pos b)) / inject_Z (Z.pos b)
end.

Lemma pentiereQetreste : forall q : Q,
q == inject_Z (pentiereQ q) + resteentiereQ q.
Proof. intros q. destruct q. simpl. rewrite Qmake_Qdiv.
assert ((Qnum = (Z.pos Qden)*(Qnum/(Z.pos Qden)) + (Qnum mod (Z.pos Qden)))%Z).
apply Z_div_mod_eq. apply inversegtZ. apply Pos2Z.is_pos.
assert (inject_Z Qnum == inject_Z (Z.pos Qden * (Qnum / Z.pos Qden) + Qnum mod Z.pos Qden)).
rewrite <- H. reflexivity. clear H. rewrite H0. rewrite inject_Z_plus.
rewrite inject_Z_mult. assert (
(inject_Z (Z.pos Qden) * inject_Z (Qnum / Z.pos Qden) + inject_Z (Qnum mod Z.pos Qden)) / inject_Z (Z.pos Qden)
== inject_Z (Qnum / Z.pos Qden) + inject_Z (Qnum mod Z.pos Qden) / inject_Z (Z.pos Qden)). 
assert (forall q1 q2 : Q, q1 / q2 == q1 * / q2). intros. reflexivity.
assert (forall q1 q2 q3 : Q, ~ (q3 == 0) -> (q1 + q2) / q3 == q1 / q3 + q2 / q3). intros.
rewrite H. rewrite H. rewrite H. rewrite Qmult_plus_distr_l. reflexivity.
rewrite H1.
assert (inject_Z (Z.pos Qden) * inject_Z (Qnum / Z.pos Qden) / inject_Z (Z.pos Qden)
== inject_Z (Qnum / Z.pos Qden)). rewrite H. rewrite <- Qmult_comm. rewrite Qmult_assoc.
assert (/ inject_Z (Z.pos Qden) * inject_Z (Z.pos Qden)==1). rewrite <- Qmult_comm.
rewrite <- H. rewrite <- Qmult_1_l. assert (1 * (inject_Z (Z.pos Qden) / inject_Z (Z.pos Qden))
== 1 * inject_Z (Z.pos Qden) / inject_Z (Z.pos Qden)). rewrite Qmult_1_l. rewrite Qmult_1_l.
reflexivity. rewrite H2.
rewrite Qdiv_mult_l. reflexivity. apply Qnot_eq_sym. apply Qlt_not_eq. 
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. rewrite H2. rewrite Qmult_1_l.
reflexivity. rewrite H2. reflexivity. apply Qnot_eq_sym. apply Qlt_not_eq.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. rewrite H. reflexivity.
Qed.

Lemma resteentiereQineg : forall q : Q, (0 <= resteentiereQ q)%Q/\(resteentiereQ q < 1)%Q.
Proof. intros q. split. destruct q. simpl. 
assert (inject_Z (Qnum mod Z.pos Qden) / inject_Z (Z.pos Qden) ==
inject_Z (Qnum mod Z.pos Qden) * / inject_Z (Z.pos Qden)). reflexivity.
rewrite H. clear H. apply Qmult_le_0_compat. replace (0%Q) with
(inject_Z 0). rewrite <- Zle_Qle. apply Z.mod_pos_bound. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. apply Qinv_le_0_compat.
replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle. apply Pos2Z.is_nonneg.
unfold inject_Z. reflexivity. 
destruct q. simpl. assert (inject_Z (Qnum mod Z.pos Qden) / inject_Z (Z.pos Qden) ==
inject_Z (Qnum mod Z.pos Qden) * / inject_Z (Z.pos Qden)). reflexivity.
rewrite H. clear H. assert ((1 == inject_Z (Z.pos Qden) * / inject_Z (Z.pos Qden))%Q).
assert (inject_Z (Z.pos Qden) * / inject_Z (Z.pos Qden) ==
 1 * inject_Z (Z.pos Qden)  / inject_Z (Z.pos Qden)). rewrite Qmult_1_l.
reflexivity. rewrite H. clear H. rewrite Qdiv_mult_l. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with 
(inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos. unfold inject_Z.
reflexivity. rewrite H. apply Qmult_lt_compat_r. apply Qinv_lt_0_compat.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. rewrite <- Zlt_Qlt.
apply Z.mod_pos_bound. apply Pos2Z.is_pos.
Qed.


Definition phi := fun (x :A) => (fun (n : nat) => (inject_Z (x n) * ( / inject_Z (w n)))%Q).

Definition psi (x : (nat -> Q)) : A :=  (fun (n : nat) => pentiereQ ((inject_Z (w n)) * ( x n))       ).

Definition plusphi :=  fun ( x y : A) => (fun (n : nat) => ((inject_Z (x n) * ( / inject_Z (w n))) + 
(inject_Z (y n) * ( / inject_Z (w n))))%Q).

Lemma QabsZabs : forall z : Z, Qabs (inject_Z z) == inject_Z (Z.abs z).
Proof.
  intros z. rewrite <- Z.sgn_abs. 
  assert ((z < 0)%Z \/ (z = 0)%Z \/ (0 < z)%Z). apply Z.lt_trichotomy.
inversion H. rewrite Z.sgn_neg. rewrite Qabs_neg.
rewrite <- inject_Z_opp. apply inject_Z_injective. ring. 
replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle. 
apply le_IZR. apply Rlt_le. apply IZR_lt. assumption. unfold inject_Z.
reflexivity. assumption. inversion H0. 
rewrite H1. simpl. unfold inject_Z. reflexivity.
rewrite Z.sgn_pos. rewrite Qabs_pos. 
apply inject_Z_injective. ring. replace (0%Q) with (inject_Z 0).
rewrite <- Zle_Qle. apply le_IZR. apply Rlt_le. apply IZR_lt.
assumption. unfold inject_Z. reflexivity. assumption. Qed.




Lemma symmetryprod : forall q1 q2 q3 q4 : Q, (q1 * (q2 * (q3 * q4)) == q1 * q3 * q2 * q4)%Q.
Proof. intros q1 q2 q3 q4. ring. Qed. 

Lemma petit1 : forall x y : A, P x -> P y -> (equalw x y <-> equalQlim (phi x) (phi y)).
Proof. intros x y H1 H2. split. intros H3. unfold equalQlim.
unfold equalw in H3. inversion H1. clear H1.
inversion H2. clear H2.
intros p. assert (H4 : exists N : nat, forall m : nat, (m > N)%nat ->
 (Z.of_nat p * Z.abs (x m - y m) <= w m)%Z). apply H3. inversion H4. clear H3. clear H4.
split with x2. intros m P. unfold phi.
assert (P0 : inject_Z (Z.of_nat p) * Qabs (inject_Z (x m) * ( / inject_Z (w m))
 + - (inject_Z (y m) * ( / inject_Z (w m)))) ==
(inject_Z (Z.of_nat p)) * (/ inject_Z (w m))* Qabs (inject_Z (x m) + - inject_Z (y m))).
assert ( PP : Qabs (inject_Z (x m) * / inject_Z (w m) + - (inject_Z (y m) * / inject_Z (w m))) ==
/ inject_Z (w m) * Qabs (inject_Z (x m) + - inject_Z (y m))). 
assert (PPP : / inject_Z (w m) * Qabs (inject_Z (x m) + - inject_Z (y m)) ==
Qabs (/ inject_Z (w m)) * Qabs (inject_Z (x m) + - inject_Z (y m))).
assert (PPPP : Qabs (/ inject_Z (w m)) == / inject_Z (w m)).
rewrite Qabs_pos. reflexivity. apply Qinv_le_0_compat. replace (0%Q) with (inject_Z 0).
rewrite <- Zle_Qle. apply wge0. unfold inject_Z. reflexivity.
rewrite PPPP. reflexivity.
 rewrite PPP. rewrite <- Qabs_Qmult. apply Qabs_wd. ring.
rewrite PP. ring. rewrite P0.
assert (P1 :  1 == (inject_Z (w m) / inject_Z (w m))).
apply Qeq_sym. rewrite <- Qmult_1_l. assert (P2 :  (1 * (inject_Z (w m) / inject_Z (w m)) == 
1 * inject_Z (w m) / inject_Z (w m))%Q). rewrite Qmult_1_l. rewrite Qmult_1_l.
reflexivity. rewrite P2. rewrite Qdiv_mult_l. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
 rewrite P1. 
assert (P2 : inject_Z (Z.of_nat p) * / inject_Z (w m) * Qabs (inject_Z (x m) + - inject_Z (y m)) ==
inject_Z (Z.of_nat p)  * Qabs (inject_Z (x m) + - inject_Z (y m)) * (/ inject_Z (w m))).
assert (inject_Z (Z.of_nat p) * / inject_Z (w m) * Qabs (inject_Z (x m) + - inject_Z (y m)) ==
inject_Z (Z.of_nat p) * (/ inject_Z (w m) * Qabs (inject_Z (x m) + - inject_Z (y m)))). 
ring. rewrite H2.
assert (PPP : / inject_Z (w m) * Qabs (inject_Z (x m) + - inject_Z (y m)) ==
Qabs (/ inject_Z (w m)) * Qabs (inject_Z (x m) + - inject_Z (y m))). 
assert (PPPP : Qabs (/ inject_Z (w m)) == / inject_Z (w m)).
rewrite Qabs_pos. reflexivity. apply Qinv_le_0_compat. replace (0%Q) with (inject_Z 0).
rewrite <- Zle_Qle. apply wge0. unfold inject_Z. reflexivity.
rewrite PPPP. reflexivity.
rewrite PPP. 
assert (PPPP : Qabs (/ inject_Z (w m)) == / inject_Z (w m)).
rewrite Qabs_pos. reflexivity. apply Qinv_le_0_compat. replace (0%Q) with (inject_Z 0).
rewrite <- Zle_Qle. apply wge0. unfold inject_Z. reflexivity.
rewrite PPPP. ring. 
rewrite P2.
apply Qmult_le_compat_r. rewrite <- inject_Z_opp. rewrite <- inject_Z_plus.
rewrite QabsZabs. rewrite <- inject_Z_mult.
rewrite <- Zle_Qle. apply H1. assumption. 
apply Qinv_le_0_compat. replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle.
apply wge0. unfold inject_Z. reflexivity. 

intros H3. unfold equalw. intros n. unfold equalQlim in H3.
assert (exists M : nat, forall m : nat, (m > M)%nat -> inject_Z (Z.of_nat n) * Qabs (phi x m + - phi y m) <= 1).
apply H3. inversion H. split with x0. intros m O.  
unfold phi in H0. 
assert (forall m : nat, 
 inject_Z (Z.of_nat n) * Qabs (inject_Z (x m) * / inject_Z (w m) + - (inject_Z (y m) * / inject_Z (w m))) ==
 inject_Z (Z.of_nat n) * Qabs (  ( / inject_Z (w m)) *   (inject_Z (x m) + - inject_Z (y m)))).
intros m0. assert (or : {inject_Z (Z.of_nat n) == 0} + {~ inject_Z (Z.of_nat n) == 0}). 
apply Qeq_dec. inversion or.
rewrite H4. 
rewrite Qmult_0_l. rewrite Qmult_0_l. ring.
rewrite Qmult_inj_l. apply Qabs_wd. ring. assumption. 
assert (forall m : nat,
     (m > x0)%nat ->
     inject_Z (Z.of_nat n) * Qabs ( / inject_Z (w m) * (inject_Z (x m) + (- inject_Z (y m)))) <= 1).
intros m0 Q0. rewrite <- H4. apply H0. assumption.
clear H4. clear H0. 
assert (forall m : nat, inject_Z (Z.of_nat n) * Qabs ( / inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m))) ==
inject_Z (Z.of_nat n)  * (Qabs((inject_Z (x m) + - inject_Z (y m))) * ( / inject_Z (w m)))).
intros m0. assert (or : {inject_Z (Z.of_nat n) == 0} + {~ inject_Z (Z.of_nat n) == 0}). 
apply Qeq_dec. inversion or.
rewrite H0. 
rewrite Qmult_0_l. rewrite Qmult_0_l. ring.
rewrite Qmult_inj_l. rewrite Qabs_Qmult. rewrite Qabs_pos.
ring.  apply Qinv_le_0_compat. replace (0%Q) with (inject_Z 0).
rewrite <- Zle_Qle. apply wge0. unfold inject_Z. reflexivity. assumption.
assert (forall m : nat,
     (m > x0)%nat -> inject_Z (Z.of_nat n) * (Qabs (inject_Z (x m) + - inject_Z (y m)) * / inject_Z (w m)) <= 1).
intros m0 Q0. rewrite <- H0. apply H5. assumption. clear H0 H5.
assert (forall m0 : nat, 1 == inject_Z (w m0) * ( / inject_Z (w m0))).
intros m0. rewrite  Qmult_inv_r. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
assert (forall m : nat,
     (m > x0)%nat -> inject_Z (Z.of_nat n) * (Qabs (inject_Z (x m) + - inject_Z (y m)) * / inject_Z (w m)) <= 
inject_Z (w m) * / inject_Z (w m)).
intros m0 Q0. rewrite <- H0. apply H4. assumption. clear H0 H4.
assert (forall m : nat,
     (m > x0)%nat ->
     inject_Z (Z.of_nat n) * (Qabs (inject_Z (x m) + - inject_Z (y m))) <=
     inject_Z (w m)).
intros m0 Q0. apply Qmult_le_r with (/ inject_Z (w m0)).  
apply Qinv_lt_0_compat. replace (0%Q) with (inject_Z 0). 
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
rewrite <- Qmult_assoc. apply H5. assumption. clear H5.
assert (forall m : nat,
     (m > x0)%nat -> inject_Z (Z.of_nat n) * 
inject_Z (Z.abs (x m + - y m)) <= inject_Z (w m)).
intros m0 Q0. rewrite <- QabsZabs. rewrite inject_Z_plus. 
rewrite inject_Z_opp. apply H0. assumption. clear H0. rewrite Zle_Qle.
rewrite inject_Z_mult. apply H4. assumption.
Qed.



Lemma petit3 : forall x y : A, P x -> P y ->  equalQlim (phi (x + y)) (plusphi x y ).
Proof. intros x y H1 H2. unfold equalQlim. intros n.
unfold phi. unfold plusphi. exists 0%nat. intros m. intros H.
unfold plusA.  assert ((inject_Z (x m + y m) * / inject_Z (w m) +
   - (inject_Z (x m) * / inject_Z (w m) + inject_Z (y m) * / inject_Z (w m))) == 0).
rewrite inject_Z_plus. ring. 
 rewrite H0. unfold Qabs. simpl. rewrite Qmult_0_r.
replace (0%Q) with (inject_Z 0). replace (1%Q) with (inject_Z 1).
rewrite <- Zle_Qle. omega. unfold inject_Z. reflexivity. unfold inject_Z.
reflexivity. Qed.

Definition egal0  (a : A) : Prop := exists M : nat, forall n : nat, (n > M)%nat ->
(a n = 0)%Z.

Definition egal1  (a : A) : Prop := exists M : nat, forall n : nat, (n > M)%nat ->
(a n = 1)%Z.






Lemma petit51 : forall a1 a2 : A, egal0 a1 -> egal0 a2 -> 
equalQlim (phi a1) (fun n : nat => inject_Z (a2 n)).
Proof. intros a1 a2 H1 H2. unfold equalQlim. intros n. 
unfold phi.  inversion H1. inversion H2. clear H1 H2.
exists (Nat.max x0 x). intros m.
intros H1. rewrite H0. rewrite H. replace (inject_Z 0) with (0%Q).
rewrite Qmult_0_l. rewrite Qplus_opp_r. unfold Qabs. simpl.
rewrite Qmult_0_r. replace (0%Q) with (inject_Z 0).
replace (1%Q) with (inject_Z 1). rewrite <- Zle_Qle.
omega. unfold inject_Z. reflexivity. unfold inject_Z. reflexivity.
unfold inject_Z. reflexivity.
assert ( (x0 <= Nat.max x0 x)%nat). apply Nat.le_max_l.
assert ( (x <= Nat.max x0 x)%nat). apply Nat.le_max_r.
apply Nat2Z.inj_gt. apply inversegtZ. apply lt_IZR.
apply Rle_lt_trans with (IZR (Z.of_nat (Nat.max x0 x))). 
apply IZR_le. apply inj_le. assumption. apply IZR_lt.
apply inverseltZ. apply inj_gt. assumption. 
apply Nat2Z.inj_gt. apply inversegtZ. apply lt_IZR.
apply Rle_lt_trans with (IZR (Z.of_nat (Nat.max x0 x))). 
apply IZR_le. apply inj_le. apply Nat.le_max_l. apply IZR_lt.
apply inverseltZ. apply inj_gt. assumption. Qed. 





Lemma petit52 : forall a2 : A,  egal1 a2 -> 
equalQlim (phi w) (fun n : nat => inject_Z (a2 n)).

Proof. intros a1 H1 n. unfold equalQlim. 
unfold phi. inversion H1. clear H1.
exists x. intros m H1. rewrite H. 
rewrite Qmult_inv_r. unfold inject_Z. simpl. rewrite Qmult_0_r.
replace (0%Q) with (inject_Z 0). replace (1%Q) with (inject_Z 1).
rewrite <- Zle_Qle. omega. unfold inject_Z. reflexivity. unfold inject_Z.
reflexivity. apply Qnot_eq_sym. apply Qlt_not_eq.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply wgt0.
unfold inject_Z. reflexivity. assumption. Qed.



Lemma petit2 : forall x y : A, P x -> P y -> (lew x y <-> leQlim (phi x) (phi y)).
Proof. intros x y H1 H2. split. intros H3. unfold leQlim.
unfold lew in H3. inversion H1. clear H1.
inversion H2. clear H2.
intros p. assert (exists N : nat, forall m : nat, 
(m > N)%nat -> (Z.of_nat p * (x m + - y m) <= w m)%Z). apply H3. inversion H1. clear H3. clear H1.
split with x2. intros m P. unfold phi.
assert (P0 : inject_Z (Z.of_nat p) * (inject_Z (x m) * ( / inject_Z (w m))
 + - (inject_Z (y m) * ( / inject_Z (w m)))) ==
(inject_Z (Z.of_nat p)) * (/ inject_Z (w m))* (inject_Z (x m) + - inject_Z (y m))).
assert ( PP :  (inject_Z (x m) * / inject_Z (w m) + - (inject_Z (y m) * / inject_Z (w m))) ==
/ inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m))).  ring.
rewrite PP. ring. rewrite P0.
assert (P1 :  1 == (inject_Z (w m) / inject_Z (w m))).
apply Qeq_sym. rewrite <- Qmult_1_l. assert (P2 :  (1 * (inject_Z (w m) / inject_Z (w m)) == 
1 * inject_Z (w m) / inject_Z (w m))%Q). rewrite Qmult_1_l. rewrite Qmult_1_l.
reflexivity. rewrite P2. rewrite Qdiv_mult_l. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
 rewrite P1. 
assert (P2 : inject_Z (Z.of_nat p) * / inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m)) ==
inject_Z (Z.of_nat p)  * (inject_Z (x m) + - inject_Z (y m)) * (/ inject_Z (w m))).
assert (inject_Z (Z.of_nat p) * / inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m)) ==
inject_Z (Z.of_nat p) * (/ inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m)))). 
ring. rewrite H1. ring. rewrite P2.
apply Qmult_le_compat_r. rewrite <- inject_Z_opp. rewrite <- inject_Z_plus.
 rewrite <- inject_Z_mult.
rewrite <- Zle_Qle. apply H2. assumption. 
apply Qinv_le_0_compat. replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle.
apply wge0. unfold inject_Z. reflexivity.

intros H3. unfold lew. intros n. unfold leQlim in H3.
assert (exists M : nat, forall m : nat, (m > M)%nat -> inject_Z (Z.of_nat n) * (phi x m + - phi y m) <= 1).
apply H3. inversion H. split with x0. intros m O.  
unfold phi in H0. 
assert (forall m : nat, 
 inject_Z (Z.of_nat n) * (inject_Z (x m) * / inject_Z (w m) + - (inject_Z (y m) * / inject_Z (w m))) ==
 inject_Z (Z.of_nat n) * (  ( / inject_Z (w m)) *   (inject_Z (x m) + - inject_Z (y m)))).
intros m0. ring. 
assert (forall m : nat,
     (m > x0)%nat ->
     inject_Z (Z.of_nat n) * (/ inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m))) <= 1).
intros m0 Q0. rewrite <- H4. apply H0. assumption. clear H4 H0 H3.
assert (forall m0 : nat, 1 == inject_Z (w m0) * ( / inject_Z (w m0))).
intros m0. rewrite  Qmult_inv_r. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
assert (forall m : nat,
     (m > x0)%nat -> inject_Z (Z.of_nat n) * (/ inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m))) <=
 inject_Z (w m) * / inject_Z (w m)). intros m0 Q0. rewrite <- H0. apply H5.
assumption. clear H0 H5. assert (forall m : nat, 
inject_Z (Z.of_nat n) * (/ inject_Z (w m) * (inject_Z (x m) + - inject_Z (y m))) ==
(inject_Z (Z.of_nat n) * (inject_Z (x m) + - inject_Z (y m))) * / inject_Z (w m)). intros m0.
ring. assert (forall m : nat,
     (m > x0)%nat ->
     inject_Z (Z.of_nat n) * (inject_Z (x m) + - inject_Z (y m)) * / inject_Z (w m) <=
     inject_Z (w m) * / inject_Z (w m)). intros m0 Q0. rewrite <- H0. apply H3. assumption.
assert (forall m : nat,
     (m > x0)%nat ->
     inject_Z (Z.of_nat n) * ( (inject_Z (x m) + - inject_Z (y m))) <=
     inject_Z (w m)).
intros m0 Q0. apply Qmult_le_r with (/ inject_Z (w m0)).  
apply Qinv_lt_0_compat. replace (0%Q) with (inject_Z 0). 
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity. apply H4. assumption.
rewrite Zle_Qle. rewrite inject_Z_mult. rewrite inject_Z_plus. rewrite inject_Z_opp.
apply H5. assumption. Qed.

Definition multdansHRw (a1 a2 : A) : A := fun (n : nat) =>
 pentiereQ ( (inject_Z (a1 n) * inject_Z (a2 n) * (/inject_Z (w n)))%Q  ).

Definition suitex (m : nat) : A := fun (n : nat) => Z.of_nat m.

Lemma multdansA : forall x y : A, forall m : nat, (( multA x y m = x m * y m)%Z).
Proof. intros x y m. unfold multA. reflexivity. Qed.


Lemma a1equal1 : exists N : nat, forall n : nat, (n>N)%nat -> a1 n = 1%Z.
Proof. assert (forall x : A, 1 * x =A x). apply mult_neutral.
assert (1 * (suitex 2) =A (suitex 2) ). apply H.
unfold equalA in H0. inversion H0. exists x.
intros. assert ((1 * suitex 2) n = suitex 2 n). apply H1.
assumption. unfold suitex in H3. simpl in H3.
rewrite multdansA in H3. 
assert ((a1 n * 2)%Z = (1 * 2)%Z).
rewrite H3. ring. apply trivial_IZR.
apply Rmult_eq_reg_r with (IZR 2). rewrite <- mult_IZR.
rewrite H4. rewrite <- mult_IZR. reflexivity.
apply Rgt_not_eq. apply inversegtR. apply IZR_lt. omega.
Qed.

Lemma limsuitex  : forall n : nat,  lim (suitex n).
Proof. intros n. unfold suitex. induction n as [|n'].
- apply ANS4. exists a1. split. apply ANS1.
simpl. unfold absA. unfold leA. exists 0%nat. intros n H.
simpl. omega.
- assert ( (fun _ : nat => Z.of_nat (S n')) =A (fun _ : nat => Z.of_nat n') + a1).
unfold equalA. assert (exists N : nat, forall n : nat, (n>N)%nat -> a1 n = 1%Z).
apply a1equal1. inversion H. exists x. intros. unfold plusA.
rewrite H0. rewrite Nat2Z.inj_succ. ring. assumption.
rewrite H. apply ANS2a. assumption. apply ANS1.
Qed.


Lemma petit4 : forall x y : A, P x -> P y ->
 equalQlim (phi (multdansHRw x y )) (fun (n : nat) => ((phi x n)  * (phi y n))%Q  ).
Proof. intros. unfold equalQlim. intros n. unfold phi. unfold multdansHRw. inversion H.
assert (H9 : suitex n <A w). apply lim_lt_w. split. apply limsuitex. unfold leA. 
assert (Propo : forall x : A, 0 <=A (| x |)).
apply abs_pos. assert (propo2 :  0 <=A (| suitex n |)). apply Propo.
inversion propo2. exists x1. 
intros n0 P0. replace (suitex n n0) with ((| suitex n |) n0).
apply H2. assumption. unfold absA. rewrite Z.abs_eq. reflexivity.
unfold suitex. replace (0%Z) with (Z.of_nat 0). apply inj_le.
apply Peano.le_0_n. apply Nat2Z.inj_0.
unfold ltA in H9. inversion H9.
assert (H10 : forall n0 : nat, (n0 > x1)%nat -> (suitex n n0 < w n0)%Z).
assumption. clear H2. exists x1. intros m H2.
assert (forall q : Q, inject_Z (pentiereQ q) == q - resteentiereQ q). 
intros q.  apply Qplus_inj_r with (resteentiereQ q). rewrite <- pentiereQetreste.
ring. rewrite H3. assert (developpement : forall q1 q2 q3 : Q,
((q1 - q2) * q3 == q1 * q3 - q2 * q3)%Q). intros. ring. 
rewrite developpement. assert (forall q1 q2 q3 : Q, q1 - q2 + -q1 == -q2).
intros. ring. assert (forall q1 q2 q3 q4 : Q, q1 * q2 * q3 * q4 == q1 * q3 * q2 * q4).
intros. ring. rewrite H5. rewrite <- Qplus_comm. 
assert (forall q1 q2 q3 : Q, q1 + (q2 - q3) == q1 + q2 - q3). intros. ring.
rewrite H6. clear H4 H5 H6.
assert (- (inject_Z (x m) * / inject_Z (w m) * (inject_Z (y m) * / inject_Z (w m))) +
   inject_Z (x m) * / inject_Z (w m) * inject_Z (y m) * / inject_Z (w m) == 0 ).
ring. rewrite H4. assert (0 - resteentiereQ (inject_Z (x m) * inject_Z (y m) *
 / inject_Z (w m)) * / inject_Z (w m) ==
- resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)) * / inject_Z (w m)). ring.
rewrite H5. rewrite <- Qabs_opp.
assert (- (- resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)) * / inject_Z (w m)) ==
resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)) * / inject_Z (w m)).
ring. rewrite H6. clear H3 H4 H5 H6.
rewrite Qabs_Qmult. assert (Qabs (/ inject_Z (w m)) == / inject_Z (w m)).
rewrite Qabs_pos. reflexivity. apply Qinv_le_0_compat. replace (0%Q) with
(inject_Z 0). rewrite <- Zle_Qle. apply wge0. unfold inject_Z. reflexivity.
rewrite H3. clear H3. assert (1 == inject_Z (w m) * / inject_Z (w m)). 
rewrite  Qmult_inv_r. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
rewrite H3. assert (inject_Z (Z.of_nat n) *
(Qabs (resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m))) * / inject_Z (w m)) ==
inject_Z (Z.of_nat n) *
(Qabs (resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)))) * / inject_Z (w m)).
ring. rewrite H4. apply Qmult_le_compat_r. clear H4. 
assert ((0 <= resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)))%Q/\
(resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)) < 1)%Q).
apply resteentiereQineg. inversion H4. clear H4.
assert ( (n > 0)%nat \/ (0 = n)%nat). apply gt_0_eq. inversion H4.
rewrite Qabs_pos. 
assert ( inject_Z (Z.of_nat n) * resteentiereQ (inject_Z (x m) * inject_Z (y m) * / inject_Z (w m)) < 
1 * inject_Z (Z.of_nat n)). rewrite Qmult_comm. apply Qmult_lt_compat_r.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. replace (0%Z) with (Z.of_nat 0).
apply inverseltZ. apply inj_gt. assumption. unfold Z.of_nat. reflexivity.
unfold inject_Z. reflexivity. assumption. rewrite Qmult_1_l in H8.
apply Qle_trans with (inject_Z (Z.of_nat n)). apply Qlt_le_weak. assumption.
unfold suitex in H10. apply Qlt_le_weak. rewrite <- Zlt_Qlt. apply H10.
assumption. apply resteentiereQineg. rewrite <- H7.
unfold Z.of_nat. replace (inject_Z 0) with (0%Q). rewrite Qmult_0_l.
replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle. apply wge0.
unfold inject_Z. reflexivity. unfold inject_Z. reflexivity.
apply Qinv_le_0_compat. replace (0%Q) with
(inject_Z 0). rewrite <- Zle_Qle. apply wge0. unfold inject_Z. reflexivity.
Qed.

Lemma pentiereequal2 : forall z1 z3  : Z, forall z2 z4 : positive,
(IZR z1 * / IZR (Z.pos z2) = IZR z3 * / IZR (Z.pos z4))%R -> (z1 / (Z.pos z2) = z3 / (Z.pos z4))%Z.
Proof. intros. apply trivial_IZR. 
replace ((IZR z1 * / IZR (Z.pos z2))%R) with 
((IZR (z1 / Z.pos z2) + IZR (z1 mod (Z.pos z2)) * / IZR (Z.pos z2))%R) in H.
replace ((IZR z3 * / IZR (Z.pos z4))%R) with 
((IZR (z3 / Z.pos z4) + IZR (z3 mod (Z.pos z4)) * / IZR (Z.pos z4))%R) in H.
assert ((IZR (z1 / Z.pos z2) - IZR (z3 / Z.pos z4) = 
IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R).
apply Rplus_eq_reg_l with ((IZR (z3 / Z.pos z4))%R).
replace ((IZR (z3 / Z.pos z4) + 
(IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2)))%R) with
((IZR (z3 / Z.pos z4) + 
IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R).
rewrite <- H. ring. ring.
assert (( -1 < IZR (z1 / Z.pos z2) - IZR (z3 / Z.pos z4) < 1)%R).
rewrite H0. split. 
assert ((0 <= IZR (z3 mod Z.pos z4) < IZR (Z.pos z4))%R).
split. apply IZR_le. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
apply IZR_lt. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
assert ((0 <= IZR (z1 mod Z.pos z2) < IZR (Z.pos z2))%R).
split. apply IZR_le. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
apply IZR_lt. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
assert ((0 <= IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) < 1)%R).
split. replace (0%R) with ((0 * / IZR (Z.pos z4))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. 
apply IZR_lt. apply Pos2Z.is_pos. apply H1. ring.
replace (1%R) with ((IZR (Z.pos z4) * / IZR (Z.pos z4))%R).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply IZR_lt. apply Pos2Z.is_pos.
apply H1. rewrite Rinv_r. ring.
apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
assert ((0 <= IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2) < 1)%R).
split. replace (0%R) with ((0 * / IZR (Z.pos z2))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. 
apply IZR_lt. apply Pos2Z.is_pos. apply H2. ring.
replace (1%R) with ((IZR (Z.pos z2) * / IZR (Z.pos z2))%R).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply IZR_lt. apply Pos2Z.is_pos.
apply H2. rewrite Rinv_r. ring.
apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
clear H1 H2. 
assert ((-1 < - (IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2)) <= 0)%R).
split. apply Ropp_lt_contravar. apply H4. replace (0%R) with ((-0)%R).
apply Ropp_ge_le_contravar. apply inversegeR. apply H4. ring.
replace ((IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R)
with ((IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) + - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R).
replace ((-1)%R) with ((0 + (- 1))%R). apply Rplus_le_lt_compat.
apply H3. replace ((- IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R) with
((- (IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2)))%R). apply H1.
ring. ring. ring. 
assert ((0 <= IZR (z3 mod Z.pos z4) < IZR (Z.pos z4))%R).
split. apply IZR_le. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
apply IZR_lt. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
assert ((0 <= IZR (z1 mod Z.pos z2) < IZR (Z.pos z2))%R).
split. apply IZR_le. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
apply IZR_lt. apply Z_mod_lt. apply inversegtZ. apply Pos2Z.is_pos.
assert ((0 <= IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) < 1)%R).
split. replace (0%R) with ((0 * / IZR (Z.pos z4))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. 
apply IZR_lt. apply Pos2Z.is_pos. apply H1. ring.
replace (1%R) with ((IZR (Z.pos z4) * / IZR (Z.pos z4))%R).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply IZR_lt. apply Pos2Z.is_pos.
apply H1. rewrite Rinv_r. ring.
apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
assert ((0 <= IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2) < 1)%R).
split. replace (0%R) with ((0 * / IZR (Z.pos z2))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. 
apply IZR_lt. apply Pos2Z.is_pos. apply H2. ring.
replace (1%R) with ((IZR (Z.pos z2) * / IZR (Z.pos z2))%R).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply IZR_lt. apply Pos2Z.is_pos.
apply H2. rewrite Rinv_r. ring.
apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
clear H1 H2. 
assert ((-1 < - (IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2)) <= 0)%R).
split. apply Ropp_lt_contravar. apply H4. replace (0%R) with ((-0)%R).
apply Ropp_ge_le_contravar. apply inversegeR. apply H4. ring.
replace ((IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R)
with ((IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) + - IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R).
replace (1%R) with ((1 + 0)%R). apply Rplus_lt_le_compat.
apply H3. replace ((- IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2))%R) with
((- (IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2)))%R). apply H1.
ring. ring. ring. rewrite <- minus_IZR in H1. inversion H1.
assert ((IZR (z1 / Z.pos z2 + - (z3 / Z.pos z4)) <= 0)%R). 
apply Rplus_le_reg_r with (1%R). rewrite <- plus_IZR.
rewrite <- plus_IZR. apply IZR_le. apply inverseleZ.
apply ArithZ. apply inversegtZ. replace ((0 + 1)%Z) with (1%Z).
apply lt_IZR. assumption. ring.
assert ((0 <= IZR (z1 / Z.pos z2 + - (z3 / Z.pos z4)))%R). 
replace (0%R) with ((-1 + 1)%R). rewrite <- plus_IZR. apply IZR_le.
apply inverseleZ. apply ArithZ. apply inversegtZ. apply lt_IZR.
assumption. ring.
apply Rplus_eq_reg_r with ((-IZR (z3 / Z.pos z4))%R).
replace ((IZR (z3 / Z.pos z4) + - IZR (z3 / Z.pos z4))%R) with (0%R).
replace ((- IZR (z3 / Z.pos z4))%R) with ((IZR (-(z3 / Z.pos z4)))%R).
rewrite <- plus_IZR. replace ((IZR (z1 / Z.pos z2 + - (z3 / Z.pos z4)))%R)
with ((IZR (z1 / Z.pos z2  - z3 / Z.pos z4))%R). apply Rle_antisym.
 assumption. assumption. apply IZR_eq. ring.
replace ((- IZR (z3 / Z.pos z4))%R) with ((0 - IZR (z3 / Z.pos z4))%R).
rewrite <- minus_IZR. apply IZR_eq. ring. ring. ring.
apply Rmult_eq_reg_r with ((IZR (Z.pos z4))%R).
replace ((((IZR (z3 / Z.pos z4) + IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4)) * IZR (Z.pos z4))%R)) with
((IZR (z3 / Z.pos z4) * IZR (Z.pos z4) + IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) * IZR (Z.pos z4))%R).
replace ((IZR z3 */ IZR (Z.pos z4) * IZR (Z.pos z4))%R) with ((IZR z3)%R).
replace ((IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) * IZR (Z.pos z4))%R) with
((IZR (z3 mod Z.pos z4))%R). symmetry. rewrite Rmult_comm.
rewrite <- mult_IZR. rewrite <- plus_IZR. apply IZR_eq.
apply Z_div_mod_eq. apply inversegtZ. apply Pos2Z.is_pos.
replace ((IZR (z3 mod Z.pos z4) * / IZR (Z.pos z4) * IZR (Z.pos z4))%R) with
((IZR (z3 mod Z.pos z4) * (/ IZR (Z.pos z4) * IZR (Z.pos z4)))%R).
rewrite <- Rinv_l_sym. ring. apply Rgt_not_eq.
apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos. ring.
replace ((IZR z3 * / IZR (Z.pos z4) * IZR (Z.pos z4))%R) with
((IZR z3 * (/ IZR (Z.pos z4) * IZR (Z.pos z4)))%R). rewrite <- Rinv_l_sym.
ring. apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
ring. ring. apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
apply Rmult_eq_reg_r with ((IZR (Z.pos z2))%R).
replace ((((IZR (z1 / Z.pos z2) + IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2)) * IZR (Z.pos z2))%R)) with
((IZR (z1 / Z.pos z2) * IZR (Z.pos z2) + IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2) * IZR (Z.pos z2))%R).
replace ((IZR z1 */ IZR (Z.pos z2) * IZR (Z.pos z2))%R) with ((IZR z1)%R).
replace ((IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2) * IZR (Z.pos z2))%R) with
((IZR (z1 mod Z.pos z2))%R). symmetry. rewrite Rmult_comm.
rewrite <- mult_IZR. rewrite <- plus_IZR. apply IZR_eq.
apply Z_div_mod_eq. apply inversegtZ. apply Pos2Z.is_pos.
replace ((IZR (z1 mod Z.pos z2) * / IZR (Z.pos z2) * IZR (Z.pos z2))%R) with
((IZR (z1 mod Z.pos z2) * (/ IZR (Z.pos z2) * IZR (Z.pos z2)))%R).
rewrite <- Rinv_l_sym. ring. apply Rgt_not_eq.
apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos. ring.
replace ((IZR z1 * / IZR (Z.pos z2) * IZR (Z.pos z2))%R) with
((IZR z1 * (/ IZR (Z.pos z2) * IZR (Z.pos z2)))%R). rewrite <- Rinv_l_sym.
ring. apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
ring. ring. apply Rgt_not_eq. apply inversegtR. apply IZR_lt. apply Pos2Z.is_pos.
Qed.


Lemma pentiereequal : forall q1 q2 : Q, q1 == q2 -> (pentiereQ q1 = pentiereQ q2)%Z.
Proof. intros.  assert (Q : q1 == q2). assumption.  apply Qred_eq_iff in H.
destruct q1. destruct q2. unfold pentiereQ. apply pentiereequal2.
rewrite Qmake_Qdiv in Q. rewrite Qmake_Qdiv in Q. 
assert (inject_Z Qnum / inject_Z (Z.pos Qden) * inject_Z (Z.pos Qden)  
== inject_Z Qnum0 / inject_Z (Z.pos Qden0) * inject_Z (Z.pos Qden)).
apply Qmult_inj_r. apply Qnot_eq_sym. apply Qlt_not_eq.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. assumption. 
assert (inject_Z Qnum / inject_Z (Z.pos Qden) * inject_Z (Z.pos Qden) ==
inject_Z Qnum). 
rewrite H0. assert (Q1 : inject_Z (Z.pos Qden)  / inject_Z (Z.pos Qden)  == 1).
assert (Q2 : inject_Z (Z.pos Qden) / inject_Z (Z.pos Qden) ==
 1 * inject_Z (Z.pos Qden) / inject_Z (Z.pos Qden)). rewrite Qmult_1_l. ring.
rewrite Q2. rewrite Qdiv_mult_l. reflexivity. 
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply Pos2Z.is_pos. unfold inject_Z. reflexivity.
apply Qmult_inj_r with ( / inject_Z (Z.pos Qden)).
apply Qnot_eq_sym. apply Qlt_not_eq. apply Qinv_lt_0_compat. 
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. 
assert (Q2 : inject_Z Qnum0 / inject_Z (Z.pos Qden0) * inject_Z (Z.pos Qden) * / inject_Z (Z.pos Qden) ==
inject_Z Qnum0 / inject_Z (Z.pos Qden0) * (inject_Z (Z.pos Qden)  / inject_Z (Z.pos Qden))).
unfold Qdiv. ring. rewrite Q2. rewrite Q1. rewrite Q. ring.
 rewrite H1 in H0. clear H1.
assert (inject_Z Qnum * inject_Z (Z.pos Qden0) == 
inject_Z Qnum0 / inject_Z (Z.pos Qden0) * inject_Z (Z.pos Qden) * inject_Z (Z.pos Qden0)). 
apply Qmult_inj_r. apply Qnot_eq_sym. apply Qlt_not_eq.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply Pos2Z.is_pos.
unfold inject_Z. reflexivity. assumption.
assert (inject_Z Qnum0 / inject_Z (Z.pos Qden0) * inject_Z (Z.pos Qden) * inject_Z (Z.pos Qden0)
== inject_Z Qnum0 * inject_Z (Z.pos Qden)). 
assert (Q1 : inject_Z (Z.pos Qden0)  / inject_Z (Z.pos Qden0)  == 1).
assert (Q2 : inject_Z (Z.pos Qden0) / inject_Z (Z.pos Qden0) ==
 1 * inject_Z (Z.pos Qden0) / inject_Z (Z.pos Qden0)). rewrite Qmult_1_l. ring.
rewrite Q2. rewrite Qdiv_mult_l. reflexivity. 
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply Pos2Z.is_pos. unfold inject_Z. reflexivity.
assert (Q2 : inject_Z Qnum0 / inject_Z (Z.pos Qden0) * inject_Z (Z.pos Qden) * inject_Z (Z.pos Qden0) ==
inject_Z Qnum0 * inject_Z (Z.pos Qden) * (inject_Z (Z.pos Qden0) / inject_Z (Z.pos Qden0))).
unfold Qdiv. ring. rewrite Q2. rewrite Q1. ring.
rewrite H2 in H1. clear H2. rewrite <- inject_Z_mult in H1.
rewrite <- inject_Z_mult in H1.  assert ((Qnum * Z.pos Qden0 = Qnum0 * Z.pos Qden)%Z).
apply inject_Z_injective. assumption. clear H H1 H0.
apply Rmult_eq_reg_l with (IZR (Z.pos Qden)). 
replace ((IZR (Z.pos Qden) * (IZR Qnum * / IZR (Z.pos Qden)))%R) with 
(IZR Qnum). apply Rmult_eq_reg_l with (IZR (Z.pos Qden0)).
replace ((IZR (Z.pos Qden0) * (IZR (Z.pos Qden) * (IZR Qnum0 * / IZR (Z.pos Qden0))))%R)
with (((IZR (Z.pos Qden) * (IZR Qnum0)))%R).
rewrite <- mult_IZR. rewrite <- mult_IZR. apply IZR_eq.
replace ((Z.pos Qden0 * Qnum)%Z) with ((Qnum * Z.pos Qden0 )%Z). rewrite H2.
ring. ring. replace ((IZR (Z.pos Qden0) * 
(IZR (Z.pos Qden) * (IZR Qnum0 * / IZR (Z.pos Qden0))))%R) with
((IZR (Z.pos Qden0) *  / IZR (Z.pos Qden0) * (IZR (Z.pos Qden) * (IZR Qnum0 )))%R).
rewrite Rinv_r. ring. apply Rgt_not_eq. apply inversegtR. 
apply IZR_lt. apply inverseltZ. apply Zgt_pos_0. ring.
apply Rgt_not_eq. apply inversegtR. 
apply IZR_lt. apply inverseltZ. apply Zgt_pos_0. 
replace ((IZR (Z.pos Qden) * (IZR Qnum * / IZR (Z.pos Qden)))%R) with
((IZR (Z.pos Qden) * / IZR (Z.pos Qden) * (IZR Qnum ))%R). rewrite Rinv_r.
ring.  apply Rgt_not_eq. apply inversegtR. 
apply IZR_lt. apply inverseltZ. apply Zgt_pos_0. 
ring. apply Rgt_not_eq. apply inversegtR. 
apply IZR_lt. apply inverseltZ. apply Zgt_pos_0. 
Qed.



Lemma petit61 : forall x : A, equalw (psi (phi x)) x.
Proof. intros x. unfold equalw. 
intros n. unfold psi. unfold phi.
exists 0%nat. intros. 
assert ( inject_Z (w m) * (inject_Z (x m) * / inject_Z (w m)) == inject_Z (x m)).
assert (inject_Z (x m) * / inject_Z (w m) == inject_Z (x m)  / inject_Z (w m)).
unfold Qdiv. reflexivity. rewrite H0. rewrite Qmult_div_r. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
assert ( pentiereQ (inject_Z (w m) * (inject_Z (x m) * / inject_Z (w m))) =
 pentiereQ (inject_Z (x m))).
apply pentiereequal. apply H0.
rewrite H1.
assert (forall z : Z, pentiereQ (inject_Z z) = z).
intros. destruct (inject_Z). simpl. apply Z.div_1_r.
rewrite H2. replace ((x m + - x m)%Z) with (0%Z). 
rewrite Z.abs_0. rewrite Z.mul_0_r. apply wge0. ring.
Qed.









Lemma petit62 : forall u : (nat -> Q), equalQlim (phi (psi u)) u.
Proof. intros u. unfold equalQlim. intros n. 
assert (H9 : suitex n <A w). apply lim_lt_w. split. apply limsuitex. unfold leA. 
assert (Propo : forall x : A, 0 <=A (| x |)).
apply abs_pos. assert (propo2 :  0 <=A (| suitex n |)). apply Propo.
inversion propo2. exists x. 
intros n0 P0. replace (suitex n n0) with ((| suitex n |) n0).
apply H. assumption. unfold absA. rewrite Z.abs_eq. reflexivity.
unfold suitex. replace (0%Z) with (Z.of_nat 0). apply inj_le.
apply Peano.le_0_n. apply Nat2Z.inj_0.
unfold ltA in H9. inversion H9.
assert (H10 : forall n0 : nat, (n0 > x)%nat -> (suitex n n0 < w n0)%Z).
assumption. clear H.
unfold phi. unfold psi. exists x. intros m H.
assert (inject_Z (pentiereQ (inject_Z (w m) * u m)) == (inject_Z (w m) * u m) - 
resteentiereQ (inject_Z (w m) * u m) ). apply Qplus_inj_r with 
(resteentiereQ (inject_Z (w m) * u m)). rewrite <- pentiereQetreste. ring.
rewrite H0. rewrite Qabs_neg. 
assert ( (inject_Z (w m) * u m - resteentiereQ (inject_Z (w m) * u m)) * / inject_Z (w m) ==
(inject_Z (w m) * u m * / inject_Z (w m) - resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m))  ).
ring. rewrite H1. clear H1. assert ( inject_Z (w m) * u m * / inject_Z (w m) ==
u m * inject_Z (w m) * / inject_Z (w m)). ring. rewrite H1.
assert ( u m * inject_Z (w m) * / inject_Z (w m) == u m * 1 * inject_Z (w m) / inject_Z (w m) ).
unfold Qdiv. ring. rewrite H2. rewrite Qdiv_mult_l. rewrite Qmult_1_r.
assert (u m - resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m) + - u m ==
 - resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m)). ring.
rewrite H3. assert ( inject_Z (Z.of_nat n) *
 - (- resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m)) ==
inject_Z (Z.of_nat n) *  (resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m))).
ring. rewrite H4. rewrite Qmult_assoc. 
assert (1 == 1 * inject_Z (w m)  / inject_Z (w m)). rewrite Qdiv_mult_l.
reflexivity. apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with
(inject_Z 0). rewrite <- Zlt_Qlt. apply wgt0. unfold inject_Z. reflexivity.
rewrite H5. rewrite Qmult_1_l. assert (inject_Z (w m) / inject_Z (w m) ==
inject_Z (w m) * / inject_Z (w m)). unfold Qdiv. reflexivity. rewrite H6.
clear H4 H5 H6 H3 H2 H1 H0. apply Qmult_le_compat_r. 
apply Qle_trans with (inject_Z (Z.of_nat n)). 
assert (inject_Z (Z.of_nat n) == inject_Z (Z.of_nat n) * 1). ring.
rewrite H0. assert (inject_Z (Z.of_nat n) * 1 * resteentiereQ (inject_Z (w m) * u m)
== inject_Z (Z.of_nat n) * resteentiereQ (inject_Z (w m) * u m)). ring.
rewrite H1. clear H0 H1.
assert ( (n > 0)%nat \/ (0 = n)%nat). apply gt_0_eq. inversion H0.
 apply Qmult_le_l. 
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. 
apply inverseltZ. rewrite <- Nat2Z.inj_0. apply inj_gt. assumption.
unfold inject_Z. reflexivity. apply Qlt_le_weak. apply resteentiereQineg.
rewrite <- H1. rewrite Nat2Z.inj_0. unfold inject_Z.
rewrite Qmult_0_l. rewrite Qmult_0_l. apply Qle_refl.
rewrite <- Zle_Qle. apply le_IZR. apply Rlt_le. apply IZR_lt.
unfold suitex in H10. apply H10. assumption. apply Qinv_le_0_compat.
replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle. apply wge0.
unfold inject_Z. reflexivity. apply Qnot_eq_sym. apply Qlt_not_eq.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply wgt0.
unfold inject_Z. reflexivity. assert (
(inject_Z (w m) * u m - resteentiereQ (inject_Z (w m) * u m)) * / inject_Z (w m) ==
(inject_Z (w m) * u m) * / inject_Z (w m) - resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m)).
ring. rewrite H1. clear H1. assert (inject_Z (w m) * u m * / inject_Z (w m) == u m).
assert (inject_Z (w m) * u m * / inject_Z (w m) == inject_Z (w m) * / inject_Z (w m) * u m).
ring. rewrite H1. rewrite Qmult_inv_r. ring. apply Qnot_eq_sym. apply Qlt_not_eq.
replace (0%Q) with (inject_Z 0). rewrite <- Zlt_Qlt. apply wgt0.
unfold inject_Z. reflexivity. rewrite H1.
assert (u m - resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m) + - u m ==
- resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m)). ring.
rewrite H2. clear H0 H1 H2. assert (zeroP : 0 == -0). ring. rewrite zeroP. assert (
- resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m) ==
- (resteentiereQ (inject_Z (w m) * u m) * / inject_Z (w m))). ring.
rewrite H0. clear H0. apply Qopp_le_compat. apply Qmult_le_0_compat.
apply resteentiereQineg. apply Qinv_le_0_compat.
replace (0%Q) with (inject_Z 0). rewrite <- Zle_Qle. apply wge0.
unfold inject_Z. reflexivity. Qed.











Definition wBn :A := fun (n:nat) => Z.pow (Z.of_nat B) (Z.of_nat n).

Definition PwBn := fun (x:A) => exists n:A, (lim n /\ 0 <A n /\  absA x <=A n*wBn).


Definition encadrement_nat (xc : Reelc) : Prop := exists x : R, forall n : Z, (0<=n)%Z -> 
(IZR (xc  n) - 1 < x * B_powerRZ  n < IZR (xc n) + 1)%R. 

Definition Reelc_to_A (xc : Reelc) : A := fun n : nat => xc (Z.of_nat n). 

Definition congruentwBn (x y : A) : Prop := 
forall r:Z, (0<r)%Z ->  exists N:nat, forall k :nat, (k>=N)%nat -> forall l:nat, (l>=N)%nat -> 
(r * (Z.abs (((x k) - (y k)) * (wBn l) - (((x l) - (y l)) * (wBn k)))) <= (wBn k) * (wBn l))%Z.

Definition regularwBn (x:A) : Prop := congruentwBn x a0.


Definition pentiereR (r:R) := Z.to_nat (Int_part r).


Lemma INR_IZR : forall x, (x>=0)%Z -> INR (Z.to_nat x) = IZR x.
Proof.
intros.
induction x.
reflexivity.
rewrite INR_IZR_INZ.
rewrite Z2Nat.id.
reflexivity.
omega.
generalize (Pos2Z.neg_is_neg p); intros; omega.
Qed.

Lemma Int_part_0 : forall r, (r >= 0)%R -> (Int_part r >=0)%Z.
Proof.
intros.
assert (-1 < Int_part r)%Z; auto with zarith.
apply lt_IZR; simpl.
apply Rlt_le_trans with (IZR (Int_part r) - r)%R.
eapply base_Int_part.
apply Rle_trans with (IZR (Int_part r) - 0)%R; [idtac|right; ring].
unfold Rminus; apply Rplus_le_compat_l; auto with real.
Qed.

Lemma pentiereRencadrement : forall r : R, (r>=0)%R -> 
(INR (pentiereR r) <= r < INR (pentiereR r + 1))%R.
Proof.
  unfold pentiereR.
  intros r Hr.
  destruct (base_Int_part r).
  split.
  rewrite INR_IZR.
  assumption.
apply Int_part_0; assumption.
rewrite plus_INR.
rewrite INR_IZR.
apply Rgt_lt in H0.
rewrite Rplus_comm.
unfold INR.
apply (Rplus_lt_reg_r (- r)).
ring_simplify.
apply (Rplus_lt_reg_r (-1)).
ring_simplify.
rewrite Rplus_comm.
unfold Rminus in *.
assumption.
apply Int_part_0; assumption.
Qed.


Lemma pentiereRgt : forall r : R, (r < INR (pentiereR r + 1))%R.
Proof. intros. unfold pentiereR. unfold Int_part. 
 assert (H :  {(r >= 0)%R} + {(0 > r)%R}).
apply Rge_gt_dec. inversion H. apply pentiereRencadrement. assumption.
rewrite plus_INR.  
apply Rlt_le_trans with (0%R). apply inverseltR. assumption.
assert ((up r <= 0)%Z). 
assert ((IZR (up r) - r <= 1)%R). apply archimed.
assert ((IZR (up r) < 1)%R). (* on le déduit de H0 et H1 *)
apply Rplus_lt_reg_r with ((-r)%R).
apply Rle_lt_trans with (1%R). assumption.
replace (1%R) with (1 + - 0)%R.
replace ((1 + - 0 + - r)%R) with (1 + - r)%R. apply inverseltR.
apply Rplus_gt_compat_l. apply Ropp_lt_gt_contravar. 
apply inverseltR. assumption. ring. ring.
apply inverseleZ. replace ((up r)%Z) with (((up r - 1) + 1)%Z).
apply ArithZ. apply inversegtZ. apply lt_IZR. rewrite minus_IZR. 
replace ((IZR (up r) - 1)%R) with ((IZR (up r) + (- 1))%R).
replace (0%R) with ((1 + (-1))%R). apply Rplus_lt_compat_r. assumption.
ring. ring. ring.
destruct up. simpl. lra. 
assert ( (Z.pos p <= 0)%Z <-> False).
apply neg_false. apply Zgt_not_le. apply inversegtZ. apply Pos2Z.is_pos.
assert (False). rewrite <- H2. assumption. inversion H3. 
replace ((Z.neg p - 1)%Z) with ((Z.neg p + Z.neg 1)%Z).
rewrite Pos2Z.add_neg_neg. simpl. lra.
ring.
Qed.




Lemma Hrw_Vmm : forall xc : Reelc, encadrement_nat xc -> (PwBn (Reelc_to_A xc))/\(regularwBn (Reelc_to_A xc)).
Proof. intros. split. unfold PwBn. unfold encadrement_nat in H. 
inversion H. clear H. 
assert ( 0 + (suitex 1) =A suitex 1). apply Radd_0_l.
unfold equalA in H. inversion H. clear H.
assert (forall m : nat, (m > x0)%nat -> 0 m = 0%Z).
intros. apply eq_IZR. apply Rplus_eq_reg_r with (IZR (suitex 1 m)).
rewrite <- plus_IZR. rewrite <- plus_IZR. apply IZR_eq. unfold plusA.
apply eq_IZR. rewrite plus_IZR. rewrite Rplus_0_l. apply IZR_eq.
apply H1. assumption.
exists (suitex (Nat.max (pentiereR x + 2) (pentiereR (-x) + 2))).
split. apply limsuitex. split. unfold ltA.
exists x0. intros. clear H1. rewrite H. unfold suitex.
replace (0%Z) with (Z.of_nat 0). apply inj_lt.
replace ((pentiereR x + 1)%nat) with ((S (pentiereR x))%nat).
replace ((pentiereR x + 2)%nat) with ((S (S (pentiereR x)))%nat).
apply INR_lt. apply Rlt_le_trans with (INR (S(S(pentiereR x)))). 
apply lt_INR. apply Nat.lt_0_succ. apply NleR.
apply Nat.le_max_l. ring. ring. apply Nat2Z.inj_0. assumption.
unfold leA. unfold absA. exists 0%nat. intros.
assert (Z.abs (Reelc_to_A xc n) = Reelc_to_A xc n \/ Z.abs (Reelc_to_A xc n) = (- (Reelc_to_A xc n))%Z). 
apply Z.abs_eq_or_opp. inversion H3. rewrite H4.
unfold multA. unfold suitex. unfold wBn.
unfold Reelc_to_A. apply le_IZR. rewrite mult_IZR. rewrite <- B_powerRZandZofnat.
apply Rle_trans with ((x * B_powerRZ (Z.of_nat n) + 1)%R). apply Rlt_le.
replace ((IZR (xc (Z.of_nat n)))%R) with ((IZR (xc (Z.of_nat n)) - 1 + 1)%R).
apply Rplus_lt_compat_r. apply H0. apply Zle_0_nat. ring.
assert ((1 <= B_powerRZ (Z.of_nat n))%R).
unfold B_powerRZ. rewrite <- powerRZ_O with (INR B). apply powerRZ_complements.Rle_powerRZ.
apply Bplusgrandque1. apply Nat2Z.is_nonneg.
apply Rle_trans with ((x * B_powerRZ (Z.of_nat n) + B_powerRZ (Z.of_nat n))%R).
apply Rplus_le_compat_l. assumption. 
replace ((x * B_powerRZ (Z.of_nat n) + B_powerRZ (Z.of_nat n))%R) with
(( (x + 1) * B_powerRZ (Z.of_nat n))%R). apply Rmult_le_compat_r.
apply Rlt_le. apply inverseltR. apply Bexpos. 
apply Rle_trans with ((IZR (Z.of_nat (pentiereR x + 2)))%R).
 rewrite Nat2Z.inj_add. 
rewrite plus_IZR. replace ((IZR (Z.of_nat 2))%R) with ((1 + 1)%R). 
replace ((IZR (Z.of_nat (pentiereR x)) + (1 + 1))%R) with
(((IZR (Z.of_nat (pentiereR x)) + 1) + 1)%R).
apply Rplus_le_compat_r. rewrite <- INR_IZR_INZ.
apply Rlt_le. replace (1%R) with (INR 1). rewrite <- plus_INR. apply pentiereRgt.
unfold INR. reflexivity. ring. ring. 
apply IZR_le. apply inj_le. apply Nat.le_max_l.
 ring. apply Z.le_ge;apply Zle_0_nat. (*apply inversegeZ. apply Nat2Z.is_nonneg.*)
rewrite H4. apply Z.abs_neq_iff in H4. unfold multA. unfold suitex. 
unfold wBn. apply le_IZR. rewrite mult_IZR. rewrite <- B_powerRZandZofnat.
unfold Reelc_to_A. assert ((x >= 0 \/ 0 > x)%R). apply Rge_or_gt.
inversion H5. replace ((IZR (- xc (Z.of_nat n)))%R) with ((-IZR ( xc (Z.of_nat n)))%R).
assert ((- (IZR (xc (Z.of_nat n)) + 1) < -(x * B_powerRZ (Z.of_nat n)))%R).
apply Ropp_lt_contravar. apply H0. apply Zle_0_nat.
assert (( - IZR (xc (Z.of_nat n)) < - (x * B_powerRZ (Z.of_nat n)) + 1)%R).
replace (( - IZR (xc (Z.of_nat n)))%R) with (( - IZR (xc (Z.of_nat n)) - 1 + 1)%R).
apply Rplus_lt_compat_r. replace ((- IZR (xc (Z.of_nat n)) - 1)%R) with
((- (IZR (xc (Z.of_nat n)) + 1))%R). assumption. ring. ring. clear H7.
apply Rle_trans with ((- (x * B_powerRZ (Z.of_nat n)) + 1)%R).
apply Rlt_le. assumption. assert ((1 <= B_powerRZ (Z.of_nat n))%R).
unfold B_powerRZ. rewrite <- powerRZ_O with (INR B). apply powerRZ_complements.Rle_powerRZ.
apply Bplusgrandque1. apply Nat2Z.is_nonneg. 
apply Rle_trans with ((- (x * B_powerRZ (Z.of_nat n)) + B_powerRZ (Z.of_nat n))%R).
apply inverseleR. apply Rplus_ge_compat. apply inversegeR. apply Rle_refl.
apply inversegeR. assumption. replace ((- (x * B_powerRZ (Z.of_nat n)) + B_powerRZ (Z.of_nat n))%R)
with (( (-x + 1) * B_powerRZ (Z.of_nat n))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply inverseltR. apply Bexpos.
rewrite <- INR_IZR_INZ. apply Rle_trans with ((INR (pentiereR x + 2))%R).
 rewrite plus_INR. replace ((INR 2)%R) with ((1 + 1)%R).
replace ((INR (pentiereR x) + (1 + 1))%R) with (((INR (pentiereR x) + 1) + 1)%R).
apply Rplus_le_compat_r. apply Rle_trans with (x%R).
assert ( ({0 < x} + {0 = x})%R). apply Rle_lt_or_eq_dec. apply inverseleR. assumption.
inversion H9. apply Rmult_le_reg_r with ((/ x)%R). apply Rinv_0_lt_compat.
assumption. rewrite Rinv_r. replace ((-x * / x)%R) with ((- (x * / x))%R). rewrite Rinv_r.
lra. apply Rgt_not_eq. apply inversegtR. assumption. ring.
apply Rgt_not_eq. apply inversegtR. assumption. rewrite <- H10. lra.
replace (1%R) with (INR 1). rewrite <- plus_INR. apply Rlt_le. apply pentiereRgt.
unfold INR. reflexivity. ring. unfold INR. reflexivity. 
apply NleR. apply Nat.le_max_l. ring. 
replace ((- IZR (xc (Z.of_nat n)))%R) with ((0 - IZR (xc (Z.of_nat n)))%R).
rewrite <- minus_IZR. apply IZR_eq. ring. ring.
assert ((- (IZR (xc (Z.of_nat n)) + 1) < -(x * B_powerRZ (Z.of_nat n)))%R).
apply Ropp_lt_contravar. apply H0. apply Zle_0_nat.
assert (( - IZR (xc (Z.of_nat n)) < - (x * B_powerRZ (Z.of_nat n)) + 1)%R).
replace (( - IZR (xc (Z.of_nat n)))%R) with (( - IZR (xc (Z.of_nat n)) - 1 + 1)%R).
apply Rplus_lt_compat_r. replace ((- IZR (xc (Z.of_nat n)) - 1)%R) with
((- (IZR (xc (Z.of_nat n)) + 1))%R). assumption. ring. ring. clear H7.
apply Rle_trans with ((- (x * B_powerRZ (Z.of_nat n)) + 1)%R).
replace ((IZR (- xc (Z.of_nat n)))%R) with ((-IZR ( xc (Z.of_nat n)))%R).
apply Rlt_le. assumption. replace ((- IZR (xc (Z.of_nat n)))%R) with
((0 - IZR (xc (Z.of_nat n)))%R). rewrite <- minus_IZR. apply IZR_eq. ring. ring.
clear H8. assert ((1 <= B_powerRZ (Z.of_nat n))%R).
unfold B_powerRZ. rewrite <- powerRZ_O with (INR B). apply powerRZ_complements.Rle_powerRZ.
apply Bplusgrandque1. apply Nat2Z.is_nonneg. 
apply Rle_trans with ((- (x * B_powerRZ (Z.of_nat n)) + B_powerRZ (Z.of_nat n))%R).
apply inverseleR. apply Rplus_ge_compat. apply inversegeR. apply Rle_refl.
apply inversegeR. assumption. replace ((- (x * B_powerRZ (Z.of_nat n)) + B_powerRZ (Z.of_nat n))%R)
with (( (-x + 1) * B_powerRZ (Z.of_nat n))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply inverseltR. apply Bexpos.
rewrite <- INR_IZR_INZ. apply Rle_trans with ((INR (pentiereR (-x) + 2))%R).
 rewrite plus_INR. replace ((INR 2)%R) with ((1 + 1)%R).
replace ((INR (pentiereR (-x)) + (1 + 1))%R) with (((INR (pentiereR (-x)) + 1) + 1)%R).
apply Rplus_le_compat_r. apply Rlt_le. replace (1%R) with (INR 1). rewrite <- plus_INR. 
apply pentiereRgt. unfold INR. reflexivity. ring. unfold INR. ring.
apply NleR. apply Nat.le_max_r. ring. apply inversegeZ. apply Nat2Z.is_nonneg.
unfold regularwBn. unfold congruentwBn. intros. 
assert ( 0 + (suitex 1) =A suitex 1). apply Radd_0_l.
unfold equalA in H1. inversion H1. clear H1.
exists (Nat.max ((x + 1)%nat) (Z.to_nat r + 1) ). intros. assert (forall m : nat, (m > x)%nat -> 0 m = 0%Z).
intros. apply eq_IZR. apply Rplus_eq_reg_r with (IZR (suitex 1 m)).
rewrite <- plus_IZR. rewrite <- plus_IZR. apply IZR_eq. unfold plusA. 
apply eq_IZR. rewrite plus_IZR. rewrite Rplus_0_l. apply IZR_eq.
apply H2. assumption. clear H2. rewrite H4. rewrite H4.
unfold encadrement_nat in H. inversion H. clear H.
rewrite Z.sub_0_r. rewrite Z.sub_0_r.  
assert ({(k <= l)%nat} + {(k >= l)%nat}). apply le_ge_dec.
inversion H. 
assert ({(Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k < 0)%Z} 
+ {(Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k = 0)%Z} + 
{(Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k > 0)%Z}).
apply Ztrichotomy_inf. inversion H6. inversion H7.
rewrite Zabssgn. rewrite Z.sgn_neg. 
clear H4. assert ((((Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k) * -1) =
((Reelc_to_A xc l * wBn k - Reelc_to_A xc k * wBn l) ))%Z). ring. 
rewrite H4. clear H4. assert ((wBn l = wBn ((k + (l - k))%nat))%Z).
unfold wBn. replace ((k + (l - k))%nat) with (l%nat). reflexivity.
omega. replace ((Reelc_to_A xc k * wBn l)%Z) with 
((Reelc_to_A xc k * wBn (k + (l - k))%nat)%Z).
 assert ((wBn (k + (l - k))%nat = wBn k%nat * wBn (l - k)%nat)%Z).
unfold wBn. rewrite <- Zpower_exp. rewrite Nat2Z.inj_add. reflexivity.
apply inversegeZ. apply Nat2Z.is_nonneg.
apply inversegeZ. apply Nat2Z.is_nonneg. rewrite H9.
replace ((r * (Reelc_to_A xc l * wBn k - Reelc_to_A xc k * (wBn k * wBn (l - k)%nat)))%Z)
with ((wBn k * (r * (Reelc_to_A xc l - Reelc_to_A xc k * wBn (l - k)%nat)))%Z).
apply Zmult_le_compat_l. 
assert ((IZR (xc (Z.of_nat l)) - 1 < x0 * B_powerRZ (Z.of_nat l))%R).
apply H2. apply Zle_0_nat. replace (IZR (xc (Z.of_nat l))) with (IZR (Reelc_to_A xc l)) in H10.
apply le_IZR. rewrite mult_IZR. rewrite minus_IZR. rewrite mult_IZR.
assert ((IZR (Reelc_to_A xc l)  < x0 * B_powerRZ (Z.of_nat l) + 1)%R).
replace (IZR (Reelc_to_A xc l)) with ((IZR (Reelc_to_A xc l) - 1 + 1)%R).
apply Rplus_lt_compat_r. assumption. ring. clear H10.
assert ((- (IZR (Reelc_to_A xc k) + 1) < - (x0 * B_powerRZ (Z.of_nat k)))%R).
apply Ropp_gt_lt_contravar. replace (Reelc_to_A xc k) with (xc (Z.of_nat k)).
apply inversegtR. apply H2. apply Zle_0_nat. unfold Reelc_to_A. reflexivity.
assert ((- (IZR (Reelc_to_A xc k)) < - (x0 * B_powerRZ (Z.of_nat k)) + 1)%R).
replace ((- IZR (Reelc_to_A xc k))%R) with ((- IZR (Reelc_to_A xc k) - 1 + 1)%R).
apply Rplus_lt_compat_r. replace ((- IZR (Reelc_to_A xc k) - 1)%R) with
((- (IZR (Reelc_to_A xc k) + 1))%R). assumption. ring. ring.
clear H10. 
assert ((- IZR (Reelc_to_A xc k) * IZR (wBn (l - k)%nat) < 
(- (x0 * B_powerRZ (Z.of_nat k)) + 1 ) * IZR (wBn (l - k)%nat))%R). 
apply Rmult_lt_compat_r.  
unfold wBn. rewrite <- B_powerRZandZofnat. apply inverseltR. apply Bexpos. 
apply inversegeZ. apply Nat2Z.is_nonneg.
 assumption. clear H12.
assert (( IZR (Reelc_to_A xc l) + - IZR (Reelc_to_A xc k) * IZR (wBn (l - k)%nat)  <
(x0 * B_powerRZ (Z.of_nat l) + 1) + (- (x0 * B_powerRZ (Z.of_nat k)) + 1) * IZR (wBn (l - k)%nat))%R).
apply Rplus_lt_compat. assumption. assumption. clear H10 H11.
assert ((IZR r * (IZR (Reelc_to_A xc l) + - IZR (Reelc_to_A xc k) * IZR (wBn (l - k)%nat)) <
IZR r * (x0 * B_powerRZ (Z.of_nat l) + 1 + (- (x0 * B_powerRZ (Z.of_nat k)) + 1) * IZR (wBn (l - k)%nat)))%R).
apply inverseltR. apply Rmult_gt_compat_l. apply inversegtR. apply IZR_lt. assumption.
apply inversegtR. assumption. clear H12.
replace ((IZR r * (IZR (Reelc_to_A xc l) + - IZR (Reelc_to_A xc k) * IZR (wBn (l - k)%nat)))%R) with
((IZR r * (IZR (Reelc_to_A xc l)  - IZR (Reelc_to_A xc k) * IZR (wBn (l - k)%nat)))%R) in H10.
apply Rle_trans with 
((IZR r * (x0 * B_powerRZ (Z.of_nat l) + 1 + 
(- (x0 * B_powerRZ (Z.of_nat k)) + 1) * IZR (wBn (l - k)%nat)))%R).
apply Rlt_le. assumption. clear H10. 
replace (((- (x0 * B_powerRZ (Z.of_nat k)) + 1) * IZR (wBn (l - k)%nat))%R) with 
((- x0 * B_powerRZ (Z.of_nat l) + B_powerRZ (Z.of_nat (l - k)%nat))%R). 
replace ((x0 * B_powerRZ (Z.of_nat l) + 1 + (- x0 * B_powerRZ (Z.of_nat l) + B_powerRZ (Z.of_nat (l - k))))%R)
with ((B_powerRZ (Z.of_nat (l - k)) + 1)%R). unfold wBn. rewrite <- B_powerRZandZofnat.
replace ((IZR r * (B_powerRZ (Z.of_nat (l - k)) + 1))%R) with 
((IZR r * B_powerRZ (Z.of_nat (l - k)) + IZR r)%R). 
apply Rmult_le_reg_l with (( /B_powerRZ (Z.of_nat (l - k)))%R).
apply Rinv_0_lt_compat. apply inverseltR. apply Bexpos.
replace ((/ B_powerRZ (Z.of_nat (l - k)) * (IZR r * B_powerRZ (Z.of_nat (l - k)) + IZR r))%R) with
((IZR r * / B_powerRZ (Z.of_nat (l - k)) + IZR r)%R). 
replace ((/ B_powerRZ (Z.of_nat (l - k)) * B_powerRZ (Z.of_nat l))%R) with
((B_powerRZ (Z.of_nat k))%R).
assert ((IZR r <= B_powerRZ (r))%R). unfold B_powerRZ. 
assert (recurrence1 : forall n : nat, (IZR (Z.of_nat n) <= powerRZ (INR B) (Z.of_nat n))%R).
intros n1. induction n1 as [|n1']. simpl. lra.
replace ((S n1')%nat) with ((n1' + 1)%nat). rewrite Nat2Z.inj_add.
rewrite plus_IZR. apply Rle_trans with  ((powerRZ (INR B) (Z.of_nat n1') + IZR (Z.of_nat 1))%R).
apply Rplus_le_compat_r. assumption. replace ((Z.of_nat 1)%Z) with (1%Z).
replace ((Z.of_nat n1' + 1)%Z) with ((Z.succ (Z.of_nat n1'))%Z).
rewrite powerRZ_complements.powerRZ_Zs. 
apply Rle_trans with ((powerRZ (INR B) (Z.of_nat n1') * 2)%R).
replace ((powerRZ (INR B) (Z.of_nat n1') * 2)%R) with
 ((powerRZ (INR B) (Z.of_nat n1') + powerRZ (INR B) (Z.of_nat n1'))%R).
apply Rplus_le_compat_l.  rewrite <- powerRZ_O with (INR B).
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. apply Nat2Z.is_nonneg.
ring. apply Rmult_le_compat_l. replace ((powerRZ (INR B) (Z.of_nat n1'))%R) with
((B_powerRZ (Z.of_nat n1'))%R). apply Rlt_le. apply inverseltR. apply Bexpos.
unfold B_powerRZ. reflexivity. apply Rle_trans with (INR 4). unfold INR. lra.
apply le_INR. apply Axiomes.B_sup_4. apply Rgt_not_eq. apply inversegtR. 
apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring. ring.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). apply recurrence1.
rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption.
assert ((IZR r * / B_powerRZ (Z.of_nat (l - k)) <= B_powerRZ r * / B_powerRZ (Z.of_nat (l - k)))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply inverseltR.
apply Bexpos. assumption. replace ((B_powerRZ r * / B_powerRZ (Z.of_nat (l - k)))%R) with
((B_powerRZ (r - Z.of_nat (l - k)))%R) in H11.
apply Rle_trans with (( B_powerRZ (r - Z.of_nat (l - k)) + B_powerRZ r)%R).
apply Rplus_le_compat. assumption. assumption. apply Rle_trans with 
((B_powerRZ r + B_powerRZ r)%R). apply Rplus_le_compat. unfold B_powerRZ.
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. 
replace (r%Z) with ((r + (-0))%Z). 
replace ((r + - 0 - Z.of_nat (l - k))%Z) with ((r + - Z.of_nat (l - k))%Z).
apply Zplus_le_compat_l. apply Z.opp_le_mono. rewrite Z.opp_involutive.
rewrite Z.opp_involutive. rewrite <- Nat2Z.inj_0. apply inj_le.
apply INR_le. apply Rplus_le_reg_r with (INR k). rewrite minus_INR.
simpl. replace ((INR l - INR k + INR k)%R) with ((INR l)%R). 
replace ((0 + INR k)%R) with ((INR k)%R). apply NleR. assumption.
ring. ring. assumption. ring. ring.
apply Rle_refl. replace ((B_powerRZ r + B_powerRZ r)%R) with ((2 * B_powerRZ r)%R).
assert ((2 * B_powerRZ r <= INR B * B_powerRZ r)%R). apply Rmult_le_compat_r.
apply Rlt_le. apply inverseltR. apply Bexpos. 
apply Rle_trans with (4%R). lra. replace (4%R) with (INR 4).
apply le_INR. apply Axiomes.B_sup_4. unfold INR. ring.
replace ((INR B * B_powerRZ r)%R) with ((B_powerRZ (r + 1))%R) in H12.
apply Rle_trans with ((B_powerRZ (r + 1))%R). assumption. 
unfold B_powerRZ. apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). replace (1%Z) with (Z.of_nat 1).
rewrite <- Nat2Z.inj_add. apply inj_le. apply Nat.max_lub_r with ((x + 1)%nat).
apply inj_ge in H1. apply inverseleZ in H1. apply Nat2Z.inj_le in H1. assumption.
 ring. rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption. unfold B_powerRZ. replace ((r + 1)%Z) with (Z.succ r).
 rewrite powerRZ_complements.powerRZ_Zs. ring. apply Rgt_not_eq. 
apply inversegtR. apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. 
rewrite Nat2Z.inj_sub_max.   replace ((- Z.max 0 (Z.of_nat l - Z.of_nat k) + Z.of_nat l)%Z)
with ((- (Z.max 0 (Z.of_nat l - Z.of_nat k)) + Z.of_nat l)%Z).
replace ((Z.max 0 (Z.of_nat l - Z.of_nat k))%Z) with ((Z.of_nat l - Z.of_nat k)%Z). ring. 
symmetry. apply Z.max_r_iff. 
apply le_IZR. apply Rplus_le_reg_l with (IZR (Z.of_nat k)). 
replace ((IZR (Z.of_nat k) + 0)%R) with ((IZR (Z.of_nat k))%R).
replace ((IZR (Z.of_nat k) + IZR (Z.of_nat l - Z.of_nat k))%R) with
((IZR (Z.of_nat l))%R). apply IZR_le. apply inj_le. assumption.
rewrite minus_IZR. ring. ring. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
replace ((/ B_powerRZ (Z.of_nat (l - k)) * (IZR r * B_powerRZ (Z.of_nat (l - k)) + IZR r))%R) with
((IZR r * / B_powerRZ (Z.of_nat (l - k)) +
 IZR r * (B_powerRZ (Z.of_nat (l - k)) * / B_powerRZ (Z.of_nat (l - k))))%R).
rewrite Rinv_r. ring. apply Rgt_not_eq. apply Bexpos. ring. ring.
apply inversegeZ. apply Nat2Z.is_nonneg. ring. 
unfold wBn. rewrite <- B_powerRZandZofnat. replace 
(((- (x0 * B_powerRZ (Z.of_nat k)) + 1) * B_powerRZ (Z.of_nat (l - k)))%R) with
((-(x0 * B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k))) + 1 * B_powerRZ (Z.of_nat (l - k)))%R).
replace ((x0 * B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k)))%R) with
((x0 * B_powerRZ(Z.of_nat k + Z.of_nat (l - k)))%R). rewrite Nat2Z.inj_sub.
replace ((Z.of_nat k + (Z.of_nat l - Z.of_nat k))%Z) with (Z.of_nat l). ring.
ring. assumption. rewrite <- produitB_powerRZ. ring. ring.
rewrite Nat2Z.inj_sub. apply inversegeZ.
apply le_IZR. apply Rplus_le_reg_l with (IZR (Z.of_nat k)). 
replace ((IZR (Z.of_nat k) + 0)%R) with ((IZR (Z.of_nat k))%R).
replace ((IZR (Z.of_nat k) + IZR (Z.of_nat l - Z.of_nat k))%R) with
((IZR (Z.of_nat l))%R). apply IZR_le. apply inj_le. assumption.
rewrite minus_IZR. ring. ring. assumption. ring.
unfold Reelc_to_A. reflexivity. unfold wBn. apply Zpower_complements.Zpower_le_0.
apply lt_IZR. apply Rlt_le_trans with (4%R). lra.
apply IZR_le. replace (4%Z) with (Z.of_nat 4). apply inj_le.
apply Axiomes.B_sup_4. ring. ring. rewrite <- H4. reflexivity. assumption.
rewrite H8. rewrite Z.abs_0. simpl. replace ((r * 0)%Z) with (0%Z).
apply le_IZR. rewrite mult_IZR. apply Rlt_le. apply inverseltR. apply produitdedeuxpositifsR.
unfold wBn. rewrite <- B_powerRZandZofnat. apply Bexpos. apply inversegeZ.
apply Nat2Z.is_nonneg. unfold wBn. rewrite <- B_powerRZandZofnat. 
apply Bexpos. apply inversegeZ. apply Nat2Z.is_nonneg. ring.
rewrite Zabssgn. rewrite Z.sgn_pos. 
 assert ((wBn l = wBn ((k + (l - k))%nat))%Z).
unfold wBn. replace ((k + (l - k))%nat) with (l%nat). reflexivity.
omega. replace ((Reelc_to_A xc k * wBn l)%Z) with 
((Reelc_to_A xc k * wBn (k + (l - k))%nat)%Z).
 assert ((wBn (k + (l - k))%nat = wBn k%nat * wBn (l - k)%nat)%Z).
unfold wBn. rewrite <- Zpower_exp. rewrite Nat2Z.inj_add. reflexivity.
apply inversegeZ. apply Nat2Z.is_nonneg.
apply inversegeZ. apply Nat2Z.is_nonneg. rewrite H9. replace
((r * ((Reelc_to_A xc k * (wBn k * wBn (l - k)%nat) - Reelc_to_A xc l * wBn k) * 1))%Z)
with ((wBn k * (r * ( Reelc_to_A xc k * wBn (l - k)%nat - Reelc_to_A xc l)))%Z). 
apply Zmult_le_compat_l.  
assert ((- (IZR (xc (Z.of_nat l)) + 1) < -(x0 * B_powerRZ (Z.of_nat l)))%R).
apply Ropp_gt_lt_contravar. apply inversegtR. apply H2. apply Zle_0_nat.
replace (Reelc_to_A xc k) with (xc (Z.of_nat k)).
replace (Reelc_to_A xc l) with (xc (Z.of_nat l)).
assert ((- (IZR (xc (Z.of_nat l))) < - (x0 * B_powerRZ (Z.of_nat l)) + 1)%R).
replace ((- IZR (xc (Z.of_nat l)))%R) with (((- IZR (xc (Z.of_nat l))) - 1 + 1)%R).
apply Rplus_lt_compat_r. replace ((- IZR (xc (Z.of_nat l)) - 1)%R) with
((- (IZR (xc (Z.of_nat l)) + 1))%R). assumption. ring. ring. clear H10.
assert ((IZR ( xc (Z.of_nat k))  < x0 * B_powerRZ (Z.of_nat k) + 1)%R).
replace (IZR ( xc (Z.of_nat k))) with ((IZR ( xc (Z.of_nat k)) - 1 + 1)%R).
apply Rplus_lt_compat_r. apply H2. apply Zle_0_nat. ring. 
assert ((IZR (xc (Z.of_nat k)) * IZR (wBn (l - k)%nat) < 
(x0 * B_powerRZ (Z.of_nat k) + 1) * IZR (wBn (l - k)%nat))%R). 
apply Rmult_lt_compat_r.  
unfold wBn. rewrite <- B_powerRZandZofnat. apply inverseltR. apply Bexpos. 
apply inversegeZ. apply Nat2Z.is_nonneg.
 assumption. 
assert ((IZR (xc (Z.of_nat k)) * IZR (wBn (l - k)%nat) + - IZR (xc (Z.of_nat l))   <
((x0 * B_powerRZ (Z.of_nat k) + 1) * IZR (wBn (l - k)%nat)) + (- (x0 * B_powerRZ (Z.of_nat l)) + 1) )%R).
apply Rplus_lt_compat. assumption. assumption. clear H10 H11.
assert ((IZR r * (IZR (xc (Z.of_nat k)) * IZR (wBn (l - k)%nat) + - IZR (xc (Z.of_nat l))) <
       IZR r * ((x0 * B_powerRZ (Z.of_nat k) + 1) * IZR (wBn (l - k)%nat) + (- (x0 * B_powerRZ (Z.of_nat l)) + 1)))%R).
apply inverseltR. apply Rmult_gt_compat_l. apply inversegtR. apply IZR_lt. assumption.
apply inversegtR. assumption. 
replace ((IZR r * (IZR (xc (Z.of_nat k)) * IZR (wBn (l - k)%nat) + - IZR (xc (Z.of_nat l))))%R) with
((IZR r * (IZR (xc (Z.of_nat k)) * IZR (wBn (l - k)%nat) - IZR (xc (Z.of_nat l))))%R) in H10.
apply le_IZR. rewrite mult_IZR. rewrite minus_IZR. rewrite mult_IZR.
apply Rle_trans with 
((IZR r * ((x0 * B_powerRZ (Z.of_nat k) + 1) * IZR (wBn (l - k)%nat) + (- (x0 * B_powerRZ (Z.of_nat l)) + 1)))%R).
apply Rlt_le. assumption. clear H10.
replace (((x0 * B_powerRZ (Z.of_nat k) + 1) * IZR (wBn (l - k)%nat))%R) with
((x0 * B_powerRZ (Z.of_nat k) * IZR (wBn (l - k)%nat) + IZR (wBn (l - k)%nat))%R).
unfold wBn. rewrite <- B_powerRZandZofnat. 
replace ((x0 * B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k)))%R) with
((x0 * B_powerRZ (Z.of_nat l))%R).
replace ((x0 * B_powerRZ (Z.of_nat l) + B_powerRZ (Z.of_nat (l - k)) + 
(- (x0 * B_powerRZ (Z.of_nat l)) + 1))%R) with ((B_powerRZ (Z.of_nat (l - k)) + 1)%R).
replace ((IZR r * (B_powerRZ (Z.of_nat (l - k)) + 1))%R) with 
((IZR r + IZR r * B_powerRZ (Z.of_nat (l - k)))%R).
apply Rmult_le_reg_l with (( /B_powerRZ (Z.of_nat (l - k)))%R).
apply Rinv_0_lt_compat. apply inverseltR. apply Bexpos.
replace ((/ B_powerRZ (Z.of_nat (l - k)) * (IZR r + IZR r * B_powerRZ (Z.of_nat (l - k))))%R) with
((IZR r * / B_powerRZ (Z.of_nat (l - k)) + IZR r)%R).
rewrite <- B_powerRZandZofnat. 
replace ((/ B_powerRZ (Z.of_nat (l - k)) * B_powerRZ (Z.of_nat l))%R) with
((B_powerRZ (Z.of_nat k))%R).
assert ((IZR r <= B_powerRZ (r))%R). unfold B_powerRZ. 
assert (recurrence1 : forall n : nat, (IZR (Z.of_nat n) <= powerRZ (INR B) (Z.of_nat n))%R).
intros n1. induction n1 as [|n1']. simpl. lra.
replace ((S n1')%nat) with ((n1' + 1)%nat). rewrite Nat2Z.inj_add.
rewrite plus_IZR. apply Rle_trans with  ((powerRZ (INR B) (Z.of_nat n1') + IZR (Z.of_nat 1))%R).
apply Rplus_le_compat_r. assumption. replace ((Z.of_nat 1)%Z) with (1%Z).
replace ((Z.of_nat n1' + 1)%Z) with ((Z.succ (Z.of_nat n1'))%Z).
rewrite powerRZ_complements.powerRZ_Zs. 
apply Rle_trans with ((powerRZ (INR B) (Z.of_nat n1') * 2)%R).
replace ((powerRZ (INR B) (Z.of_nat n1') * 2)%R) with
 ((powerRZ (INR B) (Z.of_nat n1') + powerRZ (INR B) (Z.of_nat n1'))%R).
apply Rplus_le_compat_l.  rewrite <- powerRZ_O with (INR B).
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. apply Nat2Z.is_nonneg.
ring. apply Rmult_le_compat_l. replace ((powerRZ (INR B) (Z.of_nat n1'))%R) with
((B_powerRZ (Z.of_nat n1'))%R). apply Rlt_le. apply inverseltR. apply Bexpos.
unfold B_powerRZ. reflexivity. apply Rle_trans with (INR 4). unfold INR. lra.
apply le_INR. apply Axiomes.B_sup_4. apply Rgt_not_eq. apply inversegtR. 
apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring. ring.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). apply recurrence1.
rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption.
assert ((IZR r * / B_powerRZ (Z.of_nat (l - k)) <= B_powerRZ r * / B_powerRZ (Z.of_nat (l - k)))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply inverseltR.
apply Bexpos. assumption. replace ((B_powerRZ r * / B_powerRZ (Z.of_nat (l - k)))%R) with
((B_powerRZ (r - Z.of_nat (l - k)))%R) in H11.
apply Rle_trans with (( B_powerRZ (r - Z.of_nat (l - k)) + B_powerRZ r)%R).
apply Rplus_le_compat. assumption. assumption. apply Rle_trans with 
((B_powerRZ r + B_powerRZ r)%R). apply Rplus_le_compat. unfold B_powerRZ.
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. 
replace (r%Z) with ((r + (-0))%Z). 
replace ((r + - 0 - Z.of_nat (l - k))%Z) with ((r + - Z.of_nat (l - k))%Z).
apply Zplus_le_compat_l. apply Z.opp_le_mono. rewrite Z.opp_involutive.
rewrite Z.opp_involutive. rewrite <- Nat2Z.inj_0. apply inj_le.
apply INR_le. apply Rplus_le_reg_r with (INR k). rewrite minus_INR.
simpl. replace ((INR l - INR k + INR k)%R) with ((INR l)%R). 
replace ((0 + INR k)%R) with ((INR k)%R). apply NleR. assumption.
ring. ring. assumption. ring. ring.
apply Rle_refl. replace ((B_powerRZ r + B_powerRZ r)%R) with ((2 * B_powerRZ r)%R).
assert ((2 * B_powerRZ r <= INR B * B_powerRZ r)%R). apply Rmult_le_compat_r.
apply Rlt_le. apply inverseltR. apply Bexpos. 
apply Rle_trans with (4%R). lra. replace (4%R) with (INR 4).
apply le_INR. apply Axiomes.B_sup_4. unfold INR. ring.
replace ((INR B * B_powerRZ r)%R) with ((B_powerRZ (r + 1))%R) in H14.
apply Rle_trans with ((B_powerRZ (r + 1))%R). assumption. 
unfold B_powerRZ. apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). replace (1%Z) with (Z.of_nat 1).
rewrite <- Nat2Z.inj_add. apply inj_le. apply Nat.max_lub_r with ((x + 1)%nat).
apply inj_ge in H1. apply inverseleZ in H1. apply Nat2Z.inj_le in H1. assumption.
 ring. rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption. unfold B_powerRZ. replace ((r + 1)%Z) with (Z.succ r).
 rewrite powerRZ_complements.powerRZ_Zs. ring. apply Rgt_not_eq. 
apply inversegtR. apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. 
rewrite Nat2Z.inj_sub_max.   replace ((- Z.max 0 (Z.of_nat l - Z.of_nat k) + Z.of_nat l)%Z)
with ((- (Z.max 0 (Z.of_nat l - Z.of_nat k)) + Z.of_nat l)%Z).
replace ((Z.max 0 (Z.of_nat l - Z.of_nat k))%Z) with ((Z.of_nat l - Z.of_nat k)%Z). ring. 
symmetry. apply Z.max_r_iff. 
apply le_IZR. apply Rplus_le_reg_l with (IZR (Z.of_nat k)). 
replace ((IZR (Z.of_nat k) + 0)%R) with ((IZR (Z.of_nat k))%R).
replace ((IZR (Z.of_nat k) + IZR (Z.of_nat l - Z.of_nat k))%R) with
((IZR (Z.of_nat l))%R). apply IZR_le. apply inj_le. assumption.
rewrite minus_IZR. ring. ring. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul. 
apply inversegeZ. apply Nat2Z.is_nonneg.
replace ((/ B_powerRZ (Z.of_nat (l - k)) * (IZR r * B_powerRZ (Z.of_nat (l - k)) + IZR r))%R) with
((IZR r * / B_powerRZ (Z.of_nat (l - k)) +
 IZR r * (B_powerRZ (Z.of_nat (l - k)) * / B_powerRZ (Z.of_nat (l - k))))%R).
replace ((/ B_powerRZ (Z.of_nat (l - k)) * (IZR r + IZR r * B_powerRZ (Z.of_nat (l - k))))%R) with
((IZR r * / B_powerRZ (Z.of_nat (l - k)) + 
 IZR r *( B_powerRZ (Z.of_nat (l - k)) * / B_powerRZ (Z.of_nat (l - k))))%R).
rewrite Rinv_r. ring. apply Rgt_not_eq. apply Bexpos. ring. ring. ring. ring.
replace ((x0 * B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k)))%R) with
((x0 * (B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k))))%R).
apply Rmult_eq_compat_l. rewrite produitB_powerRZ.
unfold B_powerRZ. apply powerRZ_complements.powerRZ_trivial. 
rewrite Nat2Z.inj_sub. ring. assumption. ring.
apply inversegeZ. apply Nat2Z.is_nonneg. ring. 
unfold wBn. rewrite <- B_powerRZandZofnat. replace 
(((- (x0 * B_powerRZ (Z.of_nat k)) + 1) * B_powerRZ (Z.of_nat (l - k)))%R) with
((-(x0 * B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k))) + 1 * B_powerRZ (Z.of_nat (l - k)))%R).
replace ((x0 * B_powerRZ (Z.of_nat k) * B_powerRZ (Z.of_nat (l - k)))%R) with
((x0 * B_powerRZ(Z.of_nat k + Z.of_nat (l - k)))%R). rewrite Nat2Z.inj_sub.
replace ((Z.of_nat k + (Z.of_nat l - Z.of_nat k))%Z) with (Z.of_nat l). ring.
ring. assumption. rewrite <- produitB_powerRZ. ring. ring.
rewrite Nat2Z.inj_sub. apply inversegeZ.
apply le_IZR. apply Rplus_le_reg_l with (IZR (Z.of_nat k)). 
replace ((IZR (Z.of_nat k) + 0)%R) with ((IZR (Z.of_nat k))%R).
replace ((IZR (Z.of_nat k) + IZR (Z.of_nat l - Z.of_nat k))%R) with
((IZR (Z.of_nat l))%R). apply IZR_le. apply inj_le. assumption.
rewrite minus_IZR. ring. ring. assumption. unfold Reelc_to_A. reflexivity.
unfold Reelc_to_A. reflexivity. unfold wBn. apply Zpower_complements.Zpower_le_0.
apply lt_IZR. apply Rlt_le_trans with (4%R). lra.
apply IZR_le. replace (4%Z) with (Z.of_nat 4). apply inj_le.
apply Axiomes.B_sup_4. ring. ring. 
apply eq_IZR.  rewrite mult_IZR. rewrite mult_IZR. apply Rmult_eq_compat_l.
apply IZR_eq. unfold wBn. rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_sub.
replace ((Z.of_nat k + (Z.of_nat l - Z.of_nat k))%Z) with ((Z.of_nat l)%Z).
reflexivity. ring. assumption. apply inverseltZ. assumption.
assert ({(Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k < 0)%Z} 
+ {(Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k = 0)%Z} + 
{(Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k > 0)%Z}).
apply Ztrichotomy_inf. inversion H6. inversion H7.
rewrite Zabssgn. rewrite Z.sgn_neg. 
clear H6. assert ((((Reelc_to_A xc k * wBn l - Reelc_to_A xc l * wBn k) * -1) =
((Reelc_to_A xc l * wBn k - Reelc_to_A xc k * wBn l) ))%Z). ring. 
rewrite H6. clear H4. assert ((wBn k = wBn ((l + (k - l))%nat))%Z).
unfold wBn. replace ((l + (k - l))%nat) with (k%nat). reflexivity.
omega. replace ((Reelc_to_A xc l * wBn k)%Z) with 
((Reelc_to_A xc l * wBn (l + (k - l))%nat)%Z).
 assert ((wBn (l + (k - l))%nat = wBn l%nat * wBn (k - l)%nat)%Z).
unfold wBn. rewrite <- Zpower_exp. rewrite Nat2Z.inj_add. reflexivity.
apply inversegeZ. apply Nat2Z.is_nonneg.
apply inversegeZ. apply Nat2Z.is_nonneg. rewrite H9.
replace ((r * (Reelc_to_A xc l * (wBn l * wBn (k - l)%nat) - Reelc_to_A xc k * wBn l))%Z)
with ((wBn l * (r * (Reelc_to_A xc l * wBn (k - l)%nat  - Reelc_to_A xc k)))%Z).
replace ((wBn k * wBn l)%Z) with ((wBn l * wBn k)%Z).
apply Zmult_le_compat_l. 
assert ((IZR (xc (Z.of_nat l)) - 1 < x0 * B_powerRZ (Z.of_nat l))%R).
apply H2. apply Zle_0_nat. replace (IZR (xc (Z.of_nat l))) with (IZR (Reelc_to_A xc l)) in H10.
apply le_IZR. rewrite mult_IZR. rewrite minus_IZR. rewrite mult_IZR.
assert ((IZR (Reelc_to_A xc l)  < x0 * B_powerRZ (Z.of_nat l) + 1)%R).
replace (IZR (Reelc_to_A xc l)) with ((IZR (Reelc_to_A xc l) - 1 + 1)%R).
apply Rplus_lt_compat_r. assumption. ring. clear H10.
assert ((IZR (Reelc_to_A xc l) * IZR (wBn (k - l)%nat) < 
(x0 * B_powerRZ (Z.of_nat l) + 1) * IZR (wBn (k - l)%nat))%R).
apply Rmult_lt_compat_r. unfold wBn. rewrite <- B_powerRZandZofnat.
apply inverseltR. apply Bexpos. apply inversegeZ. apply Nat2Z.is_nonneg.
assumption. clear H11.
assert ((- (IZR (Reelc_to_A xc k) + 1) < - (x0 * B_powerRZ (Z.of_nat k)))%R).
apply Ropp_lt_contravar. replace (IZR (Reelc_to_A xc k)%R) with 
((IZR (xc (Z.of_nat k)))%R). apply H2. apply Zle_0_nat. unfold Reelc_to_A. reflexivity.
assert ((- (IZR (Reelc_to_A xc k)) < - (x0 * B_powerRZ (Z.of_nat k)) + 1)%R).
replace ((- IZR (Reelc_to_A xc k))%R) with ((- IZR (Reelc_to_A xc k) - 1 + 1)%R).
apply Rplus_lt_compat_r. replace ((- IZR (Reelc_to_A xc k) - 1)%R) with
((- (IZR (Reelc_to_A xc k) + 1))%R). assumption. ring. ring.
clear H11. 
assert (( IZR (Reelc_to_A xc l) * IZR (wBn (k - l)%nat) + - IZR (Reelc_to_A xc k)  <
(x0 * B_powerRZ (Z.of_nat l) + 1) * IZR (wBn (k - l)%nat) + (- (x0 * B_powerRZ (Z.of_nat k)) + 1))%R).
apply Rplus_lt_compat. assumption. assumption. clear H10 H12.
assert ((IZR r * (IZR (Reelc_to_A xc l) * IZR (wBn (k - l)%nat) + - IZR (Reelc_to_A xc k)) <
IZR r *((x0 * B_powerRZ (Z.of_nat l) + 1) * IZR (wBn (k - l)%nat) + (- (x0 * B_powerRZ (Z.of_nat k)) + 1)))%R).
apply inverseltR. apply Rmult_gt_compat_l. apply inversegtR. apply IZR_lt. assumption.
apply inversegtR. assumption. clear H11.
replace ((IZR r * (IZR (Reelc_to_A xc l) * IZR (wBn (k - l)%nat) + - IZR (Reelc_to_A xc k)))%R) with
((IZR r * (IZR (Reelc_to_A xc l) * IZR (wBn (k - l)%nat) - IZR (Reelc_to_A xc k)))%R) in H10.
apply Rle_trans with 
((IZR r *
((x0 * B_powerRZ (Z.of_nat l) + 1) * IZR (wBn (k - l)%nat) + (- (x0 * B_powerRZ (Z.of_nat k)) + 1)))%R).
apply Rlt_le. assumption. clear H10.
replace (((x0 * B_powerRZ (Z.of_nat l) + 1) * IZR (wBn (k - l)%nat))%R) with 
((x0 * B_powerRZ (Z.of_nat l) * IZR (wBn (k - l)%nat) + IZR (wBn (k - l)%nat))%R).
replace ((x0 * B_powerRZ (Z.of_nat l) * IZR (wBn (k - l)%nat))%R) with
((x0 * B_powerRZ (Z.of_nat k) )%R).
replace ((x0 * B_powerRZ (Z.of_nat k) + IZR (wBn (k - l)%nat) + (- (x0 * B_powerRZ (Z.of_nat k)) + 1))%R)
with ((IZR (wBn (k - l)%nat) + 1)%R). 
replace ((IZR r * (IZR (wBn (k - l)%nat) + 1))%R) with 
((IZR r * IZR (wBn (k - l)%nat) + IZR r)%R).
apply Rmult_le_reg_l with (( /B_powerRZ (Z.of_nat (k - l)))%R).
apply Rinv_0_lt_compat. apply inverseltR. apply Bexpos.
replace ((/ B_powerRZ (Z.of_nat (k - l)) * (IZR r * IZR (wBn (k - l)%nat) + IZR r))%R) with
((IZR r * / B_powerRZ (Z.of_nat (k - l)) + IZR r)%R).
unfold wBn. rewrite <- B_powerRZandZofnat.
replace ((/ B_powerRZ (Z.of_nat (k - l)) * B_powerRZ (Z.of_nat k))%R) with
((B_powerRZ (Z.of_nat l))%R).
assert ((IZR r <= B_powerRZ (r))%R). unfold B_powerRZ. 
assert (recurrence1 : forall n : nat, (IZR (Z.of_nat n) <= powerRZ (INR B) (Z.of_nat n))%R).
intros n1. induction n1 as [|n1']. simpl. lra.
replace ((S n1')%nat) with ((n1' + 1)%nat). rewrite Nat2Z.inj_add.
rewrite plus_IZR. apply Rle_trans with  ((powerRZ (INR B) (Z.of_nat n1') + IZR (Z.of_nat 1))%R).
apply Rplus_le_compat_r. assumption. replace ((Z.of_nat 1)%Z) with (1%Z).
replace ((Z.of_nat n1' + 1)%Z) with ((Z.succ (Z.of_nat n1'))%Z).
rewrite powerRZ_complements.powerRZ_Zs. 
apply Rle_trans with ((powerRZ (INR B) (Z.of_nat n1') * 2)%R).
replace ((powerRZ (INR B) (Z.of_nat n1') * 2)%R) with
 ((powerRZ (INR B) (Z.of_nat n1') + powerRZ (INR B) (Z.of_nat n1'))%R).
apply Rplus_le_compat_l. rewrite <- powerRZ_O with (INR B).
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. apply Nat2Z.is_nonneg.
ring. apply Rmult_le_compat_l. replace ((powerRZ (INR B) (Z.of_nat n1'))%R) with
((B_powerRZ (Z.of_nat n1'))%R). apply Rlt_le. apply inverseltR. apply Bexpos.
unfold B_powerRZ. reflexivity. apply Rle_trans with (INR 4). unfold INR. lra.
apply le_INR. apply Axiomes.B_sup_4. apply Rgt_not_eq. apply inversegtR. 
apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring. ring.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). apply recurrence1.
rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption.
assert ((IZR r * / B_powerRZ (Z.of_nat (k - l)) <= B_powerRZ r * / B_powerRZ (Z.of_nat (k - l)))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply inverseltR.
apply Bexpos. assumption. replace ((B_powerRZ r * / B_powerRZ (Z.of_nat (k - l)))%R) with
((B_powerRZ (r - Z.of_nat (k - l)))%R) in H11.
apply Rle_trans with (( B_powerRZ (r - Z.of_nat (k - l)) + B_powerRZ r)%R).
apply Rplus_le_compat. assumption. assumption. apply Rle_trans with 
((B_powerRZ r + B_powerRZ r)%R). apply Rplus_le_compat. unfold B_powerRZ.
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. 
replace (r%Z) with ((r + (-0))%Z). 
replace ((r + - 0 - Z.of_nat (k - l))%Z) with ((r + - Z.of_nat (k - l))%Z).
apply Zplus_le_compat_l. apply Z.opp_le_mono. rewrite Z.opp_involutive.
rewrite Z.opp_involutive. rewrite <- Nat2Z.inj_0. apply inj_le.
apply INR_le. apply Rplus_le_reg_r with (INR l). rewrite minus_INR.
simpl. replace ((INR k - INR l + INR l)%R) with ((INR k)%R). 
replace ((0 + INR l)%R) with ((INR l)%R). apply NleR. assumption.
ring. ring. assumption. ring. ring.
apply Rle_refl. replace ((B_powerRZ r + B_powerRZ r)%R) with ((2 * B_powerRZ r)%R).
assert ((2 * B_powerRZ r <= INR B * B_powerRZ r)%R). apply Rmult_le_compat_r.
apply Rlt_le. apply inverseltR. apply Bexpos. 
apply Rle_trans with (4%R). lra. replace (4%R) with (INR 4).
apply le_INR. apply Axiomes.B_sup_4. unfold INR. ring.
replace ((INR B * B_powerRZ r)%R) with ((B_powerRZ (r + 1))%R) in H12.
apply Rle_trans with ((B_powerRZ (r + 1))%R). assumption. 
unfold B_powerRZ. apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). replace (1%Z) with (Z.of_nat 1).
rewrite <- Nat2Z.inj_add. apply inj_le. apply Nat.max_lub_r with ((x + 1)%nat).
apply inj_ge in H1. apply inverseleZ in H1. apply Nat2Z.inj_le in H1. assumption.
 ring. rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption. unfold B_powerRZ. replace ((r + 1)%Z) with (Z.succ r).
 rewrite powerRZ_complements.powerRZ_Zs. ring. apply Rgt_not_eq. 
apply inversegtR. apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. 
rewrite Nat2Z.inj_sub_max.   replace ((- Z.max 0 (Z.of_nat k - Z.of_nat l) + Z.of_nat k)%Z)
with ((- (Z.max 0 (Z.of_nat k - Z.of_nat l)) + Z.of_nat k)%Z).
replace ((Z.max 0 (Z.of_nat k - Z.of_nat l))%Z) with ((Z.of_nat k - Z.of_nat l)%Z). ring. 
symmetry. apply Z.max_r_iff. 
apply le_IZR. apply Rplus_le_reg_l with (IZR (Z.of_nat l)). 
replace ((IZR (Z.of_nat l) + 0)%R) with ((IZR (Z.of_nat l))%R).
replace ((IZR (Z.of_nat l) + IZR (Z.of_nat k - Z.of_nat l))%R) with
((IZR (Z.of_nat k))%R). apply IZR_le. apply inj_le. assumption.
rewrite minus_IZR. ring. ring. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply inversegeZ. apply Nat2Z.is_nonneg. unfold wBn. rewrite <- B_powerRZandZofnat.
replace ((/ B_powerRZ (Z.of_nat (k - l)) * (IZR r * B_powerRZ (Z.of_nat (k - l)) + IZR r))%R) with
((IZR r * / B_powerRZ (Z.of_nat (k - l)) +
 IZR r * (B_powerRZ (Z.of_nat (k - l)) * / B_powerRZ (Z.of_nat (k - l))))%R).
rewrite Rinv_r. ring. apply Rgt_not_eq. apply Bexpos. ring. apply inversegeZ.
apply Nat2Z.is_nonneg. ring. ring. unfold wBn. rewrite <- B_powerRZandZofnat. 
replace ((x0 * B_powerRZ (Z.of_nat l) * B_powerRZ (Z.of_nat (k - l)))%R) with
((x0 * (B_powerRZ (Z.of_nat l) * B_powerRZ (Z.of_nat (k - l))))%R).
rewrite  produitB_powerRZ. 
replace ((Z.of_nat l + Z.of_nat (k - l))%Z) with ((Z.of_nat k)%Z).
reflexivity. rewrite Nat2Z.inj_sub. ring. assumption. ring.
apply inversegeZ. apply Nat2Z.is_nonneg. ring. ring. unfold Reelc_to_A.
reflexivity. unfold wBn. apply Zpower_complements.Zpower_le_0.
apply lt_IZR. apply Rlt_le_trans with (4%R). lra.
apply IZR_le. replace (4%Z) with (Z.of_nat 4). apply inj_le.
apply Axiomes.B_sup_4. ring. ring. ring. rewrite <- H4. reflexivity. assumption.
rewrite H8. rewrite Z.abs_0. simpl. replace ((r * 0)%Z) with (0%Z).
apply le_IZR. rewrite mult_IZR. apply Rlt_le. apply inverseltR. apply produitdedeuxpositifsR.
unfold wBn. rewrite <- B_powerRZandZofnat. apply Bexpos. apply inversegeZ.
apply Nat2Z.is_nonneg. unfold wBn. rewrite <- B_powerRZandZofnat. 
apply Bexpos. apply inversegeZ. apply Nat2Z.is_nonneg. ring.
rewrite Zabssgn. rewrite Z.sgn_pos. 
 assert ((wBn k = wBn ((l + (k - l))%nat))%Z).
unfold wBn. replace ((l + (k - l))%nat) with (k%nat). reflexivity.
omega. replace ((Reelc_to_A xc l * wBn k)%Z) with 
((Reelc_to_A xc l * wBn (l + (k - l))%nat)%Z).
 assert ((wBn (l + (k - l))%nat = wBn l%nat * wBn (k - l)%nat)%Z).
unfold wBn. rewrite <- Zpower_exp. rewrite Nat2Z.inj_add. reflexivity.
apply inversegeZ. apply Nat2Z.is_nonneg.
apply inversegeZ. apply Nat2Z.is_nonneg. rewrite H9. replace
((r * ((Reelc_to_A xc k * wBn l - Reelc_to_A xc l * (wBn l * wBn (k - l)%nat)) * 1))%Z) with
((wBn l * ( r * (Reelc_to_A xc k - Reelc_to_A xc l * wBn (k - l)%nat)))%Z). 
replace ((wBn k * wBn l)%Z) with ((wBn l * wBn k)%Z).
apply Zmult_le_compat_l.   
assert ((- (IZR (xc (Z.of_nat l)) + 1) < -(x0 * B_powerRZ (Z.of_nat l)))%R).
apply Ropp_gt_lt_contravar. apply inversegtR. apply H2. apply Zle_0_nat.
replace (Reelc_to_A xc k) with (xc (Z.of_nat k)).
replace (Reelc_to_A xc l) with (xc (Z.of_nat l)).
assert ((- (IZR (xc (Z.of_nat l))) < - (x0 * B_powerRZ (Z.of_nat l)) + 1)%R).
replace ((- IZR (xc (Z.of_nat l)))%R) with (((- IZR (xc (Z.of_nat l))) - 1 + 1)%R).
apply Rplus_lt_compat_r. replace ((- IZR (xc (Z.of_nat l)) - 1)%R) with
((- (IZR (xc (Z.of_nat l)) + 1))%R). assumption. ring. ring. clear H10.
assert ((- IZR (xc (Z.of_nat l)) * IZR (wBn (k - l)%nat) <
 (- (x0 * B_powerRZ (Z.of_nat l)) + 1) * IZR (wBn (k - l)%nat))%R).
apply Rmult_lt_compat_r.  
unfold wBn. rewrite <- B_powerRZandZofnat. apply inverseltR. apply Bexpos. 
apply inversegeZ. apply Nat2Z.is_nonneg. assumption. clear H11. 
assert ((IZR ( xc (Z.of_nat k))  < x0 * B_powerRZ (Z.of_nat k) + 1)%R).
replace (IZR ( xc (Z.of_nat k))) with ((IZR ( xc (Z.of_nat k)) - 1 + 1)%R).
apply Rplus_lt_compat_r. apply H2. apply Zle_0_nat. ring.
assert ((IZR (xc (Z.of_nat k)) + (- IZR (xc (Z.of_nat l)) * IZR (wBn (k - l)%nat))   <
(x0 * B_powerRZ (Z.of_nat k) + 1) + (- (x0 * B_powerRZ (Z.of_nat l)) + 1) * IZR (wBn (k - l)%nat)  )%R).
apply Rplus_lt_compat. assumption. assumption. clear H10 H11.
assert ((IZR r * (IZR (xc (Z.of_nat k)) + - IZR (xc (Z.of_nat l)) * IZR (wBn (k - l)%nat)) <
IZR r * (x0 * B_powerRZ (Z.of_nat k) + 1 + (- (x0 * B_powerRZ (Z.of_nat l)) + 1) * IZR (wBn (k - l)%nat)))%R).
apply inverseltR. apply Rmult_gt_compat_l. apply inversegtR. apply IZR_lt. assumption.
apply inversegtR. assumption. apply le_IZR. rewrite mult_IZR. rewrite minus_IZR. rewrite mult_IZR. 
replace ((IZR r * (IZR (xc (Z.of_nat k)) + - IZR (xc (Z.of_nat l)) * IZR (wBn (k - l)%nat)))%R) with
((IZR r * (IZR (xc (Z.of_nat k)) - IZR (xc (Z.of_nat l)) * IZR (wBn (k - l)%nat)))%R) in H10.
apply Rle_trans with 
((IZR r * (x0 * B_powerRZ (Z.of_nat k) + 1 + (- (x0 * B_powerRZ (Z.of_nat l)) + 1) * IZR (wBn (k - l)%nat)))%R).
apply Rlt_le. assumption. clear H10.
replace (((- (x0 * B_powerRZ (Z.of_nat l)) + 1) * IZR (wBn (k - l)%nat))%R) with
(( -x0 * (B_powerRZ (Z.of_nat l) * IZR (wBn (k - l)%nat)) + IZR (wBn (k - l)%nat))%R).
unfold wBn. rewrite <- B_powerRZandZofnat.
rewrite produitB_powerRZ. replace ((B_powerRZ (Z.of_nat l + Z.of_nat (k - l)))%R) with
((B_powerRZ (Z.of_nat k))%R).
replace ((x0 * B_powerRZ (Z.of_nat k) + 1 + 
(- x0 * B_powerRZ (Z.of_nat k) + B_powerRZ (Z.of_nat (k - l))))%R) with
((B_powerRZ (Z.of_nat (k - l)) + 1)%R). 
replace ((IZR r * (B_powerRZ (Z.of_nat (k - l)) + 1))%R) with
((IZR r + IZR r * B_powerRZ (Z.of_nat (k - l)))%R).
apply Rmult_le_reg_l with (( /B_powerRZ (Z.of_nat (k - l)))%R).
apply Rinv_0_lt_compat. apply inverseltR. apply Bexpos.
replace ((/ B_powerRZ (Z.of_nat (k - l)) * (IZR r + IZR r * B_powerRZ (Z.of_nat (k - l))))%R)
with ((IZR r * / B_powerRZ (Z.of_nat (k - l)) + IZR r)%R).
rewrite <- B_powerRZandZofnat. 
replace ((/ B_powerRZ (Z.of_nat (k - l)) * B_powerRZ (Z.of_nat k))%R) with
((B_powerRZ (Z.of_nat l))%R).
assert ((IZR r <= B_powerRZ (r))%R). unfold B_powerRZ. 
assert (recurrence1 : forall n : nat, (IZR (Z.of_nat n) <= powerRZ (INR B) (Z.of_nat n))%R).
intros n1. induction n1 as [|n1']. simpl. lra.
replace ((S n1')%nat) with ((n1' + 1)%nat). rewrite Nat2Z.inj_add.
rewrite plus_IZR. apply Rle_trans with  ((powerRZ (INR B) (Z.of_nat n1') + IZR (Z.of_nat 1))%R).
apply Rplus_le_compat_r. assumption. replace ((Z.of_nat 1)%Z) with (1%Z).
replace ((Z.of_nat n1' + 1)%Z) with ((Z.succ (Z.of_nat n1'))%Z).
rewrite powerRZ_complements.powerRZ_Zs.
apply Rle_trans with ((powerRZ (INR B) (Z.of_nat n1') * 2)%R).
replace ((powerRZ (INR B) (Z.of_nat n1') * 2)%R) with
 ((powerRZ (INR B) (Z.of_nat n1') + powerRZ (INR B) (Z.of_nat n1'))%R).
apply Rplus_le_compat_l.  rewrite <- powerRZ_O with (INR B).
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. apply Nat2Z.is_nonneg.
ring. apply Rmult_le_compat_l. replace ((powerRZ (INR B) (Z.of_nat n1'))%R) with
((B_powerRZ (Z.of_nat n1'))%R). apply Rlt_le. apply inverseltR. apply Bexpos.
unfold B_powerRZ. reflexivity. apply Rle_trans with (INR 4). unfold INR. lra.
apply le_INR. apply Axiomes.B_sup_4. apply Rgt_not_eq. apply inversegtR. 
apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring. ring.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). apply recurrence1.
rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption.
assert ((IZR r * / B_powerRZ (Z.of_nat (k - l)) <= B_powerRZ r * / B_powerRZ (Z.of_nat (k - l)))%R).
apply Rmult_le_compat_r. apply Rlt_le. apply Rinv_0_lt_compat. apply inverseltR.
apply Bexpos. assumption. replace ((B_powerRZ r * / B_powerRZ (Z.of_nat (k - l)))%R) with
((B_powerRZ (r - Z.of_nat (k - l)))%R) in H11.
apply Rle_trans with (( B_powerRZ (r - Z.of_nat (k - l)) + B_powerRZ r)%R).
apply Rplus_le_compat. assumption. assumption. apply Rle_trans with 
((B_powerRZ r + B_powerRZ r)%R). apply Rplus_le_compat. unfold B_powerRZ.
apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1. 
replace (r%Z) with ((r + (-0))%Z). 
replace ((r + - 0 - Z.of_nat (k - l))%Z) with ((r + - Z.of_nat (k - l))%Z).
apply Zplus_le_compat_l. apply Z.opp_le_mono. rewrite Z.opp_involutive.
rewrite Z.opp_involutive. rewrite <- Nat2Z.inj_0. apply inj_le.
apply INR_le. apply Rplus_le_reg_r with (INR l). rewrite minus_INR.
simpl. replace ((INR k - INR l + INR l)%R) with ((INR k)%R). 
replace ((0 + INR l)%R) with ((INR l)%R). apply NleR. assumption.
ring. ring. assumption. ring. ring.
apply Rle_refl. replace ((B_powerRZ r + B_powerRZ r)%R) with ((2 * B_powerRZ r)%R).
assert ((2 * B_powerRZ r <= INR B * B_powerRZ r)%R). apply Rmult_le_compat_r.
apply Rlt_le. apply inverseltR. apply Bexpos. 
apply Rle_trans with (4%R). lra. replace (4%R) with (INR 4).
apply le_INR. apply Axiomes.B_sup_4. unfold INR. ring.
replace ((INR B * B_powerRZ r)%R) with ((B_powerRZ (r + 1))%R) in H13.
apply Rle_trans with ((B_powerRZ (r + 1))%R). assumption. 
unfold B_powerRZ. apply powerRZ_complements.Rle_powerRZ. apply Bplusgrandque1.
replace (r%Z) with (Z.of_nat (Z.to_nat r)). replace (1%Z) with (Z.of_nat 1).
rewrite <- Nat2Z.inj_add. apply inj_le. apply Nat.max_lub_r with ((x + 1)%nat).
apply inj_ge in H1. apply inverseleZ in H1. apply Nat2Z.inj_le in H1. assumption.
 ring. rewrite Z2Nat.id. reflexivity. apply le_IZR. apply Rlt_le.
apply IZR_lt. assumption. unfold B_powerRZ. replace ((r + 1)%Z) with (Z.succ r).
 rewrite powerRZ_complements.powerRZ_Zs. ring. apply Rgt_not_eq. 
apply inversegtR. apply Lemmes.INR_B_non_nul. unfold Z.succ. reflexivity. ring.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
unfold B_powerRZ. rewrite powerRZ_complements.Rinv_powerRZ. 
rewrite <- powerRZ_add. apply powerRZ_complements.powerRZ_trivial. 
rewrite Nat2Z.inj_sub_max.   replace ((- Z.max 0 (Z.of_nat k - Z.of_nat l) + Z.of_nat k)%Z)
with ((- (Z.max 0 (Z.of_nat k - Z.of_nat l)) + Z.of_nat k)%Z).
replace ((Z.max 0 (Z.of_nat k - Z.of_nat l))%Z) with ((Z.of_nat k - Z.of_nat l)%Z). ring. 
symmetry. apply Z.max_r_iff. 
apply le_IZR. apply Rplus_le_reg_l with (IZR (Z.of_nat l)). 
replace ((IZR (Z.of_nat l) + 0)%R) with ((IZR (Z.of_nat l))%R).
replace ((IZR (Z.of_nat l) + IZR (Z.of_nat k - Z.of_nat l))%R) with
((IZR (Z.of_nat k))%R). apply IZR_le. apply inj_le. assumption.
rewrite minus_IZR. ring. ring. ring.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul.
apply Rgt_not_eq. apply inversegtR. apply Lemmes.INR_B_non_nul. 
apply inversegeZ. apply Nat2Z.is_nonneg.
replace ((/ B_powerRZ (Z.of_nat (k - l)) * (IZR r + IZR r * B_powerRZ (Z.of_nat (k - l)) ))%R) with
((IZR r * / B_powerRZ (Z.of_nat (k - l)) +
 IZR r * (B_powerRZ (Z.of_nat (k - l)) * / B_powerRZ (Z.of_nat (k - l))))%R).
replace ((/ B_powerRZ (Z.of_nat (k - l)) * (IZR r + IZR r * B_powerRZ (Z.of_nat (k - l))))%R) with
((IZR r * / B_powerRZ (Z.of_nat (k - l)) + 
 IZR r *( B_powerRZ (Z.of_nat (k - l)) * / B_powerRZ (Z.of_nat (k - l))))%R).
rewrite Rinv_r. ring. apply Rgt_not_eq. apply Bexpos. ring. ring. ring. ring.
replace ((Z.of_nat l + Z.of_nat (k - l))%Z) with ((Z.of_nat k)%Z). reflexivity.
rewrite Nat2Z.inj_sub. ring. assumption. apply inversegeZ. apply Nat2Z.is_nonneg.
ring. ring. unfold Reelc_to_A. reflexivity.
unfold Reelc_to_A. reflexivity. unfold wBn. apply Zpower_complements.Zpower_le_0.
apply lt_IZR. apply Rlt_le_trans with (4%R). lra.
apply IZR_le. replace (4%Z) with (Z.of_nat 4). apply inj_le.
apply Axiomes.B_sup_4. ring. ring. 
apply eq_IZR.  rewrite mult_IZR. rewrite mult_IZR. 
rewrite mult_IZR. rewrite mult_IZR. 
rewrite minus_IZR. rewrite mult_IZR.
rewrite minus_IZR. rewrite mult_IZR. rewrite mult_IZR. rewrite mult_IZR. ring.
apply eq_IZR. rewrite mult_IZR. rewrite mult_IZR.
apply Rmult_eq_compat_l. apply IZR_eq. unfold wBn. rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_sub.
replace ((Z.of_nat l + (Z.of_nat k - Z.of_nat l))%Z) with ((Z.of_nat k)%Z).
reflexivity. ring. assumption. apply inverseltZ. assumption.
assert (( (x + 1 <= Nat.max (x + 1) (Z.to_nat r + 1)))%nat). apply Nat.le_max_l. assert ((x + 1 <= l)%nat). 
apply Nat.le_trans with ((Nat.max (x + 1) (Z.to_nat r + 1))%nat). assumption. assumption.
apply le_S_gt. replace ((S x)%nat) with ((x + 1)%nat). assumption. ring.
apply le_S_gt. replace ((S x)%nat) with ((x + 1)%nat). 
assert (( (x + 1 <= Nat.max (x + 1) (Z.to_nat r + 1)))%nat). apply Nat.le_max_l.
assert ((x + 1 <= k)%nat). apply Nat.le_trans with ((Nat.max (x + 1) (Z.to_nat r + 1))%nat).
assumption. assumption. assumption. ring.
Qed.



Lemma Hrw_Vmm2 : forall xc : Reelc, 
(PwBn (Reelc_to_A xc))/\(regularwBn (Reelc_to_A xc))  -> encadrement_nat xc.
Proof. intros. inversion H. clear H. unfold PwBn in H0. inversion H0. clear H0.
unfold regularwBn in H1. unfold congruentwBn in H1. 
unfold encadrement_nat. (* C'est faux *)
Admitted.





Definition equalwBn (a1 a2 : A) : Prop :=
forall n : nat, exists N : nat, forall m : nat, 
(m > N)%nat -> (Z.of_nat n * Z.abs (a1 m + - a2 m) <= wBn m)%Z.


Definition psiBn (x : (nat -> Q)) : A :=  (fun (n : nat) => pentiereQ ((inject_Z (wBn n)) * ( x n))       ).


Lemma xnImpsi : forall xc : Reelc, encadrement_nat xc ->
equalwBn (Reelc_to_A xc)  (psiBn (fun (n : nat) => (inject_Z (Reelc_to_A xc n) / inject_Z (wBn n))%Q)).
Proof. intros. unfold equalwBn. intros. unfold psiBn.
unfold encadrement_nat in H. inversion H. clear H.
exists 1%nat. intros.  assert (inject_Z (wBn m) * (inject_Z (Reelc_to_A xc m) / inject_Z (wBn m))
== inject_Z (Reelc_to_A xc m)). rewrite Qmult_div_r. reflexivity.
apply Qnot_eq_sym. apply Qlt_not_eq. replace (0%Q) with (inject_Z 0).
rewrite <- Zlt_Qlt. unfold wBn. apply Z.pow_pos_nonneg. 
rewrite <- Nat2Z.inj_0. apply inj_lt. apply INR_lt. apply Rlt_le_trans with (1%R).
replace (1%R) with (INR 1). apply lt_INR. apply Nat.lt_0_succ.
unfold INR. reflexivity.
apply Bplusgrandque1. apply Zle_0_nat. unfold inject_Z. reflexivity.
assert (pentiereQ (inject_Z (wBn m) * (inject_Z (Reelc_to_A xc m) / inject_Z (wBn m))) =
pentiereQ (  inject_Z (Reelc_to_A xc m)  )  ). apply pentiereequal.
assumption. rewrite H2. 
assert (pentiereQ (inject_Z (Reelc_to_A xc m)) =  Reelc_to_A xc m).
unfold pentiereQ. simpl. rewrite Zdiv_1_r. reflexivity.
rewrite H3. rewrite Z.add_opp_diag_r. rewrite Z.abs_0. rewrite Z.mul_0_r.
apply Z.lt_le_incl. unfold wBn. apply Z.pow_pos_nonneg. 
rewrite <- Nat2Z.inj_0. apply inj_lt. apply INR_lt. apply Rlt_le_trans with (1%R).
replace (1%R) with (INR 1). apply lt_INR. apply Nat.lt_0_succ.
unfold INR. reflexivity. apply Bplusgrandque1. apply Zle_0_nat. 
Qed.
 


End mHRwElie.

(* Local Variables: *)
(* coq-prog-name: "/Users/fuchs/.opam/4.09.0/bin/coqtop" *)
(* coq-load-path: (("../exact-real-arithmetic-homework3" "ExactRealArithmetic") ("../HR" "HR") ("." "Top")) *)
(* suffixes: .v *)
(* End: *)
