Require Import definition.
Require Import Addition.
Require Import Top.HRw_VMM_Elie.
Require Import Psatz.

Open Scope Z_scope.

Module Export TT := mHRwElie(LSw). (* to be checked and maybe fixed *)
Locate Reelc.
(* coq 1 - lemmas *)
Definition pure_vmm (xc:Reelc) : Prop :=
  forall n:Z, 0<=n -> forall k:nat,
      Z.abs(B_powerZ (Z.of_nat k) * xc n - xc (n + (Z.of_nat k))) <= B_powerZ (Z.of_nat k).

Definition pure_vmm' (xc:Reelc) : Prop :=
  forall n:Z, 0<=n -> forall k:Z, 0<=k -> 
      Z.abs(B_powerZ  k * xc n - xc (n +  k)) <= B_powerZ k.

Lemma lemma1 : forall a b c a' b' c' p:R, (a < b < c -> a' < b' < c' -> 0<p -> a'-c*p < b'-b*p < c'-a*p)%R.
Proof.
  intros; nra.
Qed.

Lemma lemma2 : forall x y z:R , (z -1 - (y+1)*x < 0 < z+1 - (y-1)*x)%R -> (-1-x <  x*y -z  < 1+x)%R.
Proof.
  intros; nra.
Qed.

Lemma lemma3 : forall x y:Z, (IZR(-1-y) < IZR x < IZR(1+y))%R ->  (Rabs (IZR x) < (IZR (1+y)))%R.
Proof.
  intros x y Hxy.
  apply Rabs_def1.
  tauto.  
  rewrite <- opp_IZR.
  rewrite Z.opp_add_distr.
  tauto.
Qed.

Lemma lemma4 : forall x y:Z, (Rabs (IZR x) < (IZR (1+y)))%R -> Z.abs x <= y.
Proof.  
intros x y Hxy; rewrite Rabs_Zabs in Hxy.
apply Zlt_succ_le.
apply lt_IZR.
simpl.
rewrite <- Z.add_1_l.
assumption.
Qed.


Check Reelc.
Print Reelc.
Locate Reelc.

Print encadrement_nat.
Locate encadrement_nat.

(* coq 1 *)
Lemma bounds_property_to_pure_vmm :
  forall xc:Reelc, encadrement_nat xc -> pure_vmm xc.
Proof.
unfold encadrement_nat, pure_vmm; intros xc Hxc n Hn k.
destruct Hxc as [x Hx].
generalize (Hx n Hn); intros Hxn.
assert (Hnk : 0<= (n+Z.of_nat k)%Z) by omega.
generalize (Hx (n+Z.of_nat k) Hnk); intro Hxnk.
apply lemma4.
apply lemma3.
assert (Hpos: (0 < IZR (B_powerZ (Z.of_nat k)))%R).
rewrite inverseB_power.
apply Bexpos; omega.
omega.
generalize (lemma1 _ _ _ _ _ _ (IZR (B_powerZ (Z.of_nat k))) Hxn Hxnk Hpos); intros Hl1.
replace (x * B_powerRZ (n + Z.of_nat k) - x * B_powerRZ n * IZR (B_powerZ (Z.of_nat k)))%R with 0%R in Hl1.
generalize (lemma2 _ _ _ Hl1); intros Hl2.
rewrite minus_IZR.
rewrite minus_IZR.
rewrite mult_IZR.
rewrite plus_IZR.
assumption.

rewrite Rmult_assoc.
rewrite <- Rmult_minus_distr_l.
rewrite inverseB_power.
rewrite produitB_powerRZ.
ring. 
omega.
Qed.

(* coq 2 - lemmas *)
Lemma exists_le : forall a b:nat, (a<=b -> exists n:nat, b=a+n)%nat.
Proof.
intros.  
exists (b-a)%nat.
ring_simplify.
rewrite le_plus_minus_r.
reflexivity.
assumption.
Qed.
                                                                                                     
Lemma cauchy_equiv :  forall r b, forall u v:nat->Z,
      (forall k l:nat, (k>=b)%nat -> (l>=b)%nat -> r*(Z.abs (u k * v l - u l * v k)) <= (v k) * (v l)) <-> forall n k:nat, (n>=b)%nat -> (r*(Z.abs (u n * v (n+k)%nat - u (n+k)%nat * v n)) <= (v n) * (v (n+k)%nat)).
Proof.
intros.
split.
intros.
apply H; omega.
intros.
destruct (Nat.lt_ge_cases k l) as [Hkl | Hkl].
assert (H':(k<=l)%nat) by omega.
destruct (exists_le _ _ H') as [p Hp].
rewrite Hp.
apply H; assumption.
destruct (exists_le _ _ Hkl) as [p Hp].
rewrite Hp.
rewrite (Z.mul_comm (v (l+p)%nat)).
assert (hyp:forall a b, Z.abs (a-b) = Z.abs (b-a)).
intros; rewrite <- Z.abs_opp.
apply f_equal; omega.
rewrite hyp.
apply H; assumption.
Qed.

Lemma wBn_add : forall x y, wBn (x+y)%nat = wBn x * wBn y.
Proof.
intros; unfold wBn.
rewrite <- Zpower_exp.
rewrite <- Nat2Z.inj_add.
reflexivity.
omega.
omega.
Qed.

Lemma wBn_pos : forall k, 0 <= wBn k.
Proof.
  intros.
  apply Zpower_complements.Zpower_le_0.
  replace 0 with (Z.of_nat 0) by reflexivity.
  apply inj_lt.
  generalize Axiomes.B_sup_4; omega.
Qed.

Lemma Zpow_BpowerZ : forall n, Z.of_nat B ^ Z.of_nat n = B_powerZ (Z.of_nat n).
Proof.
  intros; reflexivity.  
Qed.

Lemma ln_power_aux : forall x:R, forall n:nat, (0 < x)%R -> (ln (x ^ n) = (IZR (Z.of_nat n)) * ln x)%R.
Proof.
intros; induction n.
simpl.
ring_simplify.
rewrite ln_1.
reflexivity.
simpl.
rewrite ln_mult.
rewrite IHn.
rewrite Zpos_P_of_succ_nat.
rewrite succ_IZR.
rewrite Rmult_plus_distr_r.
ring_simplify.
reflexivity.
assumption.
apply pow_lt; assumption.
Qed.

Lemma ln_Rpower : forall x:R, (0<x)%R -> forall y:Z, 0<=y -> ln (powerRZ x y) = (IZR y * ln x)%R.
Proof.
  intros x Hx y Hy; induction y.
  simpl.
  rewrite ln_1.
  ring_simplify.
  reflexivity.
  simpl.
  rewrite (ln_power_aux x (Pos.to_nat p)).
  rewrite positive_nat_Z.
  reflexivity.
  assumption.
  generalize (Zlt_neg_0 p); omega.
Qed.

Lemma nra_lemma1 : forall x y:R, (1< y -> 0<=x -> x <= x*y)%R.
Proof.
intros;nra.
Qed.

Lemma Zle_Zof_nat_Z_to_nat: forall x:Z, x <= Z.of_nat (Z.to_nat x).
Proof.
intros.
destruct (Zdec_complements.Zlt_le_ind 0 x) as [Hd | Hd].
destruct x.
omega.
omega.
omega.
rewrite Z2Nat.id; omega.
Qed.

Lemma exp_le : forall x y:R, (x <= y)%R -> (exp x <= exp y)%R.
Proof.
  intros x y Hxy.
  destruct Hxy as [Hxy | Hxy].
  left.
  apply exp_increasing; assumption.
  rewrite Hxy; apply Rle_refl.
Qed.  

Lemma ln_le : forall x y:R, (0<x)%R -> (x <= y)%R -> (ln x <= ln y)%R.
Proof.
  intros x y Hx0 Hxy.
  destruct Hxy as [Hxy | Hxy].
  left.
  apply ln_increasing; assumption.
  rewrite Hxy; apply Rle_refl.
Qed.

Lemma ln_B : forall n:nat, (4<=n)%nat ->  (1<ln (IZR (Z.of_nat n)))%R.
Proof.
  intros.
  apply exp_lt_inv.
  rewrite exp_ln.
  apply Rle_lt_trans with 3%R.
  apply exp_le_3.
  apply IZR_lt.
  omega.
  apply IZR_lt.
  omega.
Qed.

Lemma witness_N_ok : forall n:nat, forall r:Z, (0<r)%Z-> (n >= (Z.abs_nat ((Int_part (Rabs (ln (IZR r))))))+1)%nat -> r <= B_powerZ (Z.of_nat n).
Proof.
intros.
apply le_IZR.
rewrite <- exp_ln.
rewrite <- (exp_ln (IZR r)).
apply Rle_trans with (exp (Rabs (ln (IZR r)))).
apply exp_le.
apply Rle_abs.
apply exp_le.

rewrite <- Zpow_BpowerZ.
rewrite <- pow_IZR.
rewrite pow_powerRZ.
rewrite ln_Rpower.

apply Rle_trans with (IZR (Z.abs (Int_part (Rabs (ln (IZR r)))))+1)%R.
destruct (base_Int_part (Rabs (ln (IZR r)))) as [Hb1 Hb2].
rewrite <- Rabs_Zabs.
replace (Rabs (IZR (Int_part (Rabs (ln (IZR r)))))) with (IZR (Int_part (Rabs (ln (IZR r))))).
nra.
rewrite (Rabs_pos_eq (IZR (Int_part (Rabs (ln (IZR r)))))).
reflexivity.
apply IZR_le.
apply Z.ge_le.
apply Int_part_0.
apply Rle_ge.
apply Rabs_pos.
apply Rle_trans with (IZR (Z.of_nat n)).
rewrite <- plus_IZR.
apply IZR_le.
rewrite <- Nat2Z.inj_abs_nat.
omega.
assert (1<ln (IZR (Z.of_nat B)))%R.
apply ln_B.
apply Axiomes.B_sup_4.

apply nra_lemma1.
assumption.
apply IZR_le; omega.
apply IZR_lt.
rewrite <- Nat2Z.inj_0.
apply inj_lt.
generalize Axiomes.B_sup_4; omega.
omega.
apply IZR_lt; assumption.
rewrite inverseB_power.
apply Bexpos. 
omega.
Qed.

(* coq 2 *)
Lemma pure_vmm_to_regular :
  forall xc:Reelc, pure_vmm xc -> regularwBn (Reelc_to_A xc).
Proof.
unfold encadrement_nat, pure_vmm, regularwBn, congruentwBn; intros.
exists ((Z.abs_nat ((Int_part (Rabs (ln (IZR r))))))+1)%nat.
intros k Hk l Hl.
rewrite Z.sub_0_r.
rewrite Z.sub_0_r.
revert k l  Hk Hl.
apply cauchy_equiv.
intros n k Hn.
rewrite wBn_add.
replace (Reelc_to_A xc n * (wBn n * wBn k)) with ((Reelc_to_A xc n * wBn k) * wBn n) by ring.
rewrite <- Z.mul_sub_distr_r.
rewrite Zabs_complements.Zabs_mult.
rewrite (Z.abs_eq (wBn n)).
rewrite (Z.mul_assoc).
rewrite (Z.mul_assoc).
rewrite (Z.mul_comm (wBn n * wBn n) (wBn k)).
rewrite (Z.mul_assoc).
apply Z.mul_le_mono_pos_r.
unfold wBn.
apply Z.pow_pos_nonneg.
replace 0 with (Z.of_nat 0) by reflexivity.
apply inj_lt.
generalize Axiomes.B_sup_4; omega.
omega.
apply Z.le_trans with (r*B_powerZ (Z.of_nat k)).
apply Z.mul_le_mono_nonneg_l.
omega.
unfold Reelc_to_A, wBn.
rewrite Z.mul_comm.
rewrite Nat2Z.inj_add.
apply H.
apply Zle_0_nat.
rewrite Z.mul_comm.
apply Z.mul_le_mono_nonneg_l.
apply wBn_pos.
apply witness_N_ok; assumption. 
apply wBn_pos. 
Qed.

(* coq 3 *)
Lemma alt_encadrement_nat : forall t z v,
    (t - v < z < t + v)%R <-> (Rabs (z - t) < v)%R.
Proof.
  intros;split; intros.
apply  (Rabs_def1 (z-t) v); nra.
lapply  (Rabs_def2 (z-t) v); [nra | assumption].
Qed.

Lemma alt2_encadrement_nat : forall t z,
    (-t < z < t )%R <-> (Rabs (z) < t)%R.
Proof.
  intros;split; intros.
apply  (Rabs_def1 z); nra.
split; apply  (Rabs_def2 z);nra. 
Qed.

Lemma alt_encadrement_nat_1 : forall t z v,
    (t - v < z < t + v)%R -> (Rabs (z - t) < v)%R.
Proof.
  intros; apply alt_encadrement_nat; assumption.
Qed.

Lemma alt_encadrement_nat_2 : forall t z v,
    (Rabs (z - t) < v)%R -> (t - v < z < t + v)%R .
Proof.
  intros; apply alt_encadrement_nat; assumption.
Qed.

Lemma pure_vmm_to_bounds_property :
  forall xc:Reelc, pure_vmm xc -> encadrement_nat xc.
Proof.
intros xc Hxc; generalize (pure_vmm_to_regular xc Hxc).
unfold regularwBn, congruentwBn; intros Hr.
simpl in *.
unfold encadrement_nat.
assert (x:R) by admit (* Cauchy limit *).
exists x.

intros.
apply alt_encadrement_nat.

Admitted.

(* coq 4 *)
Definition encadrement (xc : Reelc) (x : R) : Prop :=
  forall n : nat, (IZR (xc (Z.of_nat n)) - 1 < x * B_powerRZ (Z.of_nat n) <
                                                     IZR (xc (Z.of_nat n)) + 1)%R.
Print encadrement_nat.

Definition equal_vmm(xc1 xc2 : Reelc) : Prop :=
  exists x : R, encadrement xc1 x /\ encadrement xc2 x.

Definition Badic_equiv (xc yc:Reelc) := (exists k: Z, forall n: Z, 0<= n -> Z.abs(xc n - yc n) <= k).

(* coq 5 - lemmas *)
Lemma ln_B_0 : (0 < ln (INR B))%R.
Proof.
  rewrite <- ln_1.
  apply ln_increasing.
  nra.
  rewrite INR_IZR_INZ.
  apply IZR_lt.
  generalize Axiomes.B_sup_4; omega.
Qed.

Lemma Rdiv_Rmult_id : forall r t, (0<t)%R -> ((r/t)*t=r)%R.
Proof.
  intros; field.
  nra.  
Qed.

Lemma base_Int_part_aux :
  forall r : R, (r <= (IZR (Int_part r)) +1)%R.
Proof.
  intros; generalize (base_Int_part r).
nra.
Qed.

Lemma Zabs_x : forall x:Z, x <= Z.abs x.
Proof.
intros x.
destruct (Z.le_decidable x 0).
rewrite Z.abs_neq; omega.
rewrite Z.abs_eq; omega.
Qed.

Lemma Requal : forall x y k, (forall n:Z, (0<=n)%Z ->
    (Rabs (x - y) < IZR (k + 2) * B_powerRZ (- n)))%R -> x=y.
Proof.
  intros.
  apply cond_eq.
  intros.
  pose (N:= Z.abs ((Int_part ((ln ((IZR (k+2)%Z)/eps)%R)/ln (IZR (Z.of_nat B)))%R)+1)).
  assert (HN : 0<= N) by apply Z.abs_nonneg.
  generalize (H N HN); intros Hyp.
  apply Rlt_le_trans with (IZR (k + 2) * B_powerRZ (- N))%R.
  assumption.
  clear Hyp H.

  apply Rmult_le_reg_r with (r:= B_powerRZ (N)%R).
  apply Bexpos.
  rewrite Rmult_assoc.
  rewrite produitB_powerRZ.
  ring_simplify (-N + N).
  simpl.
  ring_simplify.
  apply Rmult_le_reg_l with (r:= (/ eps)%R).
  apply Rinv_0_lt_compat; assumption.
  rewrite <- Rmult_assoc.
  rewrite Rinv_l by nra.
  ring_simplify.
  rewrite Rmult_comm.
  replace (IZR (k + 2) * / eps)%R with ((IZR (k + 2))/ eps)%R by nra.
  destruct (total_order_T (IZR (k+2) / eps) 0%R) as [[Hneg | Hzero] | Hpos].
  apply Rle_trans with 0%R.
  nra.
  apply Rlt_le; apply Bexpos.
  rewrite Hzero.
  apply Rlt_le; apply Bexpos.

  rewrite <- exp_ln by apply Bexpos.
  rewrite <- (exp_ln ((IZR (k+2))/ eps)) by nra.
  apply exp_le.
  
  unfold B_powerRZ.
  rewrite ln_Rpower.
  unfold B_powerRZ.
  apply Rle_trans with ((ln (IZR (k + 2) / eps) / (ln (INR B))) * (ln (INR B)))%R.
  rewrite Rdiv_Rmult_id.
  nra.
  apply ln_B_0.
  apply Rmult_le_compat_r.
  apply Rlt_le.
  apply ln_B_0.
  eapply Rle_trans.
  apply base_Int_part_aux.
  rewrite <- plus_IZR.
  apply IZR_le.
  unfold N.
  rewrite INR_IZR_INZ.
  apply Zabs_x.
  apply Lemmes.INR_B_non_nul.
  unfold N.
  apply Z.abs_nonneg.
Qed.

(* coq 5 *)
Lemma bounded_difference_implies_equal_vmm: (* uses total_order_T *)
  forall xc yc: Reelc, encadrement_nat xc ->
                       encadrement_nat yc ->
                       Badic_equiv xc yc ->
                       (*(exists k: Z, forall n: Z, Z.abs(xc n - yc n) <= k) *)
                       equal_vmm xc yc.
Proof.
(*  Locate Cauchy_crit_series.*)
  unfold encadrement_nat, equal_vmm, encadrement,Badic_equiv; intros xc yc Hxc Hyc Hk.
  destruct Hxc as [x Hxc].
  destruct Hyc as [y Hyc].
  assert (Hdiff:(forall n:Z,  (0<=n)%Z -> (IZR (xc n) - (IZR (yc n)) - 2) < (x - y) * B_powerRZ n < (IZR (xc n)  - (IZR (yc n))) + 2)%R)
    by (intros n Hn; generalize (Hxc n Hn); generalize (Hyc n Hn); intros Hxcn Hycn; split; nra).
  destruct Hk as [k Hk].
  assert (Habs:(forall n:Z, (0<=n)%Z -> Rabs ((x - y) * B_powerRZ n) < (IZR (Z.abs ((xc n) - (yc n))+2)))%R).
  
  intros n Hn.
  rewrite plus_IZR.
rewrite abs_IZR.
destruct (total_order_T ((x - y) * B_powerRZ n) 0%R) as [[Hneg | Hzero] | Hpos].
rewrite Rabs_left.
destruct (Hdiff n) as [Hd1 Hd2].
assumption.
assert (- ((x - y) * B_powerRZ n) < (IZR (yc n) - IZR (xc n)) + 2)%R by nra.
apply Rlt_le_trans with (IZR (yc n) - IZR (xc n) + 2)%R.
assumption.
apply Rplus_le_compat_r.
rewrite minus_IZR.
rewrite Rabs_minus_sym.
apply Rle_abs.
assumption.

rewrite Hzero.
rewrite Rabs_R0.
assert (0<=Rabs (IZR (xc n - yc n)))%R by apply Rabs_pos.
nra.
rewrite Rabs_right.
destruct (Hdiff n Hn) as [Hd1 Hd2].
apply Rlt_le_trans with (IZR (xc n) - IZR (yc n) + 2)%R.
assumption.
rewrite minus_IZR.
assert ((IZR (xc n) - IZR (yc n)) <= Rabs (IZR (xc n) - IZR (yc n)))%R by apply Rle_abs.
nra.
nra.
assert (Hconcl :(forall n:Z, (0<= n)%Z -> Rabs (x-y) < IZR (k+2)%Z * B_powerRZ (-n))%R).
intros n Hn.
generalize (Habs n Hn); intros.
apply Rmult_lt_reg_r with (B_powerRZ n)%R.
apply Bexpos.
rewrite Rmult_assoc.
rewrite produitB_powerRZ.
ring_simplify (-n + n).
simpl.
ring_simplify.
apply Rlt_le_trans with (IZR (Z.abs (xc n - yc n) + 2))%R.
rewrite Rabs_mult in H.
rewrite (Rabs_right (B_powerRZ n)) in H.
assumption.
apply Rle_ge; apply Rlt_le; apply Bexpos. 
apply IZR_le.
apply Z.add_le_mono_r.
apply Hk.
assumption.
assert (Hequal: x=y) by (apply Requal with (k:=k) ; try apply Hconcl).
exists x.
split.
intros.
apply (Hxc (Z.of_nat n)).
apply Zle_0_nat.
intros.
rewrite Hequal.
apply (Hyc (Z.of_nat n)).
apply Zle_0_nat.
Qed.

(* coq 6 *) (* changed succ 0%Z into (Z.succ 0) *)
Lemma lemma5 : forall x y:R, ((x-1)- (y+1) < 0 < (x+1 - (y-1))  -> -2 < x -y < 2)%R.
Proof.
intros; nra.  
Qed.

Lemma lemma6 : forall x:Z, (-2 < IZR x < 2)%R -> (-1 <= x <= 1)%Z.
Proof.
  intros.
  assert (-2< x < 2)%Z.
  destruct H; split; apply lt_IZR; assumption.
  omega.
Qed.

Lemma equal_vmm_implies_tight : forall xc yc : Reelc,
    equal_vmm xc yc -> forall n : Z, 0<=n -> Z.abs (xc n - yc n) <= 1.
(* statement is fixed: n >=  0 required *)
Proof.
  unfold equal_vmm, encadrement; intros xc yc Heq.
  destruct Heq as [x [Hx Hy]].
intros n.
generalize (Hx (Z.abs_nat n)); intros Hxn.
generalize (Hy (Z.abs_nat n)); intros Hyn.
generalize (lemma1 _ _ _ _ _ _ 1%R Hxn Hyn Rlt_0_1); intros.
replace (x * B_powerRZ (Z.of_nat (Z.abs_nat n)) - x * B_powerRZ (Z.of_nat (Z.abs_nat n)) * 1)%R with 0%R in H by ring.
rewrite Rmult_1_r in H.
rewrite Rmult_1_r in H.
assert (H2: (-2 < (IZR (yc (Z.of_nat (Z.abs_nat n)))) - (IZR (xc (Z.of_nat (Z.abs_nat n)))) < 2)%R) by (apply lemma5; assumption).
apply mBridges2_LS.between_abs2.
omega.
apply lemma6.
rewrite Nat2Z.inj_abs_nat in H2.
rewrite Z.abs_eq in H2.
rewrite minus_IZR.
nra.
assumption.
Qed.

(* coq 7 *)
Theorem equal_vmm_iff_bounded_difference :
  forall xc yc: Reelc, equal_vmm xc yc <->
  pure_vmm xc /\ pure_vmm yc /\ exists k: Z, forall n: Z, 0<=n -> Z.abs(xc n - yc n) <= k.
Proof.
intros xc yc; split.
intros Hequal.
split.
apply bounds_property_to_pure_vmm.
destruct Hequal as [x [Hx Hx']].
unfold encadrement, encadrement_nat in *.
exists x.
intros.
rewrite <- (Z2Nat.id n).
apply Hx.
assumption.
split.
apply bounds_property_to_pure_vmm.
destruct Hequal as [x [Hx Hx']].
unfold encadrement, encadrement_nat in *.
exists x.
intros.
rewrite <- (Z2Nat.id n).
apply Hx'.
assumption.

exists 1.
apply equal_vmm_implies_tight; assumption.

intros (Hxc, (Hyc, Hex)).
unfold pure_vmm in Hxc, Hyc.
apply bounded_difference_implies_equal_vmm.
apply pure_vmm_to_bounds_property.
unfold pure_vmm.
intros; apply Hxc; assumption.
apply pure_vmm_to_bounds_property.
unfold pure_vmm.
intros; apply Hyc; assumption.

unfold Badic_equiv.
destruct Hex as [k Hk].
exists k; intros; apply Hk.
assumption.
Qed.
Search PwBn.
(* coq 8 *) (*En partant du travail d’Élie, il faut extraire le réel de la propriété encadrement_nat et montrer son unicité.*)

(* coq 9 *) (* L’égalité x = θ(xn) correspond à la propriété encadrement xc x *)

(* coq 10 *)
Definition le_vmm (xc yc : Reelc): Prop :=
  exists k: nat, forall n: Z, 0<= n -> xc n <= yc n + Z.of_nat k.

(* coq 11 *)
Lemma le_vmm_well_defined :
  forall x y: R, forall xc yc: Reelc,
    encadrement xc x -> encadrement yc y -> (x <= y)%R -> le_vmm xc yc.
Proof.
  unfold encadrement, le_vmm; intros.
  exists 1%nat.
  intros n Hn.
  assert (IZR (xc n - yc n) -2 < (x-y)*B_powerRZ n)%R.
  rewrite minus_IZR.
  rewrite Rmult_comm.
  rewrite Rmult_minus_distr_l.
  rewrite (Rmult_comm _ x).
  rewrite (Rmult_comm _ y).

destruct (H (Z.to_nat n)); destruct (H0 (Z.to_nat n)); rewrite Z2Nat.id in * by assumption.
nra.
assert ((IZR (xc n - yc n) - 2) < 0)%R.
apply Rlt_le_trans with ((x - y) * B_powerRZ n)%R.
assumption.
replace 0%R with (0* B_powerRZ n)%R by ring.
apply Rmult_le_compat_r.
apply Rlt_le; apply Bexpos.
nra.

assert (IZR (xc n - yc n) < 2)%R by nra.
replace 2%R with (IZR 2) by ring.
generalize (lt_IZR _ _ H4); intros.
simpl; omega.
Qed.
Print encadrement_nat.
(* coq 12 *) (* =Bn correspond à equalwBn. *)

(* coq 13 *)

Lemma is_HRBn_Reelc : forall xc: Reelc, encadrement_nat xc (* !!!*) -> PwBn (Reelc_to_A  xc).
Proof.
  intros xc Hxc.
  destruct (Hrw_Vmm xc Hxc).
  assumption.
Qed.

(* coq 14 *)

Fixpoint mp (P:nat->Prop)
         (H0:P 0%nat) (H1:P 1%nat) (H2:P 2%nat) (HR:(forall n:nat, P n -> P (3+n)%nat))
         (n:nat) {struct n} : P n :=
  match n with
    O => H0
  | S p =>
    match p with O => H1
            | S q =>
              match q with O => H2
                      | S r => HR r (mp P H0 H1 H2 HR r)
              end
    end
  end.
    

  Lemma equalwBn_equal_vmm : forall xc yc: Reelc, equalwBn (Reelc_to_A xc) (Reelc_to_A yc) <-> equal_vmm xc yc.
Proof.

Search equal_vmm.
intros; split; intros.  Check bounded_difference_implies_equal_vmm.
apply bounded_difference_implies_equal_vmm.
unfold encadrement_nat.
3: unfold Badic_equiv.
(*
intros; split.

  intros Hxy.
destruct (equal_vmm_iff_bounded_difference xc yc) as [Ha Hb].  
apply Hb.
repeat split.

Search pure_vmm.
apply bounds_property_to_pure_vmm.
unfold encadrement_nat.
 
(* preuve 2 *)



apply (equal_vmm_iff_bounded_difference xc yc).
unfold pure_vmm; repeat split.

apply bounded_difference_implies_equal_vmm.
unfold encadrement_nat.

admit.
intros Hxy.
generalize (equal_vmm_implies_tight xc yc Hxy); intros Hb.
unfold equalwBn; intros.
exists n%nat.
intros.
unfold Reelc_to_A.
assert (Hm:(0<=Z.of_nat m)%Z) by omega.
generalize (Hb (Z.of_nat m) Hm); intros.
apply Z.le_trans with ((Z.of_nat n)*1)%Z.
apply Zmult_le_compat_l.
assumption. 
omega.
ring_simplify.
apply Z.le_trans with (Z.of_nat m).
apply inj_le; omega.
Check Z.pow_gt_lin_r.
apply Z.lt_le_incl.
apply Z.pow_gt_lin_r.
replace 1 with (Z.of_nat 1) by reflexivity.
apply inj_lt.
generalize Axiomes.B_sup_4; omega.
omega.
*)
Admitted.

(* coq 15 *)
Lemma identity_VMM_HR_well_defined:
forall xc yc:Reelc, equal_vmm xc yc -> equalwBn (Reelc_to_A xc) (Reelc_to_A yc).
Proof.
  intros; apply equalwBn_equal_vmm; assumption.
Qed. (* relevance ? *)

(* coq 16 *)
Lemma identity_VMM_HR_is_injective:
  forall xc yc:Reelc, equalwBn (Reelc_to_A xc) (Reelc_to_A yc) -> equal_vmm xc yc.
Proof.
  intros; apply equalwBn_equal_vmm; assumption.
Qed.

(*then morphims properties *)
Definition A_to_Reelc a := fun (n: Z) =>
  match n with
  | Zpos p => a (Z.to_nat n)
  | Z0 => a 0%nat
  | _ => 0%Z
  end.

Print A_to_Reelc.

(* one must set up the configuration where \omega = B^n *)
Lemma add_morphism : forall x y: LSw.A, equalw (Reelc_to_A (addition_reelc (A_to_Reelc x) (A_to_Reelc y))) (LSw.plusA x y).
Proof.
unfold equalw.
intros x y N.
Search nat R.
Check Int_part.
pose (t:= Z.abs_nat (Int_part ((ln (INR N)+ln(INR (5/2)))/(ln (INR B)))%R)).
exists t.
intros n.
Print addition_reelc.
Search addition_reelc.

Search addition_reelc.
Admitted.

Lemma mult_morphism : forall x y: LSw.A, equalw (Reelc_to_A (multiplication_reelc (A_to_Reelc x) (A_to_Reelc y) None None)) (LSw.multA x y).
Proof.


Admitted.

(* to be added here (p. 15 and p. 16) *)

(* coq 17 *)
Definition close (oc xc: Reelc) (n: nat) (B: nat): Prop :=
  exists n0: Z, forall k: Z, k >= n0 -> (Z.of_nat n) * Z.abs (oc k - xc k) < wBn (Z.to_nat k).

(*La fonction equalwBn d’Élie se définit à partir de close par *)

(*Definition equalwBn' (x y: LSw.A): Prop :=
  forall n: nat, close (A_to_Reelc x)  (A_to_Reelc y) n B.*)

Lemma A_to_Reelc_simpl : forall x m, A_to_Reelc x (Z.of_nat m) = x m.
Proof.
intros.
induction m.
simpl; reflexivity.
simpl; rewrite SuccNat2Pos.id_succ; reflexivity.
Qed.

Lemma A_to_Reelc_pos : forall x k, (0<=k)%Z -> (A_to_Reelc x k = x (Z.to_nat k)).
Proof.
intros x k; destruct k; simpl.
reflexivity.
reflexivity.
intros; generalize (Zlt_neg_0 p); omega. 
Qed.

Theorem  equalw_equiv_always_close:
  forall (x y : LSw.A), equalwBn x y <->
        forall n: nat, close (A_to_Reelc x) (A_to_Reelc y) n B.
Proof.
unfold equalwBn, close; intros x y; split; intros Hxy.
(* 1 *)
intros n.
destruct (Hxy (B*n)%nat) as [N HN].
exists ((Z.of_nat N)+1)%Z.
intros k Hk.
apply Zmult_lt_reg_l with (Z.of_nat B).
replace 0 with (Z.of_nat 0) by reflexivity.
apply inj_lt.
generalize Axiomes.B_sup_4; omega.
unfold wBn.
rewrite <- Z.pow_succ_r.
rewrite Z.mul_assoc.
apply Z.le_lt_trans with (Z.of_nat B ^ (Z.of_nat (Z.to_nat k))).
rewrite <- Nat2Z.inj_mul.
assert (hyp:(Z.to_nat k > N)%nat).
rewrite <- (Nat2Z.id N).
unfold gt.
apply Z2Nat.inj_lt; omega.

rewrite A_to_Reelc_pos by omega.
rewrite A_to_Reelc_pos by omega.
apply HN; omega.
rewrite Z.pow_succ_r.
rewrite Z2Nat.id by omega.
replace (Z.of_nat B ^ k) with (1 * (Z.of_nat B ^ k)) at 1 by ring.
apply Zmult_lt_compat_r.
apply Z.pow_pos_nonneg.
replace 0 with (Z.of_nat 0) by reflexivity.
apply inj_lt.
generalize Axiomes.B_sup_4; omega.
omega.
replace 1 with (Z.of_nat 1) by reflexivity.
apply inj_lt.
generalize Axiomes.B_sup_4; omega.
omega.
omega.

(* 2 *)
intros n.
destruct (Hxy n) as [N HN].
exists (Z.to_nat (Z.abs N)).
intros.
apply Z.lt_le_incl.
rewrite <- (Nat2Z.id m).

assert (HN': Z.of_nat m >=N).
apply Z.le_ge.
apply Z.le_trans with (Z.abs N).
apply Zabs_x.
rewrite <- (Nat2Z.id m) in H.
unfold gt in H.
apply Z2Nat.inj_lt in H.
omega.
apply Z.abs_nonneg. 
omega.
generalize (HN (Z.of_nat m) HN').
do 2 rewrite A_to_Reelc_simpl.
rewrite Nat2Z.id.
intros; assumption.
Qed.

(* coq 18 *)
Definition monster1 (B: nat): Reelc :=
  fun (n: Z) => Z.pow (- (Z.of_nat B))  n.

Lemma HRw_much_bigger_VMM :
  forall a, regularwBn a -> not (close (monster1 B) (A_to_Reelc a) 2 B).
Proof.
Admitted.

(* coq 19 *)
Lemma VMM_dense :
  forall a,  regularwBn a ->
               forall n:nat, exists xc: Reelc, close (A_to_Reelc a) xc n B.
Proof.
Admitted.

(* Local Variables: *)
(* coq-prog-name: "/Users/fuchs/.opam/4.09.0/bin/coqtop" *)
(* coq-load-path: (("../exact-real-arithmetic-homework3" "ExactRealArithmetic") ("../HR" "HR") ("." "Top")) *)
(* suffixes: .v *)
(* End: *)