module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeEndpoints
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusActions

/-!
# The nonbinary pure opposite Suzuki equation

For a nonbinary coefficient field, the endpoint seed is transported by the
normalized torus. Additivity in the right endpoint then removes the residual
seed coefficient, using that a field of characteristic two and size greater
than two has a coefficient outside `{0, 1}`. Carter-coordinate injectivity
extracts the resulting endpoint identity. This is the native pure main-curve
equation in Fong--Seitz II (1974), (10.23)--(10.26).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "M" a:max y:max => (synchronizedSuzukiMixed Q split c a 0 y 0 : X ⧸ Q.D)

private theorem simple_suzuki (a b : CoefficientField m) :
    S 0 a b = (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_quartet_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

private theorem transported_seed (ε : CoefficientField m)
    (hε : M 1 1 = S 1 1 (1+ε)*L 3 1*S 3 1 ε)
    (a y : CoefficientField m) (ha : a ≠ 0) (hy : y ≠ 0) :
    M a y = S 1 (a*titsEnd m y) ((a*titsEnd m y)*titsEnd m (a*titsEnd m y)*(1+ε)) *
      L 3 ((a*titsEnd m a)*(y*titsEnd m y)) *
        S 3 (titsEnd m a*y) ((titsEnd m a*y)*titsEnd m (titsEnd m a*y)*ε) := by
  have hta : titsEnd m a ≠ 0 := (map_ne_zero (titsEnd m)).mpr ha
  let A : (CoefficientField m)ˣ := Units.mk0 a ha
  let Y : (CoefficientField m)ˣ := Units.mk0 y hy
  let t : TorusParameter m := (Y/A,A)
  have h0 : (TorusCharts.character t (.inr 0) : CoefficientField m) = a := by
    simp only [TorusCharts.character_quartet,t,Matrix.cons_val_zero,Units.val_mk0,A]
  have h2 : (TorusCharts.character t (.inr 2) : CoefficientField m) = y := by
    simp only [TorusCharts.character_quartet,t,Matrix.cons_val,Fin.isValue,
      Units.val_mul,Units.val_div_eq_div_val,A,Y,Units.val_mk0]
    field_simp [ha,hta]
  have hpow (x : CoefficientField m) : x^(2*2^m) = titsEnd m x := by
    rw [titsEnd_apply,pow_succ]
    congr 1
    omega
  have h1 : (TorusCharts.character t (.inr 1) : CoefficientField m) = a*titsEnd m y := by
    simp only [TorusCharts.character_quartet,t,Matrix.cons_val,Fin.isValue,
      Units.val_mul,Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,A,Y,Units.val_mk0]
    simp only [pow_add,pow_one,hpow,map_div₀]
    field_simp [ha,hta]
  have h3 : (TorusCharts.character t (.inr 3) : CoefficientField m) = titsEnd m a*y := by
    simp only [TorusCharts.character_quartet,t,Matrix.cons_val,Fin.isValue,
      Units.val_mul,Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,A,Y,Units.val_mk0]
    simp only [pow_add,pow_one,hpow]
    field_simp [ha,hta]
  have hp : (TorusCharts.character t (.inl 3) : CoefficientField m) =
      (a*titsEnd m a)*(y*titsEnd m y) := by
    simp only [TorusCharts.character_pair,t,Matrix.cons_val,Fin.isValue,
      Units.val_mul,Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,A,Y,Units.val_mk0]
    rw [show 2+4*2^m = 2+(2*2^m)*2 by omega]
    simp only [pow_add,pow_one,pow_mul,hpow,map_div₀]
    field_simp [ha,hta]
  let f := MulAut.conj (normalizedSynchronizedTorus Q split c t)
  have hq (i : Fin 4) (u v : CoefficientField m) :
      f (S i u v) = S i ((TorusCharts.character t (.inr i) : CoefficientField m)*u)
        ((TorusCharts.character t (.inr i) : CoefficientField m)*
          titsEnd m (TorusCharts.character t (.inr i))*v) :=
    normalizedSynchronizedTorus_quartet Q split c t i u v
  have hl (u : CoefficientField m) : f (L 3 u) = L 3 (((a*titsEnd m a)*(y*titsEnd m y))*u) := by
    simpa only [f,MulAut.conj_apply,hp] using normalizedSynchronizedTorus_pair Q split c t 3 u
  have h := congrArg f hε
  rw [synchronizedSuzukiMixed_val,←simple_suzuki] at h
  simp only [map_mul,map_inv,hq,hl,h0,h1,h2,h3,mul_zero,mul_one] at h
  rw [synchronizedSuzukiMixed_val,←simple_suzuki]
  simpa only [map_mul] using h

private theorem four_unique_r
    (v l w t r q v' l' w' t' r' q' : CoefficientField m)
    (he : S 1 v l*L 3 w*S 3 t r*L 1 q =
      S 1 v' l'*L 3 w'*S 3 t' r'*L 1 q') : r = r' := by
  have hh := linearProduct_injective Q split c
    (a₁ := (1,1,synchronizedPositiveChart Q split c (.inr 1) (v,l),
      synchronizedPositiveChart Q split c (.inl 3) w,
      synchronizedPositiveChart Q split c (.inr 3) (t,r),
      synchronizedPositiveChart Q split c (.inl 1) q,1,PUnit.unit))
    (a₂ := (1,1,synchronizedPositiveChart Q split c (.inr 1) (v',l'),
      synchronizedPositiveChart Q split c (.inl 3) w',
      synchronizedPositiveChart Q split c (.inr 3) (t',r'),
      synchronizedPositiveChart Q split c (.inl 1) q',1,PUnit.unit)) (by
        simp only [linearFactors,rootProduct,OneMemClass.coe_one,one_mul,mul_one]
        change S 1 v l*(L 3 w*(S 3 t r*L 1 q)) =
          S 1 v' l'*(L 3 w'*(S 3 t' r'*L 1 q'))
        simpa only [mul_assoc] using he)
  have hr := (synchronizedPositiveChart Q split c (.inr 3)).injective
    (congrArg (fun z => z.2.2.2.2.1) hh)
  exact congrArg Prod.snd hr

private theorem triple_mul
    (v l w t r v' l' w' t' r' : CoefficientField m) :
    (S 1 v l*L 3 w*S 3 t r)*(S 1 v' l'*L 3 w'*S 3 t' r') =
      S 1 (v+v') (l+l'+titsEnd m v*v') * L 3 (w+t*v'+w') *
        S 3 (t+t') (r+r'+titsEnd m t*t') := by
  have hs : S 3 t r*S 1 v' l' = L 3 (t*v')*S 1 v' l'*S 3 t r := by
    have h := congrArg (fun z => z*S 3 t r)
      (synchronized_nearSuzuki_middle_conjugate Q split c t r v' l')
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  have h1 := (synchronized_adjacent_commute_family Q split c (t*v') v' l').2.2.2.1
  have h2 := (synchronized_adjacent_commute_family Q split c w v' l').2.2.2.1
  have h3 := (synchronized_adjacent_commute_family Q split c w' t r).2.2.1
  calc
    _ = S 1 v l*L 3 w*(S 3 t r*S 1 v' l')*L 3 w'*S 3 t' r' := by group
    _ = (S 1 v l*S 1 v' l')*(L 3 w*L 3 (t*v')*L 3 w')*(S 3 t r*S 3 t' r') := by
      rw [hs]
      simp only [mul_assoc]
      rw [h1.left_comm,h2.left_comm,h3.symm.left_comm]
    _ = _ := by rw [synchronizedPositivePoint_quartet_mul,
      synchronizedPositivePoint_pair_mul,synchronizedPositivePoint_pair_mul,
      synchronizedPositivePoint_quartet_mul]

private theorem inverse_main_conjugate (a v l w t r : CoefficientField m) :
    (S 0 a 0)⁻¹*(S 1 v l*L 3 w*S 3 t r)*S 0 a 0 =
      S 1 v l*L 3 w*S 3 t (r+a*w)*L 1 (a*t) := by
  have hc := (synchronized_suzuki_commute_family Q split c a 0 v l).1
  have h1 : (S 0 a 0)⁻¹*S 1 v l*S 0 a 0 = S 1 v l := by
    rw [mul_assoc,hc.symm.eq]
    group
  have h2 : (S 0 a 0)⁻¹*L 3 w*S 0 a 0 = S 3 0 (a*w)*L 3 w := by
    have hi : (S 0 a 0)⁻¹ = S 0 a (titsEnd m a*a) := by
      apply inv_eq_of_mul_eq_one_right
      rw [synchronizedPositivePoint_quartet_mul]
      simp only [zero_add,CharTwo.add_self_eq_zero,synchronizedPositivePoint_quartet_zero]
    rw [hi,←inv_inv (S 0 a 0),hi]
    exact synchronized_short_conjugate Q split c a (titsEnd m a*a) w
  have h3 : (S 0 a 0)⁻¹*S 3 t r*S 0 a 0 = L 1 (a*t)*S 3 t r := by
    have hi : (S 0 a 0)⁻¹ = S 0 a (titsEnd m a*a) := by
      apply inv_eq_of_mul_eq_one_right
      rw [synchronizedPositivePoint_quartet_mul]
      simp only [zero_add,CharTwo.add_self_eq_zero,synchronizedPositivePoint_quartet_zero]
    rw [hi,←inv_inv (S 0 a 0),hi]
    exact synchronized_nearSuzuki_conjugate Q split c a (titsEnd m a*a) t r
  calc
    _ = ((S 0 a 0)⁻¹*S 1 v l*S 0 a 0)*
        ((S 0 a 0)⁻¹*L 3 w*S 0 a 0)*((S 0 a 0)⁻¹*S 3 t r*S 0 a 0) := by group
    _ = S 1 v l*(S 3 0 (a*w)*L 3 w)*(L 1 (a*t)*S 3 t r) := by rw [h1,h2,h3]
    _ = S 1 v l*L 3 w*(S 3 0 (a*w)*S 3 t r)*L 1 (a*t) := by
      rw [(synchronized_adjacent_commute_family Q split c (a*t) t r).2.1.eq]
      rw [(synchronized_adjacent_commute_family Q split c w 0 (a*w)).2.2.1.symm.eq]
      group
    _ = _ := by
      rw [synchronizedPositivePoint_quartet_mul]
      simp only [zero_add,map_zero,zero_mul,add_zero,add_comm (a*w) r,mul_assoc]

private theorem commute_of_conjugate {G : Type*} [Group G] {x y : G}
    (h : x*y*x⁻¹ = y) : Commute x y := by
  change x*y = y*x
  have hh := congrArg (fun z => z*x) h
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

private theorem omega_triple_commute (b v l w t r : CoefficientField m) :
  Commute (S 0 0 b) (S 1 v l*L 3 w*S 3 t r) := by
  have h1 := (synchronized_suzuki_commute_family Q split c 0 b v l).1
  have h2 : Commute (S 0 0 b) (L 3 w) := by
    apply commute_of_conjugate
    simpa only [zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] using
      synchronized_short_conjugate Q split c 0 b w
  have h3 : Commute (S 0 0 b) (S 3 t r) := by
    apply commute_of_conjugate
    simpa only [zero_mul,synchronizedPositivePoint_pair_zero,one_mul] using
      synchronized_nearSuzuki_conjugate Q split c 0 b t r
  exact (h1.mul_right h2).mul_right h3

private theorem linear_conjugate (b v l w t r : CoefficientField m) :
    L 1 b*(S 1 v l*L 3 w*S 3 t r)*(L 1 b)⁻¹ =
      S 1 v l*L 3 w*S 3 t (r+v*b) := by
  have hc : Commute (S 3 0 (v*b)) (S 1 v l) := by
    apply commute_of_conjugate
    simpa only [zero_mul,synchronizedPositivePoint_pair_zero,one_mul] using
      synchronized_nearSuzuki_middle_conjugate Q split c 0 (v*b) v l
  have h2 : L 1 b*L 3 w*(L 1 b)⁻¹ = L 3 w := by
    rw [(synchronized_linear_commute_family Q split c b w).1.eq]
    group
  have h3 : L 1 b*S 3 t r*(L 1 b)⁻¹ = S 3 t r := by
    rw [(synchronized_adjacent_commute_family Q split c b t r).2.1.eq]
    group
  calc
    _ = (L 1 b*S 1 v l*(L 1 b)⁻¹)*(L 1 b*L 3 w*(L 1 b)⁻¹)*
        (L 1 b*S 3 t r*(L 1 b)⁻¹) := by group
    _ = (S 3 0 (v*b)*S 1 v l)*L 3 w*S 3 t r := by
      rw [synchronized_short_perpendicular_conjugate,h2,h3]
    _ = S 1 v l*L 3 w*(S 3 0 (v*b)*S 3 t r) := by
      rw [hc.eq]
      simp only [mul_assoc]
      rw [(synchronized_adjacent_commute_family Q split c w 0 (v*b)).2.2.1.symm.left_comm]
    _ = _ := by
      rw [synchronizedPositivePoint_quartet_mul]
      simp only [zero_add,map_zero,zero_mul,add_zero,add_comm (v*b) r]

private theorem omega_left_mul (b v l w t r : CoefficientField m) :
    (L 1 b*L 3 b*S 1 0 b)*(S 1 v l*L 3 w*S 3 t r) =
      S 1 v (b+l)*L 3 (b+w)*S 3 t (r+v*b)*L 1 b := by
  have hswap : L 1 b*(S 1 v l*L 3 w*S 3 t r) =
      (S 1 v l*L 3 w*S 3 t (r+v*b))*L 1 b := by
    have hh := congrArg (fun z => z*L 1 b) (linear_conjugate Q split c b v l w t r)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  have hΩ : Commute (L 1 b) (S 1 0 b) := by
    apply commute_of_conjugate
    simpa only [zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] using
      synchronized_short_perpendicular_conjugate Q split c 0 b b
  calc
    _ = (S 1 0 b*L 3 b)*(L 1 b*(S 1 v l*L 3 w*S 3 t r)) := by
      rw [(synchronized_linear_commute_family Q split c b b).1.eq]
      simp only [mul_assoc]
      rw [hΩ.left_comm,(synchronized_adjacent_commute_family Q split c b 0 b).2.2.2.1.left_comm]
    _ = ((S 1 0 b*L 3 b*S 3 0 0)*(S 1 v l*L 3 w*S 3 t (r+v*b)))*L 1 b := by
      rw [hswap,synchronizedPositivePoint_quartet_zero]
      group
    _ = _ := by
      rw [triple_mul]
      simp only [zero_add,add_zero,map_zero,zero_mul]

private theorem endpoint_add_one (a la ra l1 r1 ls rs : CoefficientField m)
    (ha : M a 1 = S 1 a la*L 3 (a*titsEnd m a)*S 3 (titsEnd m a) ra)
    (h1 : M 1 1 = S 1 1 l1*L 3 1*S 3 1 r1)
    (hs : M (a+1) 1 = S 1 (a+1) ls*L 3 ((a+1)*titsEnd m (a+1))*S 3 (titsEnd m (a+1)) rs) :
    rs = ra+r1 := by
  let Y := S 2 1 0
  let A := S 0 a 0
  let B := S 0 1 0
  let D := S 0 (a+1) 0
  let O := S 0 0 (titsEnd m a)
  have hp : A*B = D*O := by
    dsimp [A,B,D,O]
    rw [synchronizedPositivePoint_quartet_mul,synchronizedPositivePoint_quartet_mul]
    simp only [zero_add,add_zero,mul_zero,mul_one]
  have hMa : Y⁻¹*A⁻¹*Y*A = S 1 a la*L 3 (a*titsEnd m a)*S 3 (titsEnd m a) ra := by
    simpa only [synchronizedSuzukiMixed_val,←simple_suzuki,Y,A] using ha
  have hM1 : Y⁻¹*B⁻¹*Y*B = S 1 1 l1*L 3 1*S 3 1 r1 := by
    simpa only [synchronizedSuzukiMixed_val,←simple_suzuki,Y,B] using h1
  have hMs : Y⁻¹*D⁻¹*Y*D =
      S 1 (a+1) ls*L 3 ((a+1)*titsEnd m (a+1))*S 3 (titsEnd m (a+1)) rs := by
    simpa only [synchronizedSuzukiMixed_val,←simple_suzuki,Y,D] using hs
  have hMO : Y⁻¹*O⁻¹*Y*O = L 1 (titsEnd m a)*L 3 (titsEnd m a)*S 1 0 (titsEnd m a) := by
    simpa only [Y,O,map_one,one_mul,one_pow] using
      synchronized_omegaOpposite_right Q split c (titsEnd m a) 1
  have hc := omega_triple_commute Q split c (titsEnd m a) (a+1) ls
    ((a+1)*titsEnd m (a+1)) (titsEnd m (a+1)) rs
  have he : (S 1 1 l1*L 3 1*S 3 1 r1)*
      (B⁻¹*(S 1 a la*L 3 (a*titsEnd m a)*S 3 (titsEnd m a) ra)*B) =
        (L 1 (titsEnd m a)*L 3 (titsEnd m a)*S 1 0 (titsEnd m a))*
          (S 1 (a+1) ls*L 3 ((a+1)*titsEnd m (a+1))*S 3 (titsEnd m (a+1)) rs) := by
    calc
      _ = Y⁻¹*(A*B)⁻¹*Y*(A*B) := by rw [←hMa,←hM1]; group
      _ = (Y⁻¹*O⁻¹*Y*O)*(O⁻¹*(Y⁻¹*D⁻¹*Y*D)*O) := by rw [hp]; group
      _ = _ := by
        rw [hMO,hMs]
        rw [mul_assoc O⁻¹,←hc.eq]
        dsimp only [O]
        group
  dsimp only [B] at he
  rw [inverse_main_conjugate] at he
  rw [←mul_assoc _ _ (L 1 (1*titsEnd m a)),triple_mul] at he
  simp only [one_mul,map_one] at he
  rw [omega_left_mul] at he
  have hr := four_unique_r Q split c _ _ _ _ _ _ _ _ _ _ _ _ he
  have hcancel : r1+ra+(a+1)*titsEnd m a = rs+(a+1)*titsEnd m a := by
    calc
      _ = r1+(ra+a*titsEnd m a)+titsEnd m a := by ring
      _ = _ := hr
  exact (add_right_cancel hcancel).symm.trans (add_comm _ _)

private theorem scaled_seed (ε : CoefficientField m)
    (hε : M 1 1 = S 1 1 (1+ε)*L 3 1*S 3 1 ε) (a y : CoefficientField m) :
    M a y = S 1 (a*titsEnd m y) ((a*titsEnd m y)*titsEnd m (a*titsEnd m y)*(1+ε)) *
      L 3 ((a*titsEnd m a)*(y*titsEnd m y)) *
        S 3 (titsEnd m a*y) ((titsEnd m a*y)*titsEnd m (titsEnd m a*y)*ε) := by
  by_cases ha : a = 0
  · subst a
    simp only [synchronizedSuzukiMixed_val,←simple_suzuki,map_zero,zero_mul,mul_zero,
      synchronizedPositivePoint_quartet_zero,synchronizedPositivePoint_pair_zero,
      inv_one,mul_one,inv_mul_cancel]
  by_cases hy : y = 0
  · subst y
    simp only [synchronizedSuzukiMixed_val,←simple_suzuki,map_zero,zero_mul,mul_zero,
      synchronizedPositivePoint_quartet_zero,synchronizedPositivePoint_pair_zero,
      inv_one,one_mul,mul_one,inv_mul_cancel]
  exact transported_seed Q split c ε hε a y ha hy

private theorem seed_zero (hm : 0 < m) (ε : CoefficientField m)
    (hε : M 1 1 = S 1 1 (1+ε)*L 3 1*S 3 1 ε) : ε = 0 := by
  classical
  have hs (a : CoefficientField m) : M a 1 =
      S 1 a (a*titsEnd m a*(1+ε))*L 3 (a*titsEnd m a)*
        S 3 (titsEnd m a) (titsEnd m a*a^2*ε) := by
    simpa only [map_one,mul_one,titsEnd_twice] using scaled_seed Q split c ε hε a 1
  have hadd (a : CoefficientField m) :
      titsEnd m (a+1)*(a+1)^2*ε = titsEnd m a*a^2*ε+ε :=
    endpoint_add_one Q split c a _ _ _ _ _ _ (hs a) hε (hs (a+1))
  have hz (a : CoefficientField m) : (titsEnd m a+a^2)*ε = 0 := by
    have h := hadd a
    rw [map_add,map_one,CharTwo.add_sq,one_pow] at h
    have he : (titsEnd m a+1)*(a^2+1)*ε =
        (titsEnd m a*a^2*ε+ε)+(titsEnd m a+a^2)*ε := by ring
    rw [he] at h
    exact add_left_cancel (h.trans (add_zero _).symm)
  have hc : 2 < Fintype.card (CoefficientField m) := by
    rw [←Nat.card_eq_fintype_card,field_card]
    have h := pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 2 ≤ 2*m+1)
    omega
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1} : Finset (CoefficientField m))) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by simpa using hc))
  have hne : titsEnd m a+a^2 ≠ 0 := by
    intro he
    have hθ : titsEnd m a = a^2 := by
      simpa only [CharTwo.neg_eq] using eq_neg_iff_add_eq_zero.mpr he
    have hf : titsEnd m a = a := (titsEnd m).injective
      ((titsEnd_twice m a).trans hθ.symm)
    rcases eq_zero_or_one_of_sq_eq_self (hθ.symm.trans hf) with h0|h1
    · exact ha (by simp [h0])
    · exact ha (by simp [h1])
  exact (mul_eq_zero.mp (hz a)).resolve_left hne

/-- The native pure opposite Suzuki commutator for every nonbinary field. -/
theorem synchronizedSuzukiMixed_main_nonbinary (hm : 0 < m) (a y : CoefficientField m) :
    M a y = S 1 (a*titsEnd m y) (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) *
      L 3 ((a*titsEnd m a)*(y*titsEnd m y))*S 3 (titsEnd m a*y) 0 := by
  obtain ⟨ε,hε⟩ := synchronizedSuzukiMixed_unit_seed Q split c
  have h0 := seed_zero Q split c hm ε hε
  simpa only [h0,add_zero,mul_one,mul_zero,mul_comm (a*titsEnd m y)] using
    scaled_seed Q split c ε hε a y

/-- The exact source main-curve equation, on the literal marked quotient. -/
theorem synchronized_opposite_main_commutator_nonbinary (hm : 0 < m) (a y : CoefficientField m) :
    (S 2 y 0)⁻¹*(S 0 a 0)⁻¹*S 2 y 0*S 0 a 0 =
      S 1 (a*titsEnd m y) (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) *
        L 3 ((a*titsEnd m a)*(y*titsEnd m y))*S 3 (titsEnd m a*y) 0 := by
  have h := synchronizedSuzukiMixed_main_nonbinary Q split c hm a y
  simpa only [synchronizedSuzukiMixed_val,←simple_suzuki] using h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
