module

public import CFSG.Quasithin.ChapterC.Section06.GeneralRank
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Join
public import Theory.Frattini.PGroupMap
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Schreier
public import Theory.PGroupCore

/-!
# Factorization and centralizers in C.6.3

Under the centralizer and elementary-quotient hypotheses of C.6.3(3),
the minimum centralizer rank forces an escaping conjugate to generate `R`
together with `Q`. The same argument in the other direction gives the
centralizer factorization and the equality in the literal quotient
`(L ⊔ R)/C_R(L)`.

For the index-two case, the outside conjugation exchanges each pair
`U, Uˣ` and `D, Dˣ`. The C.6.2 normalizer obstruction kills `D ∩ Dˣ`
and the Frattini subgroup of `C_R(U Uˣ)`, giving elementary abelian `Q`
and `R = Q Qˣ`. The offender assertion about `A(R)` is a separate step.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), C.6.3(3), printed pp. 166--167.
-/

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

private theorem elementary_card (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] : Nat.card E = 2 ^ Group.rank E := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  apply le_antisymm
  · exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' E
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E)))
  · have hc : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
      rw [Nat.card_congr Additive.ofMul]
      simpa using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    rw [hc]
    exact Nat.pow_le_pow_right (by decide) (IsElementaryAbelian.rank_le_finrank E)

private theorem map_relative_centralizer (e : G ≃* G) (R A : Subgroup G) :
    (R ⊓ centralizer (A : Set G)).map (e : G →* G) =
      R.map (e : G →* G) ⊓ centralizer (A.map (e : G →* G) : Set G) := by
  rw [map_inf _ _ _ e.injective]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ z hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact (e.map_mul a x).symm.trans ((congrArg e (hx a ha)).trans (e.map_mul x a))
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro a ha
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hy (e a) (mem_map_of_mem _ ha)

private theorem normalizes_centralizer (R A : Subgroup G)
    (h : R ≤ normalizer (A : Set G)) :
    R ≤ normalizer (centralizer (A : Set G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg y hy z hz
  have hz' := (mem_normalizer_iff.mp (h (R.inv_mem hg)) z).mp hz
  have hh := congrArg (MulAut.conj g) (hy (g⁻¹ * z * g) (by simpa using hz'))
  simpa [MulAut.conj_apply, mul_assoc] using hh

private theorem rank_forces_sup (R V Q : Subgroup G) [Finite R]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hQR : Q ≤ R)
    (hVQ : V ≤ normalizer (Q : Set G)) (n : ℕ)
    (hindex : Q.relIndex R = 2 ^ n)
    (hrank : let : Finite V := Finite.of_injective (inclusion hVR) (inclusion_injective hVR)
      n ≤ Group.rank (V ⧸ Q.subgroupOf V)) : R = V ⊔ Q := by
  let : Finite V := Finite.of_injective (inclusion hVR) (inclusion_injective hVR)
  have hlow : 2 ^ n ≤ Q.relIndex V := by
    change 2 ^ n ≤ Nat.card (V ⧸ Q.subgroupOf V)
    rw [elementary_card]
    exact Nat.pow_le_pow_right (by decide) hrank
  have heq : Q.relIndex V = Q.relIndex R := le_antisymm
    (relIndex_le_of_le_right hVR (by rw [hindex]; positivity)) (hindex ▸ hlow)
  let : (Q.subgroupOf (V ⊔ Q)).Normal :=
    normal_subgroupOf_sup_of_le_normalizer hVQ
  have hs : Q.relIndex (V ⊔ Q) = Q.relIndex V := by
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient V Q hVQ).toEquiv).symm
  have hm := relIndex_mul_relIndex Q (V ⊔ Q) R le_sup_right (sup_le hVR hQR)
  rw [hs, heq] at hm
  have hi : (V ⊔ Q).relIndex R = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Q.relIndex R by rw [hindex]; positivity)
    simpa using hm
  exact le_antisymm (relIndex_eq_one.mp hi) (sup_le hVR hQR)

/-- Local form of C.6.3(3)(i); the numerical premise is the order assertion in (b). -/
public theorem c6_3_factorization (R U Q : Subgroup G) [Finite R]
    [IsElementaryAbelian 2 U] (hUR : U ≤ R)
    (hRU : R ≤ normalizer (U : Set G))
    (hQ : Q = R ⊓ centralizer (U : Set G)) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hescape : ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q)
    (hindex : let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
      Q.relIndex R = 2 ^ centralizerRankMinimum R U) :
    let V := U.map (MulAut.conj x⁻¹ : G →* G)
    R = V ⊔ Q ∧ R = U ⊔ (R ⊓ centralizer (V : Set G)) ∧
      Q = U ⊔ (Q ⊓ centralizer (V : Set G)) ∧
      R = (U ⊔ V) ⊔ (R ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G)) := by
  let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
  let V := U.map (MulAut.conj x⁻¹ : G →* G)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hRx : R.map (MulAut.conj x⁻¹ : G →* G) = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
  have hVR : V ≤ R := (map_mono hUR).trans_eq hRx
  let : Finite V := Finite.of_injective (inclusion hVR) (inclusion_injective hVR)
  have hQR : Q ≤ R := hQ ▸ inf_le_left
  have hRQ : R ≤ normalizer (Q : Set G) := by
    rw [hQ]
    exact (le_inf R.le_normalizer (normalizes_centralizer R U hRU)).trans
      inf_normalizer_le_normalizer_inf
  have hUQ : U ≤ Q := by rw [hQ]; exact le_inf hUR (le_centralizer U)
  have hsub : (centralizer (U : Set G)).subgroupOf V = Q.subgroupOf V := by
    rw [hQ]; ext v; exact (and_iff_right (hVR v.property)).symm
  have hvbound := c6_3_rank_bound R U Q hUR x hx hescape (by rw [hQ])
  change centralizerRankMinimum R U ≤
    Group.rank (V ⧸ (centralizer (U : Set G)).subgroupOf V) at hvbound
  rw [hsub] at hvbound
  have hfirst := rank_forces_sup R V Q hVR hQR (hVR.trans hRQ)
    (centralizerRankMinimum R U) hindex hvbound
  have hcmap : Q.map (MulAut.conj x⁻¹ : G →* G) =
      R ⊓ centralizer (V : Set G) := by
    rw [hQ, map_relative_centralizer, hRx]
  have hcindex : (R ⊓ centralizer (V : Set G)).relIndex R =
      2 ^ centralizerRankMinimum R U := by
    calc
      _ = (Q.map (MulAut.conj x⁻¹ : G →* G)).relIndex
          (R.map (MulAut.conj x⁻¹ : G →* G)) := by rw [hcmap, hRx]
      _ = Q.relIndex R := relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective
      _ = _ := hindex
  have hnot : ¬ U ≤ centralizer (V : Set G) := by
    intro h
    exact hescape (by rw [hQ]; exact le_inf hVR (le_centralizer_iff.mp h))
  have hubound := centralizerRankMinimum_le R U (U ⊓ centralizer (V : Set G))
    inf_le_left (centralizer_lt_centralizer_inf_of_not_le R V U hVR hnot)
  have hsub' : (U ⊓ centralizer (V : Set G)).subgroupOf U =
      (R ⊓ centralizer (V : Set G)).subgroupOf U := by
    ext u; simp only [mem_subgroupOf, mem_inf, u.property, hUR u.property, true_and]
  rw [hsub'] at hubound
  have hsecond := rank_forces_sup R U (R ⊓ centralizer (V : Set G)) hUR inf_le_left
    (by
      rw [← hcmap]
      have hnorm : R ≤ normalizer (R ⊓ centralizer (V : Set G) : Set G) := by
        have hRV : R ≤ normalizer (V : Set G) := by
          calc
            R = R.map (MulAut.conj x⁻¹ : G →* G) := hRx.symm
            _ ≤ (normalizer (U : Set G)).map (MulAut.conj x⁻¹ : G →* G) := map_mono hRU
            _ ≤ normalizer (V : Set G) := U.le_normalizer_map _
        exact (le_inf R.le_normalizer (normalizes_centralizer R V hRV)).trans
          inf_normalizer_le_normalizer_inf
      rw [hcmap]
      exact hUR.trans hnorm)
    (centralizerRankMinimum R U) hcindex hubound
  have hthird : Q = U ⊔ (Q ⊓ centralizer (V : Set G)) := by
    apply le_antisymm
    · intro q hq
      have hmem : q ∈ U ⊔ (R ⊓ centralizer (V : Set G)) := hsecond ▸ hQR hq
      rcases (show ∃ u ∈ U, ∃ c ∈ R ⊓ centralizer (V : Set G), u * c = q from by
        change q ∈ ((U ⊔ (R ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) at hmem
        rw [coe_mul_of_right_le_normalizer_left U _ (inf_le_left.trans hRU)] at hmem
        exact hmem) with ⟨u, hu, c, hc, rfl⟩
      exact mul_mem_sup hu ⟨by simpa using Q.mul_mem (Q.inv_mem (hUQ hu)) hq, hc.2⟩
    · exact sup_le hUQ inf_le_left
  have hcommon : Q ⊓ centralizer (V : Set G) =
      R ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) := by
    rw [hQ]
    apply le_antisymm
    · refine le_inf (inf_le_left.trans inf_le_left) ?_
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
        (le_centralizer_iff.mp inf_le_right)
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le (show (U : Set G) ⊆ (U ⊔ V : Subgroup G) from fun _ h => mem_sup_left h))))
        (inf_le_right.trans (centralizer_le (show (V : Set G) ⊆ (U ⊔ V : Subgroup G) from fun _ h => mem_sup_right h)))
  refine ⟨hfirst, hsecond, hthird, ?_⟩
  calc
    R = V ⊔ Q := hfirst
    _ = V ⊔ (U ⊔ (R ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G))) := by
      conv_lhs => rw [hthird, hcommon]
    _ = _ := by dsimp only [V]; ac_rfl

private theorem image_eq_of_centralizer_bound {B : Type*} [Group B]
    (R U V Q S : Subgroup G) (hRS : R ≤ S)
    (hUR : U ≤ R) (hVR : V ≤ R) (hQR : Q ≤ R)
    (hfirst : R = V ⊔ Q) (hthird : Q = U ⊔ (Q ⊓ centralizer (V : Set G)))
    (f : S →* B) [IsMulCommutative ((Q.subgroupOf S).map f)]
    (hcentral : (Q.subgroupOf S).map f ⊓
      centralizer ((R.subgroupOf S).map f : Set B) ≤ (U.subgroupOf S).map f) :
    (U.subgroupOf S).map f = (Q.subgroupOf S).map f := by
  let C := Q ⊓ centralizer (V : Set G)
  have hCS : C ≤ S := (inf_le_left : C ≤ Q).trans (hQR.trans hRS)
  have hCU : (C.subgroupOf S).map f ≤ (U.subgroupOf S).map f := by
    apply le_trans (le_inf (map_mono (subgroupOf_mono S inf_le_left)) ?_) hcentral
    apply le_centralizer_iff.mpr
    have heq : (R.subgroupOf S).map f =
        (V.subgroupOf S).map f ⊔ (Q.subgroupOf S).map f := by
      rw [hfirst, subgroupOf_sup (hVR.trans hRS) (hQR.trans hRS), Subgroup.map_sup]
    rw [heq]
    apply sup_le
    · apply le_centralizer_iff.mp
      rintro z ⟨c, hc, rfl⟩ y ⟨v, hv, rfl⟩
      exact (f.map_mul v c).symm.trans
        ((congrArg f (Subtype.ext (hc.2 v hv))).trans (f.map_mul c v))
    · exact le_centralizer_iff.mp
        ((map_mono (subgroupOf_mono S inf_le_left)).trans
          (le_centralizer ((Q.subgroupOf S).map f)))
  have heq : (Q.subgroupOf S).map f =
      (U.subgroupOf S).map f ⊔ (C.subgroupOf S).map f := by
    conv_lhs => rw [hthird]
    rw [subgroupOf_sup (hUR.trans hRS) hCS, Subgroup.map_sup]
  rw [heq, sup_eq_left.mpr hCU]

/-- C.6.3(3)(ii), in the literal quotient `(L ⊔ R)/C_R(L)`. -/
public theorem c6_3_quotient_factorization (L R U Q : Subgroup G) [Finite R]
    [IsElementaryAbelian 2 U] (hUR : U ≤ R)
    (hRU : R ≤ normalizer (U : Set G))
    (hQ : Q = R ⊓ centralizer (U : Set G)) (hQtwo : IsPGroup 2 Q)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hescape : ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q)
    (hindex : let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
      Q.relIndex R = 2 ^ centralizerRankMinimum R U)
    [( (R ⊓ centralizer (L : Set G)).subgroupOf (L ⊔ R)).Normal] :
    let S := L ⊔ R
    let f := QuotientGroup.mk' ((R ⊓ centralizer (L : Set G)).subgroupOf S)
    let Qbar := (Q.subgroupOf S).map f
    let Ubar := (U.subgroupOf S).map f
    let Rbar := (R.subgroupOf S).map f
    frattini Qbar = ⊥ → Qbar ⊓ centralizer (Rbar : Set _) ≤ Ubar → Ubar = Qbar := by
  intro S f Qbar Ubar Rbar hPhi hcentral
  have hQR : Q ≤ R := hQ ▸ inf_le_left
  let : Finite Q := Finite.of_injective (inclusion hQR) (inclusion_injective hQR)
  let : Finite (Q.subgroupOf S) :=
    Finite.of_equiv Q (subgroupOfEquivOfLe (hQR.trans le_sup_right)).symm.toEquiv
  let : Finite Qbar := Finite.of_surjective
    (fun q : Q.subgroupOf S => (⟨f q, mem_map_of_mem f q.property⟩ : Qbar)) (by
      rintro ⟨y, q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩)
  have hQbar2 : IsPGroup 2 Qbar :=
    (hQtwo.of_equiv (subgroupOfEquivOfLe (hQR.trans le_sup_right)).symm).map f
  let : Fact (IsPGroup 2 Qbar) := ⟨hQbar2⟩
  let : IsElementaryAbelian 2 Qbar := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hPhi
  have hfac := c6_3_factorization R U Q hUR hRU hQ x hx hescape hindex
  exact image_eq_of_centralizer_bound R U _ Q S le_sup_right hUR
    ((map_mono hUR).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)))
    hQR hfac.1 hfac.2.2.1 f hcentral


private theorem index_sup_of_normalizes (X T : Subgroup G) [Finite T]
    (hTX : T ≤ normalizer (X : Set G)) : T.relIndex (X ⊔ T) = T.relIndex X := by
  let : (X.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hTX
  let : (X.subgroupOf (T ⊔ X)).Normal := normal_subgroupOf_sup_of_le_normalizer hTX
  have hx : X.relIndex (X ⊔ T) = X.relIndex T := by
    rw [sup_comm X T]
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient T X hTX).toEquiv).symm
  have hm : X.relIndex T * T.relIndex (X ⊔ T) = X.relIndex T * T.relIndex X := by
    calc
      _ = (T ⊓ X).relIndex (X ⊔ T) := by
        rw [← inf_relIndex_left (H := T) (K := X)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (T ⊓ X).relIndex X * X.relIndex (X ⊔ T) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = _ := by rw [inf_relIndex_right, hx, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite : X.relIndex T ≠ 0)) hm

private theorem index_two_setup (K T : Subgroup G) (hTK : T ≤ K)
    (hi : T.relIndex K = 2) (x : G) (hx : x ∈ K) (hxt : x ∉ T) :
    K ≤ normalizer (T : Set G) ∧ x ^ 2 ∈ T ∧ K = T ⊔ zpowers x := by
  let : (T.subgroupOf K).Normal := normal_of_index_eq_two hi
  refine ⟨(normal_subgroupOf_iff_le_normalizer hTK).mp inferInstance,
    (T.subgroupOf K).sq_mem_of_index_two hi ⟨x, hx⟩, ?_⟩
  apply le_antisymm
  · intro y hy
    by_cases hyt : y ∈ T
    · exact mem_sup_left hyt
    · have hyx : y * x ∈ T := by
        exact ((T.subgroupOf K).mul_mem_iff_of_index_two hi
          (a := ⟨y, hy⟩) (b := ⟨x, hx⟩)).mpr (iff_of_false hyt hxt)
      simpa using (T ⊔ zpowers x).mul_mem (mem_sup_left hyx)
        (mem_sup_right ((zpowers x).inv_mem (mem_zpowers x)))
  · exact sup_le hTK (zpowers_le.mpr hx)

private theorem normalizes_pair (K T A : Subgroup G) (x : G)
    (hKT : K ≤ normalizer (T : Set G)) (hx : x ∈ K)
    (hsq : x ^ 2 ∈ T) (hgen : K = T ⊔ zpowers x)
    (hTA : T ≤ normalizer (A : Set G)) :
    K ≤ normalizer ((A ⊔ A.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G) ∧
    K ≤ normalizer ((A ⊓ A.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G) := by
  let e := MulAut.conj x⁻¹
  let B := A.map (e : G →* G)
  have hTB : T ≤ normalizer (B : Set G) := by
    have ht := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (T : Set G)).inv_mem (hKT hx))
    calc
      T = T.map (e : G →* G) := ht.symm
      _ ≤ (normalizer (A : Set G)).map (e : G →* G) := map_mono hTA
      _ ≤ normalizer (B : Set G) := A.le_normalizer_map _
  have hswap : B.map (e : G →* G) = A := by
    change (A.map (e : G →* G)).map (e : G →* G) = A
    rw [map_map]
    have he : (e : G →* G).comp (e : G →* G) =
        (MulAut.conj (x ^ 2)⁻¹ : G →* G) := by
      ext a; simp [e, pow_two, mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (A : Set G)).inv_mem (hTA hsq))
  have hxjoin : x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    have hh : x⁻¹ ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (A ⊔ B).map (e : G →* G) = A ⊔ B
      rw [Subgroup.map_sup, hswap]; exact sup_comm B A
    simpa using (normalizer ((A ⊔ B : Subgroup G) : Set G)).inv_mem hh
  have hxmeet : x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
    have hh : x⁻¹ ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (A ⊓ B).map (e : G →* G) = A ⊓ B
      rw [map_inf _ _ _ e.injective, hswap]; exact inf_comm B A
    simpa using (normalizer ((A ⊓ B : Subgroup G) : Set G)).inv_mem hh
  rw [hgen]
  exact ⟨sup_le ((le_inf hTA hTB).trans (normalizer_inf_normalizer_le_normalizer_sup A B))
      (zpowers_le.mpr hxjoin),
    sup_le ((le_inf hTA hTB).trans inf_normalizer_le_normalizer_inf)
      (zpowers_le.mpr hxmeet)⟩

private theorem characteristic_normalized (C : Subgroup G) (F : Subgroup C)
    [F.Characteristic] :
    normalizer (C : Set G) ≤ normalizer (F.map C.subtype : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg y hy
  obtain ⟨c, hc, rfl⟩ := hy
  let e := C.normalizerMonoidHom ⟨g, hg⟩
  exact ⟨e c, characteristic_iff_le_comap.mp inferInstance e hc, rfl⟩

private theorem trivial_of_obstruction (L R T Λ W : Subgroup G)
    (hRT : R ≤ T) (hWR : W ≤ R) (hWL : W ≤ centralizer (L : Set G))
    (hKW : (Λ ⊓ normalizer (R : Set G)) ⊔ T ≤ normalizer (W : Set G))
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G)) : W = ⊥ := by
  by_contra hne
  apply hno W hne hWR
    ((normal_subgroupOf_iff_le_normalizer (hWR.trans (hRT.trans le_sup_right))).mpr
      (sup_le ((le_centralizer_iff.mp hWL).trans (centralizer_le_normalizer _))
        (le_sup_right.trans hKW)))
  exact le_inf inf_le_left (le_sup_left.trans hKW)


/-- The source centralizer `D=C_R(L)` is normal in `LR` whenever `R` normalizes `L`. -/
public theorem c6_3_centralizer_normal (L R : Subgroup G)
    (hRL : R ≤ normalizer (L : Set G)) :
    ((R ⊓ centralizer (L : Set G)).subgroupOf (L ⊔ R)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((inf_le_left : R ⊓ centralizer (L : Set G) ≤ R).trans le_sup_right)).mpr
  apply sup_le
  · exact ((le_centralizer_iff.mp (inf_le_right :
      R ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G))).trans
      (centralizer_le_normalizer _))
  · exact (le_inf R.le_normalizer (normalizes_centralizer R L hRL)).trans
      inf_normalizer_le_normalizer_inf

/-- Structural part of C.6.3(3)(iii), with the source's local normalization
inputs and the literal quotient by `D=C_R(L)`. The offender assertion is separate. -/
public theorem c6_3_structure (L R T Λ U Q : Subgroup G) [Finite R] [Finite T]
    [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (hUL : U ≤ L) (hRT : R ≤ T)
    (hRtwo : IsPGroup 2 R) (hTR : T ≤ normalizer (R : Set G))
    (hTΛ : T ≤ normalizer (Λ : Set G)) (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hQ : Q = R ⊓ centralizer (U : Set G))
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G))
    (hi : (T ⊓ Λ).relIndex (Λ ⊓ normalizer (R : Set G)) = 2)
    (x : G) (hx : x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ T)
    (hescape : ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q)
    (hindex : let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
      Q.relIndex R = 2 ^ centralizerRankMinimum R U) :
    let D := R ⊓ centralizer (L : Set G)
    let S := L ⊔ R
    letI := c6_3_centralizer_normal L R (hRT.trans hTL)
    let f := QuotientGroup.mk' (D.subgroupOf S)
    frattini ((Q.subgroupOf S).map f) = ⊥ →
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) := by
  intro D S f hPhi
  let : (D.subgroupOf S).Normal := c6_3_centralizer_normal L R (hRT.trans hTL)
  let X := Λ ⊓ normalizer (R : Set G)
  let K := X ⊔ T
  have hKR : K ≤ normalizer (R : Set G) := sup_le inf_le_right hTR
  have hxR := hKR hx
  have hQR : Q ≤ R := hQ ▸ inf_le_left
  have hUQ : U ≤ Q := by rw [hQ]; exact le_inf hUR (le_centralizer U)
  have hTX : T ≤ normalizer (X : Set G) := by
    have hTN : T ≤ normalizer (normalizer (R : Set G) : Set G) :=
      hTR.trans (normalizer (R : Set G)).le_normalizer
    exact (le_inf hTΛ hTN).trans inf_normalizer_le_normalizer_inf
  have hiX : T.relIndex X = 2 := by
    have heq : (T ⊓ Λ).subgroupOf X = T.subgroupOf X := by
      ext y; exact and_iff_left y.property.1
    change (T.subgroupOf X).index = 2
    change ((T ⊓ Λ).subgroupOf X).index = 2 at hi
    rwa [heq] at hi
  have hiK : T.relIndex K = 2 := (index_sup_of_normalizes X T hTX).trans hiX
  have hxT : x ∉ T := by
    intro ht
    have hu := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (U : Set G)).inv_mem (hTU ht))
    exact hescape (hu.le.trans hUQ)
  obtain ⟨hKT, hsq, hgen⟩ := index_two_setup K T le_sup_right hiK x hx hxT
  have hTD : T ≤ normalizer (D : Set G) :=
    (le_inf hTR (normalizes_centralizer T L hTL)).trans inf_normalizer_le_normalizer_inf
  have hDD : D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ := by
    apply trivial_of_obstruction L R T Λ _ hRT (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) _ hno
    exact (normalizes_pair K T D x hKT hx hsq hgen hTD).2
  let V := U.map (MulAut.conj x⁻¹ : G →* G)
  let C := R ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G)
  have hCR : C ≤ R := inf_le_left
  have hCQ : C ≤ Q := by
    rw [hQ]
    exact le_inf inf_le_left (inf_le_right.trans
      (centralizer_le (show (U : Set G) ⊆ (U ⊔ V : Subgroup G) from fun _ h => mem_sup_left h)))
  have hKC : K ≤ normalizer (C : Set G) :=
    (le_inf hKR (normalizes_centralizer K _
      (normalizes_pair K T U x hKT hx hsq hgen hTU).1)).trans
      inf_normalizer_le_normalizer_inf
  let : Finite C := Finite.of_injective (inclusion hCR) (inclusion_injective hCR)
  let : Finite Q := Finite.of_injective (inclusion hQR) (inclusion_injective hQR)
  let : Finite D := Finite.of_injective (inclusion (inf_le_left : D ≤ R))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 C) := ⟨hRtwo.to_le hCR⟩
  let : Fact (IsPGroup 2 Q) := ⟨hRtwo.to_le hQR⟩
  let : Fact (IsPGroup 2 D) := ⟨hRtwo.to_le inf_le_left⟩
  let Qbar := (Q.subgroupOf S).map f
  change frattini Qbar = ⊥ at hPhi
  let : Finite (Q.subgroupOf S) :=
    Finite.of_equiv Q (subgroupOfEquivOfLe (hQR.trans le_sup_right)).symm.toEquiv
  let : Finite Qbar := Finite.of_surjective
    (fun q : Q.subgroupOf S => (⟨f q, mem_map_of_mem f q.property⟩ : Qbar)) (by
      rintro ⟨y, q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩)
  let : Fact (IsPGroup 2 Qbar) := ⟨
    ((hRtwo.to_le hQR).of_equiv
      (subgroupOfEquivOfLe (hQR.trans le_sup_right)).symm).map f⟩
  let F := (frattini C).map C.subtype
  have hFD : F ≤ D := by
    let j : C →* S := inclusion (hCR.trans le_sup_right)
    let k : C →* Qbar := (f.comp j).codRestrict Qbar (by
      intro c
      exact mem_map_of_mem f (hCQ c.property))
    rintro y ⟨c, hc, rfl⟩
    have hh := frattini_map_le_of_isPGroup (p := 2) k (mem_map_of_mem k hc)
    have heq : k c = 1 := by simpa only [hPhi, mem_bot] using hh
    have hq : f (j c) = 1 := congrArg Subtype.val heq
    have hd : j c ∈ D.subgroupOf S := (QuotientGroup.eq_one_iff (j c)).mp hq
    exact hd
  have hFbot : F = ⊥ := trivial_of_obstruction L R T Λ F hRT
    ((map_subtype_le _).trans hCR) (hFD.trans inf_le_right)
    (hKC.trans (characteristic_normalized C (frattini C))) hno
  have hCphi : frattini C = ⊥ := by
    apply eq_bot_iff.mpr
    intro c hc
    have hh : (c : G) = 1 := by
      have hh := mem_map_of_mem C.subtype hc
      change (c : G) ∈ F at hh
      simpa only [hFbot, mem_bot] using hh
    exact Subtype.ext hh
  let : IsElementaryAbelian 2 C := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hCphi
  have hfac := c6_3_factorization R U Q hUR (hRT.trans hTU) hQ x hxR hescape hindex
  have hcommon : Q ⊓ centralizer (V : Set G) = C := by
    apply le_antisymm
    · refine le_inf (inf_le_left.trans hQR) ?_
      apply le_centralizer_iff.mpr
      exact sup_le
        (le_centralizer_iff.mp (inf_le_left.trans (hQ.le.trans inf_le_right)))
        (le_centralizer_iff.mp inf_le_right)
    · exact le_inf hCQ (inf_le_right.trans
        (centralizer_le (show (V : Set G) ⊆ (U ⊔ V : Subgroup G) from fun _ h => mem_sup_right h)))
  have hQC : Q = U ⊔ C := hfac.2.2.1.trans (congrArg (U ⊔ ·) hcommon)
  have hCU : C ≤ centralizer (U : Set G) := hCQ.trans (hQ.le.trans inf_le_right)
  have hQelem : IsElementaryAbelian 2 Q := by
    rw [hQC]
    exact IsElementaryAbelian.sup_of_le_centralizer hCU
  let : IsElementaryAbelian 2 Q := hQelem
  have hDQ : D ≤ Q := by
    rw [hQ]
    exact le_inf inf_le_left (inf_le_right.trans (centralizer_le hUL))
  have hDphi : frattini D = ⊥ := by
    apply eq_bot_iff.mpr
    intro d hd
    have hh := frattini_map_le_of_isPGroup (p := 2) (inclusion hDQ)
      (mem_map_of_mem (inclusion hDQ) hd)
    rw [frattini_eq_bot_of_isElementaryAbelian (p := 2)] at hh
    have heq : inclusion hDQ d = 1 := mem_bot.mp hh
    exact mem_bot.mpr (Subtype.ext (congrArg (fun q : Q => (q : G)) heq))
  refine ⟨hDD, hDphi, hQelem, le_antisymm ?_ ?_⟩
  · rw [hfac.1]
    exact sup_le ((map_mono hUQ).trans le_sup_right) le_sup_left
  · exact sup_le hQR ((map_mono hQR).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hxR)))


/-- The order assertion used in the proof is precisely the elementary
quotient/rank hypothesis C.6.3(3)(b). -/
public theorem c6_3_order_of_elementary_quotient (R Q : Subgroup G) [Finite R]
    [(Q.subgroupOf R).Normal] [IsElementaryAbelian 2 (R ⧸ Q.subgroupOf R)] :
    Q.relIndex R = 2 ^ Group.rank (R ⧸ Q.subgroupOf R) := elementary_card _

/-- C.6.3(3)(i), accepting the literal elementary quotient and its stated rank. -/
public theorem c6_3_factorization_of_quotient_rank (R U Q : Subgroup G) [Finite R]
    [IsElementaryAbelian 2 U] (hUR : U ≤ R)
    (hRU : R ≤ normalizer (U : Set G))
    (hQ : Q = R ⊓ centralizer (U : Set G)) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hescape : ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q)
    [(Q.subgroupOf R).Normal] [IsElementaryAbelian 2 (R ⧸ Q.subgroupOf R)]
    (hrank : let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
      Group.rank (R ⧸ Q.subgroupOf R) = centralizerRankMinimum R U) :
    let V := U.map (MulAut.conj x⁻¹ : G →* G)
    R = V ⊔ Q ∧ R = U ⊔ (R ⊓ centralizer (V : Set G)) ∧
      Q = U ⊔ (Q ⊓ centralizer (V : Set G)) ∧
      R = (U ⊔ V) ⊔ (R ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G)) := by
  apply c6_3_factorization R U Q hUR hRU hQ x hx hescape
  exact (c6_3_order_of_elementary_quotient R Q).trans (congrArg (2 ^ ·) hrank)

private theorem residual_core_le (L : Subgroup G) :
    ⁅(pCore 2 L).map L.subtype, L⁆ ≤ L :=
  le_normalizer_iff_commutator_le_right.mp ((map_subtype_le _).trans L.le_normalizer)

private theorem residual_core_normalized (L T : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) :
    T ≤ normalizer ((⁅(pCore 2 L).map L.subtype, L⁆ : Subgroup G) : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (characteristic_normalized L (pCore 2 L) (hTL ht)),
    mem_normalizer_iff_map_conj_eq.mp (hTL ht)]

/-- Apply the structural theorem to the source subgroup `U=[O₂(L),L]`.
Its containment in `R` comes from the initial core calculation in C.6.3;
its containment in `L`, its normalization, and the two-group input are
proved here from the defining commutator and C.6.2(2). -/
public theorem c6_3_structure_of_residual_core (L R T Λ U Q : Subgroup G) [Finite R] [Finite T]
    [IsElementaryAbelian 2 U]
    (hU : U = ⁅(pCore 2 L).map L.subtype, L⁆)
    (hUR : U ≤ R) (hRT : R ≤ T)
    (hTtwo : IsPGroup 2 T) (hTR : T ≤ normalizer (R : Set G))
    (hTΛ : T ≤ normalizer (Λ : Set G)) (hTL : T ≤ normalizer (L : Set G))
    (hQ : Q = R ⊓ centralizer (U : Set G))
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G))
    (hi : (T ⊓ Λ).relIndex (Λ ⊓ normalizer (R : Set G)) = 2)
    (x : G) (hx : x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ T)
    (hescape : ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q)
    (hindex : let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
      Q.relIndex R = 2 ^ centralizerRankMinimum R U) :
    let D := R ⊓ centralizer (L : Set G)
    let S := L ⊔ R
    letI := c6_3_centralizer_normal L R (hRT.trans hTL)
    let f := QuotientGroup.mk' (D.subgroupOf S)
    frattini ((Q.subgroupOf S).map f) = ⊥ →
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) := by
  have hUL : U ≤ L := by simpa only [hU] using residual_core_le L
  have hTU : T ≤ normalizer (U : Set G) := by
    simpa only [hU] using residual_core_normalized L T hTL
  exact c6_3_structure L R T Λ U Q hUR hUL hRT
    (hTtwo.to_le hRT) hTR hTΛ hTL hTU hQ hno hi x hx hescape hindex

end CFSG.Quasithin.ChapterC
