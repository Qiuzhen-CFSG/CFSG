module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeUnitaryFive
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.WreathedIntersection

/-!
# Excluding linear-three containers of the smaller-Sylow A₅ section

The existing odd-ternary restriction forces q=p=5 and identifies the literal
right quotient image with SL₂(5). Intersect the actor–Sylow join with the
normal containing component. Its order divides 2^k·5, and its Sylow group
is C₄ wreath C₂. The characteristic central involution recovers the marked
SL₂(5), so the prime actor normalizes it, contradicting the original
normalizer disjointness.

This removes the remaining PSL₃(5) row. Together with the distinct unitary
and cubic-cover exclusions, the A₅ containing catalogue now consists of J₄
and the two original noncentral-Fitting alternatives. Both Cartan markings,
the literal quotient maps and relative component normality are retained.
The changed-Sylow residual equality, remaining containing cases, zero-core
recognition and higher-field reductions remain obligations of this task.

Source: Aschbacher–Smith 5.1.13 and5.2.2, pp.637–638,648–649 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
private theorem derived_bound_of_equiv {Y Z : Type*} [Group Y] [Group Z]
    (e : Y ≃* Z)
    (hb : ∀ z : Z, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Z))) ≤ 120) :
    ∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120 := by
  intro z hz
  have he : (centralizer ({z} : Set Y)).map e.toMonoidHom =
      centralizer ({e z} : Set Z) := by
    simpa only [Set.image_singleton] using map_centralizer_equiv ({z} : Set Y) e
  let a := (e.subgroupMap (centralizer ({z} : Set Y))).trans (MulEquiv.subgroupCongr he)
  have ha : (commutator (centralizer ({z} : Set Y))).map a.toMonoidHom =
      commutator (centralizer ({e z} : Set Z)) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective]
    rfl
  rw [Nat.card_congr ((a.subgroupMap (commutator (centralizer ({z} : Set Y)))).trans
    (MulEquiv.subgroupCongr ha)).toEquiv]
  exact hb (e z) ((e.orderOf_eq z).trans hz)

private theorem linear_five_structure {Y : Type*} [Group Y] [Finite Y]
    (hm : ClassicalGroup.IsPSL Y 3 5) :
    (∀ S : Sylow 2 Y, Nonempty (S ≃* WreathedThirtyTwo)) ∧
    (∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  refine ⟨?_,derived_bound_of_equiv e ?_⟩
  · intro S
    exact ⟨(e.subgroupMap (S : Subgroup Y)).trans
      (Theory.SpecificGroups.Classical.SylowMarkedSL2.psl3_five_sylow_wreath hF (S.mapSurjective e.surjective)).some⟩
  · let q := Matrix.PSL3.projection F
    have hk : q.ker ≤ center SL(3,F) := by rw [Matrix.PSL3.projection_ker]
    have hc : ∀ x ∈ q.ker, x^3 = 1 := by
      intro x hx
      exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
        ((_root_.orderOf_dvd_natCard (⟨x,hk hx⟩ : center SL(3,F))).trans (Matrix.SL3.card_center_dvd_three F)))
    exact Theory.SpecificGroups.Classical.SylowMarkedSL2.derived_centralizer_bound_of_central_cube_cover
      q (Matrix.PSL3.projection_surjective F) hk hc
      (Theory.SpecificGroups.Classical.SylowMarkedSL2.linear_derived_centralizer_card_le hF)

private theorem linear_five_actor_normalizes
    {Y : Type*} [Group Y] [Finite Y]
    (K R D : Subgroup Y) [K.Normal] (hRK : R ≤ K)
    (P : Sylow 2 Y) (hPR : (P : Subgroup Y) ≤ normalizer (R : Set Y))
    (hm : ClassicalGroup.IsPSL K 3 5)
    (hR : Chapter1.Section02.LocalModels.IsSL R 2 5)
    {k : ℕ} (hd : Nat.card (D ⊔ (P : Subgroup Y) : Subgroup Y) ∣ 2^k*5) :
    D ≤ normalizer (R : Set Y) := by
  let J := (D ⊔ (P : Subgroup Y)).subgroupOf K
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  have hSJ : (S : Subgroup K) ≤ J := by rw [hS]; exact comap_mono le_sup_right
  have hSR : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [hS,←subgroupOf_normalizer_eq hRK]
    exact comap_mono hPR
  have hJd : Nat.card J ∣ 2^k*5 :=
    (card_comap_dvd_of_injective (D ⊔ (P : Subgroup Y)) K.subtype K.subtype_injective).trans hd
  obtain ⟨F,_,_,hF,⟨eR⟩⟩ := hR
  obtain ⟨hgens,hbound⟩ := linear_five_structure hm
  intro d hdD
  let a : MulAut K := MulAut.conjNormal d
  have hJ : J.map a.toMonoidHom = J := by
    ext x
    rw [mem_map_equiv]
    change (a.symm x).val ∈ D ⊔ (P : Subgroup Y) ↔ x.val ∈ D ⊔ (P : Subgroup Y)
    rw [MulAut.conjNormal_symm_apply]
    exact ((mem_normalizer_iff''.mp
      ((D ⊔ (P : Subgroup Y)).le_normalizer (show d ∈ D ⊔ (P : Subgroup Y) from (show D ≤ D ⊔ (P : Subgroup Y) from le_sup_left) hdD))) x.val).symm
  have he := Theory.SpecificGroups.Classical.SylowMarkedSL2.automorphism_preserves_sl2_five_of_wreathed_intersection hgens hbound (R.subgroupOf K) J
    ((subgroupOfEquivOfLe hRK).trans eR) hF S hSR hSJ hJd a hJ
  rw [mem_normalizer_iff_map_conj_eq]
  have hh := congrArg (Subgroup.map K.subtype) he
  rw [map_map,map_subgroupOf_eq_of_le hRK] at hh
  have hf : K.subtype.comp a.toMonoidHom = (MulAut.conj d).toMonoidHom.comp K.subtype := by
    ext x; rfl
  rw [hf,←map_map,map_subgroupOf_eq_of_le hRK] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G]
private theorem source_linear_five_exclusion
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 5 D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 5) : False := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hTX : normalizingSylow T R ≤ X := le_sup_right
  obtain ⟨hc,hdis,_⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  have hRfive := (d.source_overcomponent_odd_ternary_A5_section h hH hSyl
    hRX hKX hRK hK hA5 (by decide : Nat.Prime 5) (by decide)
    (.inl hm)).2
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have hPR : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map q ≤ _
    rw [heS]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hjoin : Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) =
      ((D ⊔ normalizingSylow T R).subgroupOf X).map q := by
    change Dbar ⊔ (S : Subgroup X).map q = _
    rw [heS,subgroupOf_sup hDX hTX,Subgroup.map_sup]
  obtain ⟨a,ha⟩ := d.actor_join_order h hH c hd
  have hdiv : Nat.card (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) ∣
      2^a * 5 := by
    rw [hjoin]
    apply (((D ⊔ normalizingSylow T R).subgroupOf X).card_map_dvd q).trans
    rwa [Nat.card_congr (subgroupOfEquivOfLe (sup_le hDX hTX)).toEquiv]
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hnorm := linear_five_actor_normalizes Kbar Rbar Dbar (map_mono (comap_mono hRK))
    P hPR (hm.of_mulEquiv eK) hRfive hdiv
  have hbot : Dbar = ⊥ := disjoint_self.mp (hdis.mono_right hnorm)
  change Nat.card Dbar = 5 at hc
  rw [hbot] at hc
  norm_num at hc

/-- The actual smaller-Sylow A₅ branch has no odd-prime linear-three container. -/
theorem LocalData.changedSylow_A5_linear_exclusion
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p q : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q) : False := by
  have hternary : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q ∨
      ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q := by
    exact .inl hm
  obtain ⟨rfl,rfl,_,_⟩ := d.changedSylow_A5_odd_ternary h hH hgen hthree c hd hz hs
    P hP hKX hRK hK hA5 hq ho hternary
  exact source_linear_five_exclusion d h hH c hd hz
    (Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right le_sup_left) hRK hKX hK hKn hA5 hm

open Chapter1.Section02 LocalModels


/-- After the linear-five exclusion, the A₅ containing catalogue consists of J₄
and the two original noncentral-Fitting alternatives. -/
theorem LocalData.changedSylow_A5_remaining_nonternary
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer (generated L H D R ⊔ normalizingSylow T R) K) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    A36Common I ∧
      ((IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧
        Nonempty (I ≃* Janko4.Model)) ∨
      A36Natural I ∨ A36Nilpotent I) := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let e : I ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  obtain ⟨hc,hcases⟩ := d.changedSylow_A5_remaining_nonunitary h hH hgen hthree c hd hz hs
    P hP hKX hRK hK hKn hA5 hm
  refine ⟨hc,?_⟩
  rcases hcases with ⟨hi,hsimple,hj | hl⟩ | hn | hn
  · exact .inl ⟨hi,hsimple,hj⟩
  · exact (d.changedSylow_A5_linear_exclusion h hH hgen hthree c hd hz hs P hP
      hKX hRK hK hKn hA5 (by decide : Nat.Prime 5) (by decide)
      (hl.of_mulEquiv e.symm)).elim
  · exact .inr (.inl hn)
  · exact .inr (.inr hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
