module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOddTernarySection
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SolvableIntersection
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SignedThree
public import Theory.SpecificGroups.SU3.FiveSylow
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Excluding unitary containers of the smaller-Sylow A₅ section

The original Cartan markings force the actor and the unitary field parameter
to be five, and identify the literal right quotient image as SL₂(5).
Inside the normal containing component, intersect the actor–Sylow join
with that component. This intersection is solvable of order dividing
2^a times five and contains a full semidihedral Sylow subgroup. Its
characteristic central involution forces the actor to preserve SL₂(5),
contradicting the established disjointness from its normalizer.

The argument treats SU₃(5) and PSU₃(5) separately through their actual
carriers and the odd central projection. It removes both unitary rows
from the same containing catalogue without assuming that the selected
right factor is an actual H-component. The changed-Sylow residual equality,
remaining containing rows, zero-core recognition and field reductions
remain separate obligations of the local-to-global argument.

Source: Aschbacher–Smith 5.1.13 and5.2.2, printed pp.637–638,648–649;
A.3.21 and C.5.12, pp.55,163 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

private theorem generators_of_equiv {Y Z : Type*} [Group Y] [Group Z]
    (e : Y ≃* Z)
    (hg : ∃ a b : Z, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set Z)=⊤) :
    ∃ a b : Y, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set Y)=⊤ := by
  obtain ⟨a,b,ha,hb,hab,hgen⟩ := hg
  refine ⟨e.symm a,e.symm b,(e.symm.orderOf_eq a).trans ha,
    (e.symm.orderOf_eq b).trans hb,?_,?_⟩
  · simpa only [map_mul,map_inv,map_pow] using congrArg e.symm hab
  · have hh := congrArg (map e.symm.toMonoidHom) hgen
    rw [MonoidHom.map_closure,map_top_of_surjective _ e.symm.surjective] at hh
    simpa only [Set.image_insert_eq,Set.image_singleton,MulEquiv.coe_toMonoidHom] using hh

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

private theorem unitary_five_structure {Y : Type*} [Group Y] [Finite Y]
    (hm : ClassicalGroup.IsPSU Y 3 5 ∨ Chapter1.Section02.LocalModels.IsSU Y 3 5) :
    (∀ S : Sylow 2 Y, ∃ a b : S, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set S)=⊤) ∧
    (∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120) := by
  rcases hm with ⟨F,_,_,J,hF,hc,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  · let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective e e.surjective
    refine ⟨?_,derived_bound_of_equiv e ?_⟩
    · intro S
      exact generators_of_equiv (e.subgroupMap (S : Subgroup Y))
        (BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow.sylow_generators J hF hc
          (S.mapSurjective e.surjective))
    · exact Theory.SpecificGroups.Classical.SylowMarkedSL2.derived_centralizer_bound_of_central_cube_cover
        J.specialToProjective J.specialToProjective_surjective
        J.specialToProjective_ker_le_center
        (fun x hx => congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩))
        (Theory.SpecificGroups.Classical.SylowMarkedSL2.unitary_derived_centralizer_card_le J hF hc)
  · refine ⟨?_,derived_bound_of_equiv e
      (Theory.SpecificGroups.Classical.SylowMarkedSL2.unitary_derived_centralizer_card_le J hF hc)⟩
    intro S
    let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let Q := P.mapSurjective J.specialToProjective_surjective
    let a := Sylow.equivOfSurjectiveCoprime J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left P Q
    exact generators_of_equiv ((e.subgroupMap (S : Subgroup Y)).trans a)
      (BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow.sylow_generators J hF hc Q)

private theorem unitary_five_actor_normalizes
    {Y : Type*} [Group Y] [Finite Y]
    (K R D : Subgroup Y) [K.Normal] (hRK : R ≤ K)
    (P : Sylow 2 Y) (hPR : (P : Subgroup Y) ≤ normalizer (R : Set Y))
    (hm : ClassicalGroup.IsPSU K 3 5 ∨ Chapter1.Section02.LocalModels.IsSU K 3 5)
    (hR : Chapter1.Section02.LocalModels.IsSL R 2 5)
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup Y) : Subgroup Y))
    {k : ℕ} (hd : Nat.card (D ⊔ (P : Subgroup Y) : Subgroup Y) ∣ 2^k*5) :
    D ≤ normalizer (R : Set Y) := by
  let J := (D ⊔ (P : Subgroup Y)).subgroupOf K
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  have hSJ : (S : Subgroup K) ≤ J := by rw [hS]; exact comap_mono le_sup_right
  have hSR : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [hS,←subgroupOf_normalizer_eq hRK]
    exact comap_mono hPR
  let f : J →* (D ⊔ (P : Subgroup Y) : Subgroup Y) :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hJs : Group.IsSolvable J := by
    let := hs
    apply Group.isSolvable_of_isSolvable_injective (f := f)
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (D ⊔ (P : Subgroup Y) : Subgroup Y) => (z : Y)) hh
  have hJd : Nat.card J ∣ 2^k*5 :=
    (card_comap_dvd_of_injective (D ⊔ (P : Subgroup Y)) K.subtype K.subtype_injective).trans hd
  obtain ⟨F,_,_,hF,⟨eR⟩⟩ := hR
  obtain ⟨hgens,hbound⟩ := unitary_five_structure hm
  intro d hdD
  let a : MulAut K := MulAut.conjNormal d
  have hJ : J.map a.toMonoidHom = J := by
    ext x
    rw [mem_map_equiv]
    change (a.symm x).val ∈ D ⊔ (P : Subgroup Y) ↔ x.val ∈ D ⊔ (P : Subgroup Y)
    rw [MulAut.conjNormal_symm_apply]
    exact ((mem_normalizer_iff''.mp
      ((D ⊔ (P : Subgroup Y)).le_normalizer (show d ∈ D ⊔ (P : Subgroup Y) from (show D ≤ D ⊔ (P : Subgroup Y) from le_sup_left) hdD))) x.val).symm
  have he := Theory.SpecificGroups.Classical.SylowMarkedSL2.automorphism_preserves_sl2_five_of_solvable_intersection hgens hbound (R.subgroupOf K) J
    ((subgroupOfEquivOfLe hRK).trans eR) hF S hSR hSJ hJs hJd a hJ
  rw [mem_normalizer_iff_map_conj_eq]
  have hh := congrArg (Subgroup.map K.subtype) he
  rw [map_map,map_subgroupOf_eq_of_le hRK] at hh
  have hf : K.subtype.comp a.toMonoidHom = (MulAut.conj d).toMonoidHom.comp K.subtype := by
    ext x; rfl
  rw [hf,←map_map,map_subgroupOf_eq_of_le hRK] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G]

private theorem source_unitary_five_exclusion
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
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 5 ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 5) : False := by
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
    (by rcases hm with hm | hm; exact .inr (.inl hm); exact .inr (.inr (.inr hm)))).2
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
  have hsol : Group.IsSolvable (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) := by
    rw [hjoin]
    let := d.actor_join_solvable h hH c hd
    let : Group.IsSolvable ((D ⊔ normalizingSylow T R).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (sup_le hDX hTX)).toMonoidHom)
        (subgroupOfEquivOfLe (sup_le hDX hTX)).injective
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hmK : ClassicalGroup.IsPSU Kbar 3 5 ∨ Chapter1.Section02.LocalModels.IsSU Kbar 3 5 := by
    rcases hm with hm | ⟨F,_,_,J,hF,hf,⟨e⟩⟩
    · exact .inl (hm.of_mulEquiv eK)
    · exact .inr ⟨F,inferInstance,inferInstance,J,hF,hf,⟨eK.trans e⟩⟩
  have hnorm := unitary_five_actor_normalizes Kbar Rbar Dbar (map_mono (comap_mono hRK))
    P hPR hmK hRfive hsol hdiv
  have hbot : Dbar = ⊥ := disjoint_self.mp (hdis.mono_right hnorm)
  change Nat.card Dbar = 5 at hc
  rw [hbot] at hc
  norm_num at hc

/-- The actual smaller-Sylow A₅ branch has no odd-prime unitary container,
including the distinct special unitary cover. -/
theorem LocalData.changedSylow_A5_unitary_exclusion
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
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q) : False := by
  have hternary : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q ∨
      ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q := by
    rcases hm with hm | hm
    · exact .inr (.inl hm)
    · exact .inr (.inr (.inr hm))
  obtain ⟨rfl,rfl,_,_⟩ := d.changedSylow_A5_odd_ternary h hH hgen hthree c hd hz hs
    P hP hKX hRK hK hA5 hq ho hternary
  exact source_unitary_five_exclusion d h hH c hd hz
    (Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right le_sup_left) hRK hKX hK hKn hA5 hm

open Chapter1.Section02 LocalModels

/-- Remove both unitary rows from the literal remaining A₅ containing catalogue.
The special unitary row is excluded with its cubic center intact. -/
theorem LocalData.changedSylow_A5_remaining_nonunitary
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
        (Nonempty (I ≃* Janko4.Model) ∨ ClassicalGroup.IsPSL I 3 5)) ∨
      A36Natural I ∨ A36Nilpotent I) := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X :=
    Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right le_sup_left
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let e : I ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  obtain ⟨hc,hcases⟩ := d.remaining_A5_source_container h hH hSyl hRX hKX hRK hK hA5 hm
  refine ⟨hc,?_⟩
  rcases hcases with ⟨hi,hsimple,hj | hl | hu⟩ | ⟨_,_,hu⟩ | hn | hn
  · exact .inl ⟨hi,hsimple,.inl hj⟩
  · exact .inl ⟨hi,hsimple,.inr hl⟩
  · exact (d.changedSylow_A5_unitary_exclusion h hH hgen hthree c hd hz hs P hP
      hKX hRK hK hKn hA5 (by decide : Nat.Prime 5) (by decide)
      (.inl (hu.of_mulEquiv e.symm))).elim
  · obtain ⟨F,_,_,J,hF,hf,⟨a⟩⟩ := hu
    exact (d.changedSylow_A5_unitary_exclusion h hH hgen hthree c hd hz hs P hP
      hKX hRK hK hKn hA5 (by decide : Nat.Prime 5) (by decide)
      (.inr ⟨F,inferInstance,inferInstance,J,hF,hf,⟨e.symm.trans a⟩⟩)).elim
  · exact .inr (.inl hn)
  · exact .inr (.inr hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
