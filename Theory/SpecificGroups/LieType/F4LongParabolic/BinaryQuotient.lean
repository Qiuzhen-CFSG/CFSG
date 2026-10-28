module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryLevi
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.RadicalFree
public import Mathlib.GroupTheory.Complement
public import Theory.Quasithin.CoprimeRank
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# The original two-core and component in the binary F4 matrix parabolic

The explicit Levi equivalence identifies P/E with SL3(2), so E is exactly
O2(P). The perfect residual L is a C-component and L/O2(L) has the same
binary linear model. If the centralizer of E surjected onto the simple
quotient, it would contain L; the existing explicit noncommuting pair rules
this out. Thus E is self-centralizing and F*(P)=E. Odd prime ranks descend
through E and are bounded using the order 168 of the quotient.

All groups are the literal matrix subgroups in `BinaryCoordinates`; these
results do not assume the desired centrality or an MS classification.
The source consumer is `MS93.OriginalAction.F4SourceHypotheses`, testing the
remaining original-action gap in Aschbacher--Smith C.1.31--34, pp.135--137.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates
namespace QuotientModel
private theorem sl_simple : IsSimpleGroup Matrix.PSL3Two.SL := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup
private theorem simple_core_bot {B : Type*} [Group B] [Finite B]
    [IsSimpleGroup B] [Group.IsPerfect B] : pCore 2 B = ⊥ := by
  rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 B :=
      (h ▸ (pCore_isPGroup (p := 2) (G := B))).of_equiv topEquiv
    exact (Group.IsPerfect.not_isNilpotent B hp.isNilpotent).elim
private theorem equiv_core_bot {B : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] (f : B ≃* Matrix.PSL3Two.SL) : pCore 2 B = ⊥ := by
  let : IsSimpleGroup Matrix.PSL3Two.SL := sl_simple
  let : IsSimpleGroup B := f.isSimpleGroup
  exact simple_core_bot
private theorem SL_pCore : pCore 2 Matrix.PSL3Two.SL = ⊥ := by
  let : IsSimpleGroup Matrix.PSL3Two.SL := sl_simple
  let : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
  exact simple_core_bot
private theorem A_pCore : pCore 2 A = ⊥ := by
  let := A_isPerfect
  exact equiv_core_bot leviEquiv
private theorem EA_bot : E.subgroupOf A = ⊥ := by
  let : (E.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer A_normalizes_E
  have hp := E_isPGroup.comap_of_injective A.subtype A.subtype_injective
  exact le_bot_iff.mp ((show E.subgroupOf A ≤ pCore 2 A from le_sSup ⟨inferInstance, hp⟩).trans_eq (A_pCore))
instance E_normal : (E.subgroupOf P).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show E ≤ P from le_sup_left)).mpr
    (sup_le E.le_normalizer A_normalizes_E)
private theorem complement : (A.subgroupOf P).IsComplement' (E.subgroupOf P) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    intro x hA hE
    have hx : (⟨(x : Matˣ), hA⟩ : A) ∈ E.subgroupOf A := hE
    rw [EA_bot] at hx
    have he := congrArg (fun a : A => (a : Matˣ)) (show (⟨(x : Matˣ), hA⟩ : A) = 1 from hx)
    exact Subtype.ext he
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ A.subgroupOf P ⊔ E.subgroupOf P := by
      rw [← subgroupOf_sup (show A ≤ P from le_sup_right) (show E ≤ P from le_sup_left),
        sup_comm A E]
      exact x.property
    exact mem_sup_of_normal_right.mp hx
noncomputable def quotientEquiv : (P ⧸ E.subgroupOf P) ≃* Matrix.PSL3Two.SL :=
  (complement).QuotientMulEquiv.trans ((subgroupOfEquivOfLe (show A ≤ P from le_sup_right)).trans leviEquiv)
noncomputable def projection : P →* Matrix.PSL3Two.SL :=
  (quotientEquiv).toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf P))
theorem projection_surjective : Function.Surjective (projection) :=
  (quotientEquiv).surjective.comp (QuotientGroup.mk'_surjective _)
theorem projection_ker : (projection).ker = E.subgroupOf P := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ (quotientEquiv).injective,
    QuotientGroup.ker_mk']
theorem core_eq : pCore 2 P = E.subgroupOf P := by
  let : IsSimpleGroup Matrix.PSL3Two.SL := sl_simple
  have hp : IsPGroup 2 (E.subgroupOf P) := E_isPGroup.comap_of_injective P.subtype P.subtype_injective
  have hbot := SL_pCore
  have hk : IsPGroup 2 (projection).ker := (projection_ker).symm ▸ hp
  have he := (projection).comap_pCore_of_ker_isPGroup (projection_surjective) hk
  rw [hbot, MonoidHom.comap_bot, projection_ker] at he
  exact he.symm

theorem L_component : (L.subgroupOf P).IsCComponent := by
  let : IsSimpleGroup Matrix.PSL3Two.SL := sl_simple
  let : Group.IsPerfect A := A_isPerfect
  let : Group.IsPerfect Matrix.PSL3Two.SL :=
    Group.IsPerfect.ofSurjective (f := leviEquiv.toMonoidHom) leviEquiv.surjective
  let : IsSimpleGroup (⊤ : Subgroup Matrix.PSL3Two.SL) := topEquiv.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup Matrix.PSL3Two.SL) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := Matrix.PSL3Two.SL)).symm.toMonoidHom)
      (topEquiv (G := Matrix.PSL3Two.SL)).symm.surjective
  have ht : (solvableResidual Matrix.PSL3Two.SL).IsCComponent := by
    rw [solvableResidual_eq_top]
    exact isCComponent_of_isSimpleGroup_of_isPerfect .top
  have hp : IsPGroup 2 (projection).ker := (projection_ker).symm ▸
    E_isPGroup.comap_of_injective P.subtype P.subtype_injective
  let : Group.IsNilpotent (projection).ker := hp.isNilpotent
  have hr := residual_isCComponent_of_surjective (projection) (projection_surjective) ht
  have he : solvableResidual P = L.subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [L_eq_residual, map_subgroupOf_eq_of_le L_le_P]
  exact he ▸ hr

private theorem LE : L ⊔ E = P :=
  le_antisymm (sup_le L_le_P le_sup_left)
    (sup_le le_sup_right ((show A ≤ L from le_sup_left).trans le_sup_left))
noncomputable def componentProjection : L →* Matrix.PSL3Two.SL :=
  (projection).comp (inclusion L_le_P)
theorem componentProjection_surjective : Function.Surjective (componentProjection) := by
  intro y
  obtain ⟨x, rfl⟩ := projection_surjective y
  have hx : x ∈ L.subgroupOf P ⊔ E.subgroupOf P := by
    rw [← subgroupOf_sup L_le_P (show E ≤ P from le_sup_left), LE, subgroupOf_self]
    trivial
  obtain ⟨l,hl,z,hz,hx⟩ := mem_sup_of_normal_right.mp hx
  refine ⟨⟨(l : Matˣ),hl⟩, ?_⟩
  change projection l = projection x
  have hzK : z ∈ (projection).ker := (projection_ker).symm ▸ hz
  rw [← hx, map_mul, show projection z = 1 from hzK, mul_one]
theorem componentProjection_ker : (componentProjection).ker = pCore 2 L := by
  have hk : (componentProjection).ker = E.subgroupOf L := by
    rw [componentProjection, ← MonoidHom.comap_ker, projection_ker]
    rfl
  have hp : IsPGroup 2 (componentProjection).ker := hk.symm ▸
    E_isPGroup.comap_of_injective L.subtype L.subtype_injective
  have hbot := SL_pCore
  have he := (componentProjection).comap_pCore_of_ker_isPGroup
    (componentProjection_surjective) hp
  simpa only [hbot, MonoidHom.comap_bot] using he
noncomputable def componentQuotientEquiv : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
  (QuotientGroup.quotientMulEquivOfEq (componentProjection_ker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (componentProjection_surjective))

/-- The original radical is self-centralizing; the nontrivial Levi action
excludes a centralizing normal supplement to the simple quotient. -/
theorem core_selfCentralizing : centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
  let : IsSimpleGroup Matrix.PSL3Two.SL := sl_simple
  let C := centralizer (E.subgroupOf P : Set P)
  let : C.Normal := inferInstance
  have hn : (C.map (projection)).Normal :=
    (inferInstance : C.Normal).map _ (projection_surjective)
  rcases hn.eq_bot_or_eq_top with hc | hc
  · have hh : C ≤ (projection).ker := (Subgroup.map_eq_bot_iff C).mp hc
    simpa only [core_eq, projection_ker] using hh
  · have hgen : C ⊔ E.subgroupOf P = ⊤ := by
      have hh := congrArg (comap (projection)) hc
      simpa only [comap_map_eq, projection_ker, comap_top] using hh
    have hq : IsPGroup 2 (P ⧸ C) := isPGroup_quotient_of_sup_eq_top C
      (E.subgroupOf P) (E_isPGroup.comap_of_injective P.subtype P.subtype_injective) hgen
    let : Group.IsNilpotent (P ⧸ C) := hq.isNilpotent
    let : Group.IsPerfect L := L_isPerfect
    let : Group.IsPerfect (L.subgroupOf P) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe L_le_P).symm.toMonoidHom)
        (subgroupOfEquivOfLe L_le_P).symm.surjective
    have hl : L.subgroupOf P ≤ C := le_of_isPerfect_of_solvable_quotient _ _
    have hhL : h ∈ L := by
      have hD : D ≤ L := le_sup_right
      exact hD ((commutator_le_self D)
        ((commutator_mono (commutator_le_self D) le_rfl) h_mem_third))
    have hh := hl (show (⟨h,L_le_P hhL⟩ : P) ∈ L.subgroupOf P from hhL)
      (⟨x,(show E ≤ P from le_sup_left) (root_mem 13)⟩ : P) (root_mem 13)
    exact (h_does_not_commute_x (congrArg Subtype.val hh).symm).elim
theorem fitting_eq_core : Theory.GroupTheory.generalizedFitting P = pCore 2 P :=
  Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2 (core_selfCentralizing)
/-- Every odd prime rank is at most two, on the original matrix group. -/
theorem odd_primeRank_le_two (p : ℕ) [Fact p.Prime] (ho : Odd p) : primeRank p P ≤ 2 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (E.subgroupOf P)
    (E_isPGroup.comap_of_injective P.subtype P.subtype_injective),
    primeRank_congr p (quotientEquiv)]
  apply (primeRank_le_iff_elementary_card_le Matrix.PSL3Two.SL).mpr
  intro B hB
  let := hB
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p B).exists_card_eq
  have hd : p ^ n ∣ 168 := by
    rw [← hn, ← Matrix.PSL3Two.card_SL]
    exact B.card_subgroup_dvd_card
  have hn2 : n ≤ 2 := by
    by_contra hn2
    have hd3 : p ^ 3 ∣ 168 := (pow_dvd_pow p (by omega : 3 ≤ n)).trans hd
    have hp : p.Prime := Fact.out
    have hpos : 0 < p := hp.pos
    have hb : p ^ 3 ≤ 168 := Nat.le_of_dvd (by decide) hd3
    have hlt : p ≤ 5 := by
      by_contra hh
      have ht := Nat.pow_le_pow_left (show 6 ≤ p by omega) 3
      norm_num at ht
      omega
    have hnop : ∀ p : Fin 6, Nat.Prime p.val → Odd p.val → ¬ p.val ^ 3 ∣ 168 := by decide
    exact hnop ⟨p, by omega⟩ hp ho hd3
  rw [hn]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn2
end QuotientModel
end Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates
