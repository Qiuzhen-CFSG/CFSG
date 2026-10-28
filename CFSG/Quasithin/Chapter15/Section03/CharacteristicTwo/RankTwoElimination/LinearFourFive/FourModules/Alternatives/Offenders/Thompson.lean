module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Offenders.Quotient
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Stability

/-!
# Actual Thompson offenders on the commutator module

The map from LR to L/O₂(L) acts on U_L by ambient conjugation, and
faithfulness of the original component representation identifies its kernel
with C_LR(U_L). The equality L = [L,J(R)] forces J(R) to have nontrivial
image. A maximum elementary subgroup of R with nontrivial image therefore
satisfies the binary offender inequality. An explicit equivariant linear
identification returns this offender to the original U_L representation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.4–7
and 15.3.16,24, printed pp.75–76 and 1126,1129.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders
variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
variable (hn : d.R ≤ normalizer (L : Set G))
  (hc : center (L ⧸ pCore 2 L) = ⊥)
  (hi : ∀ g : (L ⊔ d.R : Subgroup G),
    pCoreJoinAction 2 hn g ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L))
  (hW : d.componentSpan L ≤ L ⊔ d.R)
  (hred : IsR2Within (d.componentSpan L) (L ⊔ d.R))
  [IsElementaryAbelian 2 (spanCommutator d L)]
  (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))

include hW hred in
/-- The entire LR-action agrees with the specified component representation. -/
theorem coreMap_representation_apply (g : (L ⊔ d.R : Subgroup G))
    (u : Additive (spanCommutator d L)) :
    ((coreRepresentation d L hcore hR (coreMap d L hn hc hi g) u).toMul : G) =
      (g : G) * u.toMul * (g : G)⁻¹ := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (coreMap d L hn hc hi g)
  let i : L →* (L ⊔ d.R : Subgroup G) := inclusion le_sup_left
  have hk : i l⁻¹ * g ∈ (coreMap d L hn hc hi).ker := by
    change coreMap d L hn hc hi (i l⁻¹ * g) = 1
    rw [map_mul, show i l⁻¹ = (i l)⁻¹ from map_inv i l, map_inv,
      coreMap_on_component, hl, inv_mul_cancel]
  rw [coreMap_ker] at hk
  have hcu := core_centralizes_internal_span d L hred hk
  have hu : (⟨u.toMul, (spanCommutator_le_span d L).trans hW u.toMul.property⟩ :
      (L ⊔ d.R : Subgroup G)) ∈ (d.componentSpan L).subgroupOf (L ⊔ d.R) :=
    spanCommutator_le_span d L u.toMul.property
  have he := congrArg (fun x : (L ⊔ d.R : Subgroup G) => (x : G)) (hcu _ hu)
  change (u.toMul : G) * ((l : G)⁻¹ * (g : G)) =
    ((l : G)⁻¹ * (g : G)) * u.toMul at he
  rw [← hl, coreRepresentation_apply]
  symm
  calc
    (g : G) * u.toMul * (g : G)⁻¹ =
      (l : G) * ((l : G)⁻¹ * (g : G) * u.toMul) * (g : G)⁻¹ := by group
    _ = (l : G) * (u.toMul * ((l : G)⁻¹ * (g : G))) * (g : G)⁻¹ := by rw [← he]
    _ = (l : G) * u.toMul * (l : G)⁻¹ := by group

include hW hred in
/-- Faithfulness identifies the literal centralizer kernel needed by B.2.4. -/
theorem coreMap_centralizer_kernel
    (hfaith : Function.Injective (coreRepresentation d L hcore hR)) :
    (coreMap d L hn hc hi).ker =
      centralizer ((spanCommutator d L).subgroupOf (L ⊔ d.R) : Set (L ⊔ d.R : Subgroup G)) := by
  apply le_antisymm
  · rw [coreMap_ker]
    exact (core_centralizes_internal_span d L hred).trans
      (centralizer_le (comap_mono (spanCommutator_le_span d L)))
  · intro g hg
    change coreMap d L hn hc hi g = 1
    apply hfaith
    rw [map_one]
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coreMap_representation_apply d L hn hc hi hW hred]
    have he := congrArg (fun x : (L ⊔ d.R : Subgroup G) => (x : G))
      (hg ⟨u.toMul, (spanCommutator_le_span d L).trans hW u.toMul.property⟩ u.toMul.property)
    change (u.toMul : G) * g = (g : G) * u.toMul at he
    change (g : G) * u.toMul * (g : G)⁻¹ = u.toMul
    rw [← he, mul_inv_cancel_right]

omit [IsElementaryAbelian 2 (spanCommutator d L)] in
/-- The full Thompson commutator forces a nontrivial Thompson image. -/
theorem thompson_not_le_coreMap_ker [Nontrivial (L ⧸ pCore 2 L)]
    (hJ : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆) :
    ¬ Stellmacher.elementaryAbelianMaxJ (d.R.subgroupOf (L ⊔ d.R)) ≤
      (coreMap d L hn hc hi).ker := by
  intro hj
  have he : L.subgroupOf (L ⊔ d.R) =
      ⁅L.subgroupOf (L ⊔ d.R),
        Stellmacher.elementaryAbelianMaxJ (d.R.subgroupOf (L ⊔ d.R))⁆ := by
    apply map_injective (L ⊔ d.R).subtype_injective
    rw [map_subgroupOf_eq_of_le le_sup_left, map_commutator,
      map_subgroupOf_eq_of_le le_sup_left,
      ← Stellmacher.elementaryAbelianMaxJ_map_injective _ (L ⊔ d.R).subtype_injective,
      map_subgroupOf_eq_of_le le_sup_right]
    exact hJ
  have hL : L.subgroupOf (L ⊔ d.R) ≤ (coreMap d L hn hc hi).ker := by
    rw [he]
    exact (commutator_mono le_top hj).trans (commutator_le_right _ _)
  obtain ⟨x, hx⟩ := exists_ne (1 : L ⧸ pCore 2 L)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  apply hx
  rw [← coreMap_on_component d L hn hc hi l]
  exact hL l.property


open Representation.BinaryOffender

include hW hred in
/-- A genuine maximum elementary subgroup of R gives an offender on U_L. -/
theorem coreRepresentation_maxElementary_offender [Finite G]
    [Nontrivial (L ⧸ pCore 2 L)]
    (hfaith : Function.Injective (coreRepresentation d L hcore hR))
    (hLRcore : (L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hJ : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆) :
    ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (d.R.subgroupOf (L ⊔ d.R)),
      IsOffender (coreRepresentation d L hcore hR) (A.map (coreMap d L hn hc hi)) := by
  classical
  let H := L ⊔ d.R
  let U := (spanCommutator d L).subgroupOf H
  have hU : spanCommutator d L ≤ H := (spanCommutator_le_span d L).trans hW
  let _ : U.Normal := (normal_subgroupOf_iff_le_normalizer hU).mpr
    (commutator_normalizes d L hn hW hred)
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hU
  let q := coreMap d L hn hc hi
  have hq := coreMap_surjective d L hn hc hi
  have hk := coreMap_centralizer_kernel d L hn hc hi hW hred hcore hR hfaith
  let ρ := Representation.NormalElementaryQuotient.representation U q hq hk
  have hJR := thompson_not_le_coreMap_ker d L hn hc hi hJ
  have hex : ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (d.R.subgroupOf H),
      ¬ A ≤ q.ker := by
    by_contra! h
    exact hJR (sSup_le h)
  obtain ⟨A, hA, hne⟩ := hex
  have hρA : IsOffender ρ (A.map q) :=
    Representation.NormalElementaryQuotient.maxElementary_isOffender U q hq hk
      (d.R.subgroupOf H) A
      (comap_mono ((spanCommutator_le_span d L).trans (span_le_R d L hW hred hLRcore)))
      hA hne
  let E : Additive U ≃ₗ[ZMod 2] Additive (spanCommutator d L) :=
    LinearEquiv.ofBijective
      ((subgroupOfEquivOfLe hU).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hU).bijective
  have he : ∀ x v, E (ρ x v) = coreRepresentation d L hcore hR x (E v) := by
    intro x v
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [← coreMap_on_component d L hn hc hi l]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (((ρ (q (inclusion le_sup_left l)) v).toMul : H) : G) = _
    rw [coreMap_representation_apply d L hn hc hi hW hred]
    exact congrArg H.subtype (Representation.NormalElementaryQuotient.representation_apply
      U q hq hk (inclusion le_sup_left l) v)
  have ho := hρA.map_equivariant ρ (coreRepresentation d L hcore hR)
    (MonoidHom.id _) Function.injective_id E he
  rw [Subgroup.map_id] at ho
  exact ⟨A, hA, ho⟩

include hn hc hi hW hred in
/-- The original component representation is an FF-module. -/
theorem coreRepresentation_isFFModule [Finite G] [Nontrivial (L ⧸ pCore 2 L)]
    (hfaith : Function.Injective (coreRepresentation d L hcore hR))
    (hLRcore : (L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hJ : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆) :
    IsFFModule (coreRepresentation d L hcore hR) := by
  obtain ⟨A, _, hA⟩ := coreRepresentation_maxElementary_offender
    d L hn hc hi hW hred hcore hR hfaith hLRcore hJ
  exact ⟨_, hA⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders

end
