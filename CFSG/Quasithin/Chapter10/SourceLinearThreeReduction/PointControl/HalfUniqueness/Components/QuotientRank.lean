module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Nonconstrained
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.MovedSize
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The original moved factor in a quasisimple containing quotient

The original factor modulo its fixed subgroup has at least eight elements.
A quasisimple containing component has central two-core, so quotienting by
that core kills only fixed elements of the conjugate moved factor. Its
literal image is therefore elementary abelian of order at least eight.
This gives two-rank at least three without a factor-of-five hypothesis.

The BinaryThree consumer combines this with the actual low-cubic-rank
Theorem C catalogue to finish the nonconstrained enlargement branch.
Source: Aschbacher--Smith 10.2.6, printed pp.748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Central two-cores cannot remove the original moved quotient of order at least eight. -/
theorem quasisimple_overgroup_quotient_twoRank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {s : G} {K : Subgroup G} [IsQuasisimple K]
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K) :
    3 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
  let c := (MulAut.conj s).toMonoidHom
  let U := (⁅D.fullModule,L⁆).map c
  let B := L.map c
  have hUB : U ≤ B := map_mono
    ((source_full_moved_le_component_core D).trans (L.pCoreIn_le 2))
  have hUK : U ≤ K := hUB.trans hBK
  let q := QuotientGroup.mk' (pCore 2 K)
  let W := U.subgroupOf K
  let E := W.map q
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map c
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUK
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hcard : Nat.card E = (K.pCoreIn 2).relIndex U := by
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    have hh := relIndex_map_map_of_injective (pCore 2 K) W K.subtype_injective
    rw [map_subgroupOf_eq_of_le hUK] at hh
    exact hh.symm
  have hcentral : K.pCoreIn 2 ≤ centralizer (B : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ b hb
    exact congrArg K.subtype (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 hx)
      ⟨b,hBK hb⟩)
  have hfixed : 8 ≤ (centralizer (B : Set G)).relIndex U := by
    change 8 ≤ (centralizer (L.map (MulAut.conj s).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom)
    rw [←Theory.Quasithin.map_centralizer (MulAut.conj s) L,
      relIndex_map_map_of_injective _ _ (MulAut.conj s).injective]
    exact SmallOffender.moved_fixed_quotient_card_ge_eight D
  have hlarge : 8 ≤ Nat.card E := by
    rw [hcard]
    exact hfixed.trans (relIndex_le_of_le_left hcentral (by
      change Nat.card (U ⧸ (K.pCoreIn 2).subgroupOf U) ≠ 0
      exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩))
  by_contra! hsmall
  have hc : Nat.card E ≤ 2 ^ 2 :=
    (primeRank_le_iff_elementary_card_le (K ⧸ pCore 2 K)).mp
      (by omega : primeRank 2 (K ⧸ pCore 2 K) ≤ 2) E inferInstance
  omega

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
