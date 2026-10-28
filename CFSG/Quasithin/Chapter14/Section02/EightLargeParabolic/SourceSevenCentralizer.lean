module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTripleModule
public import Theory.Representation.SL2.EightTripleTorus
public import Theory.Representation.BinaryConjugationSection.CoprimeFixedCard
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Order-seven centralizers in the original eight-field core

Every specified order-seven subgroup of the original H survives its full
two-core quotient. Its action on the literal extraspecial central quotient
has a binary fixed plane. Coprime lifting restores the full center of order
two, so its centralizer inside the original full core has order eight.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- Every literal subgroup of order seven in H has centralizer of order
eight inside the original full H-core. -/
theorem source_seven_core_centralizer (A : Subgroup G) (hAH : A ≤ H)
    (hA : Nat.card A = 7) :
    Nat.card (H.pCoreIn 2 ⊓ centralizer (A : Set G) : Subgroup G) = 8 := by
  classical
  let Q := H.pCoreIn 2
  obtain ⟨he,Z,hZ,hN,hel,ρ,d,hcoord,hi,hquot,htriple⟩ :=
    SourceTripleModule.source_core_triple hG T hempty hM hu hmany hcard e H hH eR
  let _ := he
  let _ := hN
  let _ := hel
  let V := Additive (Q ⧸ Z.subgroupOf Q)
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let ε := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  let eSL := ε.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let π := QuotientGroup.mk' (pCore 2 H)
  let q : H →* SL(2,GaloisField 2 3) := eSL.toMonoidHom.comp π
  let σ : Representation (ZMod 2) SL(2,GaloisField 2 3) V := ρ.comp eSL.symm.toMonoidHom
  let A₀ := A.subgroupOf H
  have hA₀ : Nat.card A₀ = 7 := (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA
  have hQ : Nat.card Q = 512 := (source_core_orders hG T hempty hM hu hmany hcard e H hH eR).1
  have hker : q.ker = pCore 2 H := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective π eSL.toMonoidHom eSL.injective,QuotientGroup.ker_mk']
  have hkcard : Nat.card q.ker = 512 := by
    rw [hker]
    simpa only [Q,pCoreIn,card_map_of_injective H.subtype_injective] using hQ
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hA₀p : IsPGroup 7 A₀ := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hA₀)
  have hinj : Function.Injective (q.comp A₀.subtype) :=
    injective_comp_subtype_of_coprime_ker q (by rw [hkcard]; decide) A₀ hA₀p
  have himage : Nat.card (A₀.map q) = 7 := by
    have hr : (q.comp A₀.subtype).range = A₀.map q := by rw [MonoidHom.range_comp,range_subtype]
    rw [←hr,←Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hA₀
  have hf : Module.finrank (ZMod 2) (fixedSpace σ (A₀.map q)) = 2 :=
    Representation.SL2.BinarySmall.TripleFixedSpaces.binary_seven_fixed_finrank
      (GaloisField.card 2 3 (by decide)) σ htriple (A₀.map q) himage
  have hspace : fixedSpace (ρ.comp π) A₀ = fixedSpace σ (A₀.map q) := by
    rw [←fixedSpace_comp_map]
    congr 1
    ext h v
    change ρ (π h) v = ρ (eSL.symm (eSL (π h))) v
    rw [eSL.symm_apply_apply]
  have hfixed : Nat.card (fixedSpace (ρ.comp π) A₀) = 4 := by
    rw [hspace,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hf]
    decide
  have hz2 : Nat.card Z = 2 := by
    rw [hZ,centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.center_order_p 2 Q
  have hZA : Z ≤ centralizer (A : Set G) := by
    rw [hZ]
    exact centerIn_centralizes_of_card_two (hZ ▸ hz2) (hAH.trans d.normalized)
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  have hc := d.coprime_fixed_card A hAH (inferInstance : Group.IsSolvable Q)
    (by rw [hA,hQ]; decide)
  rw [hfixed,inf_eq_left.mpr hZA,hz2] at hc
  exact hc

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizer
