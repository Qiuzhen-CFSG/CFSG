module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceExtraspecial
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReducedPair
public import Theory.Representation.SL2.EightTriple

/-!
# The original eight-field core quotient is the triple tensor module

The original full core Q of H is extraspecial, and its actual conjugation
action on Q/Z(Q) has 256 elements and is irreducible over the binary field.
Along the source quotient identification H/O₂(H) = PSL₂(8), the scalar
extension of this very action is the natural tensor and its two Frobenius
twists. The canonical quotient coordinates and the source center equality
are retained, without assuming an action comparison or a highest weight.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTripleModule
variable {G : Type*} [Group G]

/-- The original core and quotient coordinates together with an equivariant
triple-tensor identification for the specified full parabolic quotient map. -/
@[expose] def HasTripleExtraspecialCore (P : Subgroup G)
    (ε : (P ⧸ pCore 2 P) ≃* Theory.PSL2.BinaryGroup 3) : Prop :=
  let Q := P.pCoreIn 2
  IsExtraspecial 2 Q ∧ ∃ C : Subgroup G, C = centerIn Q ∧
    ∃ hN : (C.subgroupOf Q).Normal, letI := hN
      ∃ hel : IsElementaryAbelian 2 (Q ⧸ C.subgroupOf Q), letI := hel
        ∃ ρ : Representation (ZMod 2) (P ⧸ pCore 2 P) (Additive (Q ⧸ C.subgroupOf Q)),
          ∃ d : Representation.BinaryConjugationSection P Q C
              (ρ.comp (QuotientGroup.mk' (pCore 2 P))),
            (∀ q : Q, (d.coordinates q).toAdd =
              Additive.ofMul (QuotientGroup.mk' (C.subgroupOf Q) q)) ∧
            ρ.IsIrreducible ∧ Nat.card (Q ⧸ C.subgroupOf Q) = 256 ∧
            Representation.SL2.BinarySmall.IsTriple
              (ρ.comp (ε.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm).symm.toMonoidHom)

private theorem triple_core_of_structure [Finite G] (P : Subgroup G)
    (ε : (P ⧸ pCore 2 P) ≃* Theory.PSL2.BinaryGroup 3)
    (hs : HasIrreducibleExtraspecialCore P) : HasTripleExtraspecialCore P ε := by
  obtain ⟨he,C,hC,hN,hel,ρ,d,hcoord,hi,hcard⟩ := hs
  let _ := hN
  let _ := hel
  let _ := hi
  let V := Additive (P.pCoreIn 2 ⧸ C.subgroupOf (P.pCoreIn 2))
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let eSL := ε.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let σ : Representation (ZMod 2) SL(2,GaloisField 2 3) V := ρ.comp eSL.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff eSL.symm.toMonoidHom eSL.symm.surjective ρ).mpr hi
  have hd : Module.finrank (ZMod 2) V = 8 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod] at hc
    have hp : 2 ^ Module.finrank (ZMod 2) V = 2 ^ 8 := hc.symm.trans hcard
    exact Nat.pow_right_injective (by decide : 1 < 2) hp
  exact ⟨he,C,hC,hN,hel,ρ,d,hcoord,hi,hcard,
    Representation.SL2.BinarySmall.eight_irreducible_isTriple σ hd⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
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

/-- The actual H-core's canonical binary conjugation module is the triple
Frobenius tensor along the original source quotient equivalence. -/
theorem source_core_triple : HasTripleExtraspecialCore H
    (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR) :=
  triple_core_of_structure H _ (source_core_structure hG T hempty hM hu hmany hcard e H hH eR)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTripleModule
