module
public import Theory.SpecificGroups.SL2.EvenBorelResidual.NaturalFixed
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
/-!
# Natural block fixed points of a higher-field Borel residual

Conjugating a Sylow subgroup to the upper root group transports the actual
Borel residual and its zero fixed space. The defining natural block model
then puts every residual-fixed element of U(L) in C_U(L). This retains the
central covering layers and the original quotient map L -> L/O₂(L).

Source: Aschbacher--Smith15.3.18, pp.1126--1127; the higher-field natural
fixed-space calculation is shared with13.6.18.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC

private theorem natural_sylowNormalizer_residual_fixed
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n) (P : Sylow 2 SL(2,F)) :
    fixedSpace (HigherFieldBorelFixedSpaces.binaryNatural (F := F) 2)
      ((piResidual twoThreePrimes (normalizer (P : Set SL(2,F)))).map
        (normalizer (P : Set SL(2,F))).subtype) = ⊥ := by
  let ρ := HigherFieldBorelFixedSpaces.binaryNatural (F := F) 2
  let B := normalizer (P : Set SL(2,F))
  let N := (piResidual twoThreePrimes B).map B.subtype
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) P (upperUnipotentSylow F 2)
  have hP : (P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F := by
    change ((a • P : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have hB : B.map (MulAut.conj a).toMonoidHom = rankOneBorel F := by
    calc
      _ = normalizer ((P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom : Set SL(2,F)) :=
        map_equiv_normalizer_eq (P : Subgroup SL(2,F)) (MulAut.conj a)
      _ = rankOneBorel F := by rw [hP]
  have hN : N.map (MulAut.conj a).toMonoidHom = RankOneResidual.residual (F := F) := by
    change ((piResidual twoThreePrimes B).map B.subtype).map _ = _
    rw [map_embedded_piResidual,hB]
  have he := fixedSpaceConjEquiv ρ N a
  have hz : fixedSpace ρ (N.map (MulAut.conj a).toMonoidHom) = ⊥ := by
    rw [hN]
    exact RankOneResidual.natural_fixedSpace hn hF
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hh : he ⟨v,hv⟩ = 0 := by
    apply Subtype.ext
    exact (Submodule.mem_bot (R := ZMod 2)).mp (hz ▸ (he ⟨v,hv⟩).property)
  exact congrArg Subtype.val (he.injective (hh.trans he.map_zero.symm))

/-- A higher-field Borel residual fixes no noncentral vector of the literal
natural block module. The marking uses the original quotient map. -/
theorem natural_block_residual_fixed_le_center
    {L F : Type*} [Group L] [Finite L] [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n)
    (r : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel L r)
    (hr : ∀ (g : SL(2,F)) (v : Multiplicative (Fin 2 → F)),
      (r g v).toAdd = Representation.specialLinearNatural (k := F) 2 g v.toAdd)
    (B : Subgroup L) (P : Sylow 2 SL(2,F))
    (hB : B.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
      normalizer (P : Set SL(2,F))) :
    blockU L ⊓ centralizer
      (((piResidual twoThreePrimes B).map B.subtype : Subgroup L) : Set L) ≤ center L := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let N := (piResidual twoThreePrimes B).map B.subtype
  have hN : N.map q = (piResidual twoThreePrimes (normalizer (P : Set SL(2,F)))).map
      (normalizer (P : Set SL(2,F))).subtype := by
    change ((piResidual twoThreePrimes B).map B.subtype).map _ = _
    rw [map_embedded_piResidual,hB]
  rintro u ⟨hu,hc⟩
  let v := (m.moduleIso (QuotientGroup.mk' (blockFixed L) ⟨u,hu⟩)).toAdd
  have hv : v ∈ fixedSpace (HigherFieldBorelFixedSpaces.binaryNatural (F := F) 2)
      ((piResidual twoThreePrimes (normalizer (P : Set SL(2,F)))).map
        (normalizer (P : Set SL(2,F))).subtype) := by
    intro g
    obtain ⟨l,hl,he⟩ := (show (g : SL(2,F)) ∈ N.map q from hN.symm ▸ g.property)
    have hconj : blockConjugate L l ⟨u,hu⟩ = ⟨u,hu⟩ := by
      apply Subtype.ext
      change l*u*l⁻¹=u
      rw [(mem_centralizer_iff.mp hc) l hl,mul_inv_cancel_right]
    have hh := congrArg Multiplicative.toAdd (m.intertwining l ⟨u,hu⟩)
    rw [hconj,hr] at hh
    change HigherFieldBorelFixedSpaces.binaryNatural 2 g v = v
    rw [←he]
    exact hh.symm
  rw [natural_sylowNormalizer_residual_fixed hn hF P,Submodule.mem_bot] at hv
  have hm : m.moduleIso (QuotientGroup.mk' (blockFixed L) ⟨u,hu⟩) = 1 :=
    Multiplicative.toAdd.injective hv
  change (⟨u,hu⟩ : blockU L) ∈ blockFixed L
  exact (QuotientGroup.eq_one_iff (⟨u,hu⟩ : blockU L)).mp (m.moduleIso.map_eq_one_iff.mp hm)
end CFSG.Quasithin.ChapterC
