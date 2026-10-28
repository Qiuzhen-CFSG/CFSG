module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Module
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The order formula for the binary almost-special group

The two marked summands have equal dimension, while the natural binary
plane has dimension two. Hence the dimension of W/S₂ is precisely the
natural multiplicity. The quotient map then computes |W:S₂|, and the
index-two image of U and |V|=4 give G.2.3(7).

Source: Aschbacher–Smith, G.2.3(7), printed pp.333–334.
-/

open Subgroup InvertedCubicTensor
open scoped _root_.TensorProduct

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem imageSpace_card {H S E : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) H M}
    (d : Representation.BinaryConjugationSection H S E ρ)
    (B : Subgroup G) (hBS : B ≤ S) :
    Nat.card (d.imageSpace B) = E.relIndex B := by
  change Nat.card ((B.subgroupOf S).map d.coordinates) = _
  rw [← relIndex_ker, d.kernel_eq]
  have he := relIndex_map_map_of_injective (E.subgroupOf S) (B.subgroupOf S)
    S.subtype_injective
  rw [map_subgroupOf_eq_of_le d.kernel_le, map_subgroupOf_eq_of_le hBS] at he
  exact he.symm

/-- Clause (7), with the exponent tied to the multiplicity of the actual
natural-module equivalence, rather than an independent numerical witness. -/
public theorem binary_order_of_natural_quotient (D : Setup G) (g : G)
    (hg : g ∈ D.I g)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2)
    (hVE : D.V ≤ D.S₂ g) (hES : D.S₂ g ≤ D.S g)
    (hVcard : Nat.card D.V = 4)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (σ : Representation (ZMod 2) S₃ M)
    (d : Representation.BinaryConjugationSection (D.I g) (D.S g)
      (D.S₂ g) (σ.comp (D.binaryCoreProjection g e)))
    (j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] M) :
    Nat.card D.U = 2 ^ (Module.finrank (ZMod 2) (multiplicitySpace σ) + 3) *
      D.V.relIndex (D.S₂ g) := by
  have hs := D.binary_core_factorization g hg e hnorm hindex
  have hc := d.isCompl_imageSpace (D.W g) (conjugate (D.W g) g) hs
    (D.binary_marked_intersection g hg hES)
  have hconj := d.imageSpace_conjBy (D.W g)
    (show D.W g ≤ D.S g from inf_le_right) (⟨g, hg⟩ : D.I g)⁻¹
  change d.imageSpace (conjugate (D.W g) g) =
    (d.imageSpace (D.W g)).map (σ (D.binaryCoreProjection g e (⟨g, hg⟩ : D.I g)⁻¹)) at hconj
  have hdim : Module.finrank (ZMod 2) (d.imageSpace (conjugate (D.W g) g)) =
      Module.finrank (ZMod 2) (d.imageSpace (D.W g)) := by
    rw [hconj]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      (σ.asGroupHom (D.binaryCoreProjection g e (⟨g, hg⟩ : D.I g)⁻¹))).finrank_map_eq _
  have htotal := Submodule.finrank_add_eq_of_isCompl hc
  have htensor := j.finrank_eq
  rw [Module.finrank_tensorProduct, BinaryPermutation.finrank_core] at htensor
  simp only [Fintype.card_fin] at htensor
  have hmult : Module.finrank (ZMod 2) (d.imageSpace (D.W g)) =
      Module.finrank (ZMod 2) (multiplicitySpace σ) := by omega
  have hquot : (D.S₂ g).relIndex (D.W g) =
      2 ^ Module.finrank (ZMod 2) (multiplicitySpace σ) := by
    rw [← imageSpace_card d (D.W g) inf_le_right,
      Module.natCard_eq_pow_finrank (K := ZMod 2), hmult]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  have hEW : D.S₂ g ≤ D.W g := le_inf inf_le_left hES
  have ht := relIndex_mul_relIndex (D.S₂ g) (D.W g) D.U hEW inf_le_left
  have hv := relIndex_mul_relIndex D.V (D.S₂ g) D.U hVE inf_le_left
  have hb := relIndex_mul_relIndex (⊥ : Subgroup G) D.V D.U bot_le
    (hVE.trans inf_le_left)
  rw [relIndex_bot_left, relIndex_bot_left, hVcard] at hb
  rw [hquot, hindex] at ht
  rw [← hv, ← ht] at hb
  rw [← hb, pow_add]
  ring

end CFSG.Quasithin.ChapterG.Section02.Setup
