module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.Representation.SL2OrthogonalCover.Universal
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer

/-!
# The central kernel of a natural even-field rank-one block

The actual binary module U/C_U(L) is identified with its specified natural
SL₂ module. Binary self-duality and I.1.6 bound the kernel of the genuine
central cover U → U/C_U(L) by the field degree. If O₂(L)=U, this bounds
the whole center, as required in the recognition step of Lemma 2.4.8(4).
Source: Aschbacher–Smith, I.1.6 and Lemma 2.4.8, printed pp.408, 530.
-/

public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L]

theorem IsL2EvenBlock.dual_H1_finrank {n : ℕ} (h : IsL2EvenBlock L n) :
    letI := h.2.1.elementary
    letI := h.2.1.module_elementary
    Module.finrank (ZMod 2) (H1 (moduleRepresentation h.2.1).dual) = n := by
  let := h.2.1.finite
  let := h.2.1.elementary
  let := h.2.1.module_elementary
  obtain ⟨F,_,_,hF,_,r,⟨m⟩,hm⟩ := h.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let σ := SL2OrthogonalCover.binaryNatural (F := F)
  let e : Additive (BlockModule L) ≃ₗ[ZMod 2] (Fin 2 → F) :=
    { m.moduleIso.toAdditiveLeft with map_smul' := fun a v => ZMod.map_smul m.moduleIso.toAdditiveLeft a v }
  have he (g : L ⧸ pCore 2 L) (v : Additive (BlockModule L)) :
      e (moduleRepresentation h.2.1 g v) = σ (m.quotientIso g) (e v) := by
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
    obtain ⟨u,rfl⟩ := moduleProjection_surjective v
    rw [← moduleProjection_equivariant]
    change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L l u.toMul))) = _
    rw [m.intertwining]
    exact hm _ _
  have hed (g : Matrix.SpecialLinearGroup (Fin 2) F)
      (v : Module.Dual (ZMod 2) (Fin 2 → F)) :
      e.dualMap (σ.dual g v) =
        (moduleRepresentation h.2.1).dual (m.quotientIso.symm g) (e.dualMap v) := by
    ext u
    change v (σ g⁻¹ (e u)) = v (e (moduleRepresentation h.2.1 ((m.quotientIso.symm g)⁻¹) u))
    rw [he,m.quotientIso.map_inv,m.quotientIso.apply_symm_apply]
  have hd := H1Congr σ.dual (moduleRepresentation h.2.1).dual m.quotientIso.symm e.dualMap hed
  rw [← hd.finrank_eq]
  exact SL2OrthogonalCover.binary_dual_H1_finrank n h.1 hF

theorem IsL2EvenBlock.fixed_card_le {n : ℕ} (h : IsL2EvenBlock L n) :
    Nat.card (blockFixed L) ≤ 2 ^ n := by
  let := h.2.1.finite
  let := h.2.1.elementary
  let := h.2.1.module_elementary
  have hb := finrank_ker_le_H1_of_cover (projection h.2.1) (projection_isCover h.2.1)
  rw [h.dual_H1_finrank] at hb
  let e : blockFixed L ≃ (moduleProjection (L := L)).ker :=
    { toFun := fun v => ⟨Additive.ofMul v.val, (QuotientGroup.eq_one_iff _).mpr v.property⟩
      invFun := fun v => ⟨v.val.toMul, (QuotientGroup.eq_one_iff _).mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hb

theorem IsL2EvenBlock.center_le_module {n : ℕ} (h : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) : center L ≤ blockU L := by
  rw [← hcore, ← h.2.1.centralizer_blockU]
  exact center_le_centralizer _

theorem IsL2EvenBlock.center_card_le {n : ℕ} (h : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) : Nat.card (center L) ≤ 2 ^ n := by
  have hc := Nat.card_congr (subgroupOfEquivOfLe (h.center_le_module hcore)).toEquiv
  change Nat.card (blockFixed L) = Nat.card (center L) at hc
  rw [← hc]
  exact h.fixed_card_le
end CFSG.Quasithin.ChapterC
