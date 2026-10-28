module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryAutomizer
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers

/-!
# Inner four-group fixed spaces on a marked binary doubled orbit

Transport the literal natural–dual fixed space along the unchanged component
marking. Every inner elementary four-group fixes eight vectors, and the
inner pointwise stabilizer is the four-group itself. Any further pointwise
fixer must normalize that inner stabilizer. The checked four-group normalizer
lies in the inner automorphism subgroup, excluding all additional fixers.

The actual chosen-module application is in
`NonFFSourceDoubledBinaryFixed`. It supplies the three-dimensional centralizer
in 7.6.1, with the full ambient automizer as pointwise actor.
Source: Aschbacher–Smith H.4.3(2) and 7.6.1, printed pp.380,702.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open BinaryLinearThree
open FourGroupGeometry

/-- The fixed space of every inner four-group has eight elements; its
pointwise stabilizer in the whole actor is exactly that four-group. -/
theorem doubledBinary_inner_four_fixed
    {H J U : Type*} [_root_.Group H] [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (i : J →* H)
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (hE : ∀ j v, E (ρ (i j) v) = BinaryLinearThree.NaturalDual.action (q j) (E v))
    (f : H ≃* MulAut Group) (hf : ∀ j, f (i j) = MulAut.conj (q j))
    (A : Subgroup H) (hAI : ∀ a ∈ A, f a ∈ MulAut.innerSubgroup Group)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) :
    Nat.card (fixedSpace ρ A) = 8 ∧
      ∀ b : H, (∀ v ∈ fixedSpace ρ A, ρ b v = v) → b ∈ A := by
  let B := A.map f.toMonoidHom
  have hBI : B ≤ MulAut.innerSubgroup Group := by
    rintro _ ⟨a,ha,rfl⟩
    exact hAI a ha
  let := hA
  have hBE : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBc : Nat.card B = 4 := (card_map_of_injective f.injective).trans hcard
  have hact (g : Group) (v : U) :
      E (ρ (f.symm (MulAut.conj g)) v) = BinaryLinearThree.NaturalDual.action g (E v) := by
    obtain ⟨j,rfl⟩ := hq g
    rw [← hf j, f.symm_apply_apply]
    exact hE j v
  have hmem (v : U) : E v ∈ naturalDualFixed B ↔ v ∈ fixedSpace ρ A := by
    rw [mem_naturalDualFixed]
    constructor
    · intro hv a
      obtain ⟨g,hg⟩ := hAI a a.property
      apply E.injective
      have he := hact g v
      rw [hg, f.symm_apply_apply] at he
      exact he.trans (hv g (hg ▸ mem_map_of_mem f.toMonoidHom a.property))
    · intro hv g hg
      obtain ⟨a,ha,he⟩ := hg
      have he' : f.symm (MulAut.conj g) = a := by rw [← he]; exact f.symm_apply_apply a
      change BinaryLinearThree.NaturalDual.action g (E v) = E v
      rw [← hact, he']
      exact congrArg E (hv ⟨a,ha⟩)
  obtain ⟨hfixed,hfixer⟩ := FixedSpaces.naturalDualFixed_geometry B hBI hBE hBc
  have hinner (b : H) (hb : f b ∈ MulAut.innerSubgroup Group)
      (hbfix : ∀ v ∈ fixedSpace ρ A, ρ b v = v) : b ∈ A := by
    obtain ⟨g,hg⟩ := hb
    have hgb : MulAut.conj g ∈ B := by
      apply hfixer
      intro w hw
      have he := hact g (E.symm w)
      rw [hg, f.symm_apply_apply, E.apply_symm_apply] at he
      have hv : E.symm w ∈ fixedSpace ρ A := (hmem _).mp (by rwa [E.apply_symm_apply])
      rw [hbfix _ hv, E.apply_symm_apply] at he
      exact he.symm
    rw [hg] at hgb
    simpa only [f.symm_apply_apply] using mem_map_equiv.mp hgb
  refine ⟨?_, ?_⟩
  · exact (Nat.card_congr (E.toEquiv.subtypeEquiv (fun v => (hmem v).symm))).trans hfixed
  · intro b hb
    let I := (MulAut.innerSubgroup Group).comap f.toMonoidHom
    have hN : normalizer (A : Set H) ≤ I := by
      intro c hc
      exact (inner_fourGroup_normalizer B hBI hBE hBc).1
        (A.le_normalizer_map f.toMonoidHom (mem_map_of_mem _ hc))
    have hinv (c : H) (hc : ∀ v ∈ fixedSpace ρ A, ρ c v = v) :
        ∀ v ∈ fixedSpace ρ A, ρ c⁻¹ v = v := by
      intro v hv
      have he := congrArg (ρ c⁻¹) (hc v hv)
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using he.symm
    have hconj (c : H) (hc : ∀ v ∈ fixedSpace ρ A, ρ c v = v)
        (a : H) (ha : a ∈ A) : c*a*c⁻¹ ∈ A := by
      apply hinner
      · exact (inferInstance : I.Normal).conj_mem a (hAI a ha) c
      · intro v hv
        simp only [map_mul, Module.End.mul_apply]
        rw [hinv c hc v hv]
        have hav : ρ a v = v := hv ⟨a,ha⟩
        rw [hav, hc v hv]
    have hn : b ∈ normalizer (A : Set H) := by
      rw [mem_normalizer_iff]
      intro a
      constructor
      · exact hconj b hb a
      · intro ha
        have he := hconj b⁻¹ (hinv b hb) _ ha
        simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he
    exact hinner b (hN hn) hb

end CFSG.Quasithin.Chapter7.NormalizedSource
