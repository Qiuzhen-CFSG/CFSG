module
public import Theory.Representation.BinaryPermutation.SevenNormalizer
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Extending a marked seven-letter conjugation action

The linear normalizer of the natural binary A₇ action consists of the
seven-letter permutation operators. Transporting through bijective coordinates
therefore extends a marked A₇ action to every common normalizer of the actor
and module. The extension preserves the original actor quotient and coordinates.

The proof uses Aut(A₇) = S₇ and the trivial linear centralizer on the
augmentation core; it makes no faithfulness assumption on the overgroup.
Source: Aschbacher--Smith, §B.3 and original 15.2.23, printed pp.1115--1117.
-/

public noncomputable section
open Subgroup BinaryPermutation
namespace BinaryPermutation

/-- The natural binary A₇ image has exactly the permutation normalizer. -/
theorem normalizer_alternatingSeven_naturalMulAction_le_range :
    normalizer ((alternatingGroup (Fin 7)).map (naturalMulAction (Fin 7)) :
      Set (MulAut (Multiplicative (natural (Fin 7))))) ≤
      (naturalMulAction (Fin 7)).range := by
  intro f hf
  let j := naturalMulAction (Fin 7)
  let A := alternatingGroup (Fin 7)
  let B := A.map j
  let e : A ≃* B := A.equivMapOfInjective j
    (naturalMulAction_injective_of_odd (Fin 7) (by decide))
  let a : MulAut B := B.normalizerMonoidHom ⟨f,hf⟩
  let φ : MulAut A := e.trans (a.trans e.symm)
  let F : natural (Fin 7) ≃ₗ[ZMod 2] natural (Fin 7) :=
    { AddEquiv.toMultiplicative.symm f with
      map_smul' := fun c v => ZMod.map_smul (AddEquiv.toMultiplicative.symm f) c v }
  have hF (g : A) (v : natural (Fin 7)) :
      F (naturalRepresentation (Fin 7) g.val v) =
        naturalRepresentation (Fin 7) (φ g).val (F v) := by
    have he : e (φ g) = a (e g) := e.apply_symm_apply _
    have hh := congrArg Subtype.val he
    change j (φ g).val = f * j g.val * f⁻¹ at hh
    have hm := mul_inv_eq_iff_eq_mul.mp hh.symm
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hm (Multiplicative.ofAdd v))
  let t := coreEquivNatural (Fin 7) (by decide)
  let c := t.trans (F.trans t.symm)
  have ht (g : Equiv.Perm (Fin 7)) (v : core (Fin 7)) :
      t (coreRepresentation (Fin 7) g v) = naturalRepresentation (Fin 7) g (t v) :=
    coreEquivNatural_equivariant (Fin 7) (by decide) g v
  have hc (g : A) (v : core (Fin 7)) :
      c (coreRepresentation (Fin 7) g.val v) =
        coreRepresentation (Fin 7) (φ g).val (c v) := by
    apply t.injective
    simp only [c,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
    rw [ht,hF,ht,LinearEquiv.apply_symm_apply]
  refine ⟨SevenNormalizer.permutationOfAut φ,?_⟩
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  have hh := congrArg t (SevenNormalizer.intertwiner c φ hc (t.symm v.toAdd))
  have hh' : naturalRepresentation (Fin 7) (SevenNormalizer.permutationOfAut φ)
      v.toAdd = F v.toAdd := by
    simpa only [c,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,ht] using hh.symm
  exact hh'
end BinaryPermutation

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]
/-- Extend the literal conjugation coordinates to their common normalizer. -/
theorem exists_seven_normalizer_action
    (H W N : Subgroup G) (hHN : H ≤ N) (hNW : N ≤ normalizer (W : Set G))
    (hNH : N ≤ normalizer (H : Set G))
    (q : H →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection H W ⊥
      ((alternatingNaturalRepresentation (Fin 7)).comp q)) :
    ∃ π : N →* Equiv.Perm (Fin 7),
      (∀ (n : N) (w : W),
        (c.coordinates ⟨(n : G) * w * (n : G)⁻¹,
          (mem_normalizer_iff.mp (hNW n.property) w).mp w.property⟩).toAdd =
          naturalRepresentation (Fin 7) (π n) (c.coordinates w).toAdd) ∧
      (∀ h : H, π (inclusion hHN h) = (q h).val) := by
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq, bot_subgroupOf]
  let E := MulEquiv.ofBijective c.coordinates ⟨hci, c.onto⟩
  let α : N →* MulAut (Multiplicative (natural (Fin 7))) :=
    (MulAut.congr E).toMonoidHom.comp (W.normalizerMonoidHom.comp (inclusion hNW))
  have hact (n : N) (w : W) : α n (c.coordinates w) =
      c.coordinates ⟨(n : G) * w * (n : G)⁻¹,
        (mem_normalizer_iff.mp (hNW n.property) w).mp w.property⟩ := by
    change E (W.normalizerMonoidHom (inclusion hNW n) (E.symm (E w))) = _
    rw [E.symm_apply_apply]
    rfl
  let j := naturalMulAction (Fin 7)
  have hj : Function.Injective j := naturalMulAction_injective_of_odd (Fin 7) (by decide)
  have hmark (h : H) : α (inclusion hHN h) = j (q h).val := by
    apply MulEquiv.ext
    intro v
    obtain ⟨w, rfl⟩ := c.onto v
    apply Multiplicative.toAdd.injective
    rw [hact]
    exact c.equivariant h w
  let K := H.subgroupOf N
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hHN).mpr hNH
  have him : K.map α = (alternatingGroup (Fin 7)).map j := by
    ext a
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨q ⟨h, hh⟩, (q ⟨h, hh⟩).property, (hmark ⟨h, hh⟩).symm⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨h, hh⟩ := hq ⟨a, ha⟩
      exact ⟨inclusion hHN h, h.property, by rw [hmark, hh]⟩
  have hm (n : N) : α n ∈ j.range := by
    apply normalizer_alternatingSeven_naturalMulAction_le_range
    rw [← him]
    apply Subgroup.le_normalizer_map α
    exact ⟨n, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _, rfl⟩
  let k : N →* j.range := α.codRestrict j.range hm
  let π : N →* Equiv.Perm (Fin 7) := (MonoidHom.ofInjective hj).symm.toMonoidHom.comp k
  have hπ (n : N) : j (π n) = α n := MonoidHom.apply_ofInjective_symm hj (k n)
  refine ⟨π, ?_, ?_⟩
  · intro n w
    have hh := congrArg (fun f : MulAut (Multiplicative (natural (Fin 7))) =>
      (f (c.coordinates w)).toAdd) (hπ n)
    rw [hact] at hh
    exact hh.symm
  · intro h
    apply hj
    exact (hπ (inclusion hHN h)).trans (hmark h)

end Representation.BinaryConjugationSection
