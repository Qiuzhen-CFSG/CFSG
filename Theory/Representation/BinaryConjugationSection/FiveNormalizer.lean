module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.BinaryAlternatingFiveNormalizer
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Extending an original deleted A₅ section to five-point permutations

Bijective coordinates on W transport the action of every common normalizer
of W and its marked A₅ actor. The actual A₅ image is normal in this action,
so the binary A₅ normalizer theorem gives a permutation of the same five
coordinates. The extension keeps both the original coordinate map and the
original actor quotient; no ambient quotient or abstract module is substituted.

Source: Aschbacher–Smith, 10.1.1(2) and the deleted row of 10.2.9(1), pp.741,750.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Representation.BinaryConjugationSection
noncomputable section
variable {G : Type*} [Group G]

theorem exists_five_normalizer_action
    (H W N : Subgroup G) (hHN : H ≤ N) (hNW : N ≤ normalizer (W : Set G))
    (hNH : N ≤ normalizer (H : Set G))
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection H W ⊥
      ((alternatingNaturalRepresentation (Fin 5)).comp q)) :
    ∃ π : N →* Equiv.Perm (Fin 5),
      (∀ (n : N) (w : W),
        (c.coordinates ⟨(n : G) * w * (n : G)⁻¹,
          (mem_normalizer_iff.mp (hNW n.property) w).mp w.property⟩).toAdd =
          naturalRepresentation (Fin 5) (π n) (c.coordinates w).toAdd) ∧
      (∀ h : H, π (inclusion hHN h) = (q h).val) := by
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq, bot_subgroupOf]
  let E := MulEquiv.ofBijective c.coordinates ⟨hci, c.onto⟩
  let α : N →* MulAut (Multiplicative (natural (Fin 5))) :=
    (MulAut.congr E).toMonoidHom.comp (W.normalizerMonoidHom.comp (inclusion hNW))
  have hact (n : N) (w : W) : α n (c.coordinates w) =
      c.coordinates ⟨(n : G) * w * (n : G)⁻¹,
        (mem_normalizer_iff.mp (hNW n.property) w).mp w.property⟩ := by
    change E (W.normalizerMonoidHom (inclusion hNW n) (E.symm (E w))) = _
    rw [E.symm_apply_apply]
    rfl
  let j := naturalMulAction (Fin 5)
  have hj : Function.Injective j := naturalMulAction_injective_of_odd (Fin 5) (by decide)
  have hmark (h : H) : α (inclusion hHN h) = j (q h).val := by
    apply MulEquiv.ext
    intro v
    obtain ⟨w, rfl⟩ := c.onto v
    apply Multiplicative.toAdd.injective
    rw [hact]
    exact c.equivariant h w
  let K := H.subgroupOf N
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hHN).mpr hNH
  have him : K.map α = (alternatingGroup (Fin 5)).map j := by
    ext a
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨q ⟨h, hh⟩, (q ⟨h, hh⟩).property, (hmark ⟨h, hh⟩).symm⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨h, hh⟩ := hq ⟨a, ha⟩
      exact ⟨inclusion hHN h, h.property, by rw [hmark, hh]⟩
  have hm (n : N) : α n ∈ j.range := by
    apply normalizer_alternatingFive_naturalMulAction_le_range
    rw [← him]
    apply Subgroup.le_normalizer_map α
    exact ⟨n, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _, rfl⟩
  let k : N →* j.range := α.codRestrict j.range hm
  let π : N →* Equiv.Perm (Fin 5) := (MonoidHom.ofInjective hj).symm.toMonoidHom.comp k
  have hπ (n : N) : j (π n) = α n := MonoidHom.apply_ofInjective_symm hj (k n)
  refine ⟨π, ?_, ?_⟩
  · intro n w
    have hh := congrArg (fun f : MulAut (Multiplicative (natural (Fin 5))) =>
      (f (c.coordinates w)).toAdd) (hπ n)
    rw [hact] at hh
    exact hh.symm
  · intro h
    apply hj
    exact (hπ (inclusion hHN h)).trans (hmark h)

end
end Representation.BinaryConjugationSection
