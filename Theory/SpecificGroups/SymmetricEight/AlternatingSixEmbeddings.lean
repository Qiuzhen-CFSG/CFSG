module

public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.Orbits
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.PairGeometry

/-!
# A₆ embeddings in the actual alternating group on eight letters

An A₆ action on eight letters fixes a pair. Faithfulness makes its image
have order 360, so it is the whole even pointwise pair stabilizer. Pair
transport therefore conjugates any two images, with the induced actor
automorphism constructed from their injective maps. Their normalizers have
order at most 720.

These results provide the finite permutation-group input to the binary
four-space recognition and natural normalizer in Aschbacher–Smith,
K.1–K.1.1, printed p.452. The consumer transports through the actual
PSL₄(2) ≃ A₈ comparison and constructs the linear intertwiner.
-/

public section

open Subgroup MulAction
namespace Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings

theorem range_eq_pairFixer (f : A6 →* A8) (hf : Function.Injective f) :
    ∃ a b : Fin 8, a ≠ b ∧ f.range = pairFixer a b := by
  obtain ⟨a, b, hab, hfix⟩ := exists_fixed_pair (A8.subtype.comp f)
  refine ⟨a, b, hab, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact hfix g
  · rw [pairFixer_card a b hab, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, card_A6]

theorem ranges_conjugate (f g : A6 →* A8)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ p : A8, f.range.map (MulAut.conj p).toMonoidHom = g.range := by
  obtain ⟨a, b, hab, hf⟩ := range_eq_pairFixer f hf
  obtain ⟨c, d, hcd, hg⟩ := range_eq_pairFixer g hg
  rw [hf, hg]
  exact pairFixer_conjugate a b c d hab hcd

theorem normalizer_card_le (f : A6 →* A8) (hf : Function.Injective f) :
    Nat.card (normalizer (f.range : Set A8)) ≤ 720 := by
  obtain ⟨a, b, hab, he⟩ := range_eq_pairFixer f hf
  rw [he]
  exact pairFixer_normalizer_card_le a b hab

theorem exists_conjugating_equiv (f g : A6 →* A8)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ p : A8, ∃ a : A6 ≃* A6, ∀ x : A6, p * f x * p⁻¹ = g (a x) := by
  obtain ⟨p, hp⟩ := ranges_conjugate f g hf hg
  let f' := (MulAut.conj p).toMonoidHom.comp f
  have hf' : Function.Injective f' := (MulAut.conj p).injective.comp hf
  have hr : f'.range = g.range := by
    rw [MonoidHom.range_comp]
    exact hp
  let a : A6 ≃* A6 := (MonoidHom.ofInjective hf').trans
    ((MulEquiv.subgroupCongr hr).trans (MonoidHom.ofInjective hg).symm)
  refine ⟨p, a, fun x => ?_⟩
  exact (MonoidHom.apply_ofInjective_symm hg
    ((MulEquiv.subgroupCongr hr) ((MonoidHom.ofInjective hf') x))).symm
end Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
