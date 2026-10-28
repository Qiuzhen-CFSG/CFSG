module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Labels
public import Mathlib.Data.Fintype.Perm

/-!
# Recognition of a full semilinear image from an escaping residual

A proper subgroup of the determinant-label symmetric group S₃ is abelian.
Consequently a subgroup J satisfying J = [J,S] and escaping the special
linear kernel forces a full label image. An ambient image containing the
special linear group is then all of ΓL₂(4).

The last theorem applies this criterion to an actual faithful marked
homomorphism. No cardinality or ambient surjectivity is assumed: these are
the image-recognition inputs in the noncontained branch of Aschbacher--Smith
13.7.19. The tiny checked certificate concerns only permutations of three
points; all transport and commutator arguments are structural.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Representation.SL2FourNatural.SemilinearNormalizer

private theorem three_noncommuting_generation :
    ∀ a b g : Equiv.Perm (Fin 3), a * b ≠ b * a →
      g = 1 ∨ g = a ∨ g = b ∨ g = a * b ∨ g = b * a ∨
        g = a * b * a ∨ g = a ^ 2 ∨ g = b ^ 2 := by
  decide +kernel

private theorem label_noncommuting_generation (a b g : Equiv.Perm Fˣ)
    (h : a * b ≠ b * a) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b ∨ g = b * a ∨
      g = a * b * a ∨ g = a ^ 2 ∨ g = b ^ 2 := by
  let e := Equiv.permCongrHom (Fintype.equivFinOfCardEq card_labels)
  have hn : e a * e b ≠ e b * e a := by
    intro hh
    apply h
    exact e.injective (by simpa only [map_mul] using hh)
  have hs := three_noncommuting_generation (e a) (e b) (e g) hn
  have hs' : e g = e 1 ∨ e g = e a ∨ e g = e b ∨ e g = e (a * b) ∨
      e g = e (b * a) ∨ e g = e (a * b * a) ∨ e g = e (a ^ 2) ∨ e g = e (b ^ 2) := by
    simpa only [map_one, map_mul, map_pow] using hs
  simpa only [e.injective.eq_iff] using hs'

private theorem proper_labels_commute (D : Subgroup (Equiv.Perm Fˣ))
    (hD : D ≠ ⊤) (a b : Equiv.Perm Fˣ) (ha : a ∈ D) (hb : b ∈ D) :
    a * b = b * a := by
  by_contra h
  apply hD
  apply top_unique
  intro g hg
  rcases label_noncommuting_generation a b g h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact D.one_mem
  · exact ha
  · exact hb
  · exact D.mul_mem ha hb
  · exact D.mul_mem hb ha
  · exact D.mul_mem (D.mul_mem ha hb) ha
  · exact D.pow_mem ha 2
  · exact D.pow_mem hb 2

/-- The label image is full once a commutator-generated subgroup escapes SL₂(4). -/
theorem labels_eq_top_of_commutator_noncontained (X J S : Subgroup Gamma)
    (hJX : J ≤ X) (hSX : S ≤ X) (hJS : J = ⁅J, S⁆)
    (hne : ¬ J ≤ special.range) : X.map labels = ⊤ := by
  by_contra hh
  have hc : ⁅J.map labels, S.map labels⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    apply mem_centralizer_iff.mpr
    intro b hb
    exact proper_labels_commute (X.map labels) hh b a (map_mono hSX hb) (map_mono hJX ha)
  have hJ : J.map labels = ⊥ := by
    conv_lhs => rw [hJS]
    rw [map_commutator]
    exact hc
  apply hne
  rw [← labels_ker]
  exact (Subgroup.map_eq_bot_iff _).mp hJ

/-- An overgroup of SL₂(4) is full if it contains an escaping commutator-generated subgroup. -/
theorem eq_top_of_commutator_noncontained (X J S : Subgroup Gamma)
    (hKX : special.range ≤ X) (hJX : J ≤ X) (hSX : S ≤ X)
    (hJS : J = ⁅J, S⁆) (hne : ¬ J ≤ special.range) : X = ⊤ := by
  have hlabels := labels_eq_top_of_commutator_noncontained X J S hJX hSX hJS hne
  have hk : labels.ker ≤ X := labels_ker ▸ hKX
  have he : (X.map labels).comap labels = X := Subgroup.comap_map_eq_self hk
  rw [hlabels, Subgroup.comap_top] at he
  exact he.symm

/-- An actual marked injection is onto once a noncontained commutator-generated subgroup survives. -/
theorem surjective_of_marked_commutator
    {H : Type*} [Group H] (f : H →* Gamma) (hf : Function.Injective f)
    (K J S : Subgroup H) (hK : K.map f = special.range)
    (hJS : J = ⁅J, S⁆) (hne : ¬ J ≤ K) : Function.Surjective f := by
  have hn : ¬ J.map f ≤ special.range := by
    rw [← hK, Subgroup.map_le_map_iff_of_injective hf]
    exact hne
  have he := eq_top_of_commutator_noncontained f.range (J.map f) (S.map f)
    (hK ▸ Subgroup.map_le_range f K) (Subgroup.map_le_range f J)
    (Subgroup.map_le_range f S)
    (by
      conv_lhs => rw [hJS]
      rw [map_commutator]) hn
  exact MonoidHom.range_eq_top.mp he

end Representation.SL2FourNatural.SemilinearNormalizer
