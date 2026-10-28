module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.NormalClosure
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.Permutations

/-!
# Marking the actual degree-eight action

The coordinate factorization gives group order 56 or 168, so every point
stabilizer has odd order. Consequently every nonidentity involution is fixed
point free. Cauchy's theorem supplies an element of order seven; marking its
cycle constructs an injective permutation homomorphism whose image contains
the fixed seven-cycle used in the finite recognition calculation.

These reductions retain the actual source actor; no simplicity, normal
generation or order-168 hypothesis is introduced. Source: GLS, Volume 4,
Chapter 1, Theorem 3.2 and Lemma 3.9 (`refs/KGroup/GLS4/Chapter1.tex`).
-/

public section
namespace MulAction.SemilinearPointStabilizer.DegreeEight

variable {X F : Type*} [Group X] [Field F] [Finite X] [Finite F]
    [MulAction X F] [FaithfulSMul X F]

/-- The actual KΓ factorization leaves precisely these two orders. -/
theorem card_group_options (c : Coordinates X F)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 8) :
    Nat.card X = 56 ∨ Nat.card X = 168 := by
  let : IsMultiplyPretransitive X F 2 := htwo
  let : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  have hd : Nat.card (twoPoint (X := X) (F := F)) ∣ 3 :=
    c.card_twoPoint_dvd Nat.prime_two (by simpa using hF)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · left
    simpa [hF, h] using c.card_group
  · right
    simpa [hF, h] using c.card_group

/-- No nonidentity involution can fix a field point. -/
theorem involution_has_no_fixed_point (c : Coordinates X F)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 8)
    (t : X) (ht : t ^ 2 = 1) (hne : t ≠ 1) (x : F) : t • x ≠ x := by
  intro hx
  let : IsMultiplyPretransitive X F 2 := htwo
  let : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let u : stabilizer X x := ⟨t, hx⟩
  have hu : orderOf u = 2 := orderOf_eq_prime (Subtype.ext ht)
    (fun h => hne (congrArg Subtype.val h))
  have hd := orderOf_dvd_natCard u
  rw [hu] at hd
  have hc := (stabilizer X x).card_mul_index
  rw [index_stabilizer_of_transitive, hF] at hc
  rcases card_group_options c htwo hF with h | h <;> rw [h] at hc <;> omega

section Label

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- Transport the given action along an actual labeling of its point set. -/
@[expose] noncomputable def labeledHom (e : Ω ≃ Fin 8) : G →* Perm :=
  e.permCongrHom.toMonoidHom.comp (toPermHom G Ω)

@[simp] theorem labeledHom_apply (e : Ω ≃ Fin 8) (g : G) (i : Fin 8) :
    labeledHom e g i = e (g • e.symm i) := rfl

theorem labeledHom_injective [FaithfulSMul G Ω] (e : Ω ≃ Fin 8) :
    Function.Injective (labeledHom (G := G) e) :=
  e.permCongrHom.injective.comp (toPerm_injective (β := Ω))

end Label

/-- Normalize a seven-cycle in a faithful permutation image of the original
actor, retaining the order bound and the fixed-point-free involutions. -/
theorem exists_marked_image (c : Coordinates X F)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 8) :
    ∃ f : X →* Perm, Function.Injective f ∧ cycle ∈ f.range ∧
      Nat.card f.range ∣ 168 ∧ 2 ∣ Nat.card f.range ∧
      (∀ t ∈ f.range, t ^ 2 = 1 → t ≠ 1 → ∀ i : Fin 8, t i ≠ i) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have horder := card_group_options c htwo hF
  have hseven : 7 ∣ Nat.card X := by rcases horder with h | h <;> simp [h]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 7 hseven
  let e : F ≃ Fin 8 := (Finite.equivFin F).trans (finCongr hF)
  have hs' : orderOf (labeledHom e s) = 7 :=
    (orderOf_injective (labeledHom e) (labeledHom_injective e) s).trans hs
  obtain ⟨q, hq⟩ := normalize_seven (labeledHom e s) hs'
  let e' : F ≃ Fin 8 := e.trans q
  let f := labeledHom (G := X) e'
  have hf : Function.Injective f := labeledHom_injective e'
  have hc : f s = cycle := by
    change MulAut.conj q (labeledHom e s) = cycle
    exact hq
  have hcard : Nat.card f.range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  refine ⟨f, hf, ⟨s, hc⟩, ?_, ?_, ?_⟩
  · rw [hcard]
    rcases horder with h | h <;> simp [h]
  · rw [hcard]
    rcases horder with h | h <;> simp [h]
  · intro t ht ht2 htne i hi
    obtain ⟨g, rfl⟩ := ht
    have hg2 : g ^ 2 = 1 := hf (by simpa using ht2)
    have hgne : g ≠ 1 := fun h => htne (by simp [h])
    have hfix : g • e'.symm i = e'.symm i := by
      apply e'.injective
      change e' (g • e'.symm i) = i at hi
      simpa only [Equiv.apply_symm_apply] using hi
    exact involution_has_no_fixed_point c htwo hF g hg2 hgne _ hfix

end MulAction.SemilinearPointStabilizer.DegreeEight
