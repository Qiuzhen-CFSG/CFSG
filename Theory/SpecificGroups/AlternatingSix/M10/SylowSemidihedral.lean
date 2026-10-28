module
public import Theory.SpecificGroups.AlternatingSix.M10.SylowRecognition
/-!
# The actual Sylow two-subgroups of M₁₀

The selected subgroup of the cyclic-eight holomorph embeds in the literal
M₁₀ extension. Its two explicit generators satisfy the semidihedral
presentation and its order is sixteen. Sylow conjugacy therefore identifies
every actual Sylow two-subgroup, retaining a quotient-map interface.
Source: Aschbacher--Smith, Lemma 2.5.21, printed p.567.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace AlternatingSix.M10
open ShadowLocal SylowRecognition
private abbrev D := Coordinates.selected
private instance : Fintype D := Subtype.fintype _
private def a : D := ⟨Holomorph.rotation * Holomorph.transposition, by decide +kernel⟩
private def b : D := ⟨Holomorph.reflection, by decide +kernel⟩
private theorem d_card : Nat.card D = 16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private theorem d_presentation :
    orderOf a = 8 ∧ orderOf b = 2 ∧ b * a * b⁻¹ = a ^ 3 ∧ closure ({a,b} : Set D) = ⊤ := by
  refine ⟨?_, ?_, by decide +kernel, ?_⟩
  · apply (orderOf_eq_iff (by decide : 0 < 8)).mpr
    exact ⟨by decide +kernel, by intro n hn hn0; interval_cases n <;> decide +kernel⟩
  · exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  · apply top_unique
    intro x _
    have hw : ∀ x : D, ∃ i : Fin 8, ∃ j : Fin 2, x = a ^ i.val * b ^ j.val := by decide +kernel
    obtain ⟨i, j, rfl⟩ := hw x
    exact (closure ({a,b} : Set D)).mul_mem
      ((Subgroup.closure _).pow_mem (subset_closure (by simp)) _)
      ((Subgroup.closure _).pow_mem (subset_closure (by simp)) _)
private theorem d_equiv : Nonempty (D ≃* Semidihedral.StandardModel 4 (by decide)) :=
  Semidihedral.standardModel_equiv_of_presentation (by decide) a b
    d_presentation.1 d_presentation.2.1 d_presentation.2.2.1 d_presentation.2.2.2 d_card

private theorem embedding_mem_extension (x : D) : Identification.embedding x.val ∈ extension := by
  obtain ⟨i,j,k,hx⟩ := Coordinates.selected_normal_form x.val x.property
  rw [hx]
  simp only [map_mul, map_pow,
    Identification.embedding_rotation, Identification.embedding_reflection,
    Identification.embedding_transposition]
  have hr : Identification.rotation ^ 2 ∈ extension := by
    rw [Identification.rotation_sq]
    exact Action.inner_le_extension ⟨dihedralRotation, (permutationAction_coe _).symm⟩
  have hc : Identification.reflection ∈ extension :=
    Action.inner_le_extension ⟨dihedralReflection, (permutationAction_coe _).symm⟩
  have ht : Identification.rotation * Identification.transposition ∈ extension :=
    (show zpowers (Identification.rotation * Identification.transposition) ≤ extension
      from le_sup_right) (mem_zpowers _)
  exact extension.mul_mem (extension.mul_mem (extension.pow_mem hr _) (extension.pow_mem hc _))
    (extension.pow_mem ht _)

private noncomputable def selectedEmbedding : D →* extension :=
  (Identification.embedding.comp D.subtype).codRestrict extension embedding_mem_extension
private theorem selectedEmbedding_injective : Function.Injective selectedEmbedding := by
  intro x y h
  exact Subtype.ext (Identification.embedding_injective (congrArg Subtype.val h))
private theorem card_selectedEmbedding : Nat.card selectedEmbedding.range = 16 :=
  (Nat.card_congr (MonoidHom.ofInjective selectedEmbedding_injective).symm.toEquiv).trans d_card

/-- Every actual Sylow two-subgroup of M₁₀ is the standard semidihedral sixteen. -/
noncomputable def sylowTwoEquivSemidihedral (P : Sylow 2 extension) :
    P ≃* Semidihedral.StandardModel 4 (by decide) := by
  refine Classical.choice ?_
  let Q : Sylow 2 extension := Sylow.ofCard selectedEmbedding.range (by
    rw [card_selectedEmbedding, Action.card_extension]
    rw [show 720 = 2 ^ 4 * 45 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    rfl)
  obtain ⟨e⟩ := d_equiv
  exact ⟨(P.equiv Q).trans ((MonoidHom.ofInjective selectedEmbedding_injective).symm.trans e)⟩

/-- Restrict an actual epimorphism to a specified Sylow subgroup, preserving
its exact kernel-membership test. -/
theorem exists_sylow_semidihedral_epimorphism {H : Type*} [Group H] [Finite H]
    (f : H →* extension) (hf : Function.Surjective f) (S : Sylow 2 H) :
    ∃ q : S →* Semidihedral.StandardModel 4 (by decide), Function.Surjective q ∧
      ∀ s : S, q s = 1 ↔ f (s : H) = 1 := by
  let P := S.mapSurjective hf
  let r : S →* P := (f.comp (S : Subgroup H).subtype).codRestrict P
    (fun s => mem_map_of_mem f s.property)
  have hr : Function.Surjective r := by
    rintro ⟨p, hp⟩
    obtain ⟨s, hs, he⟩ := hp
    exact ⟨⟨s, hs⟩, Subtype.ext he⟩
  let e := sylowTwoEquivSemidihedral P
  refine ⟨e.toMonoidHom.comp r, e.surjective.comp hr, ?_⟩
  intro s
  change e (r s) = 1 ↔ f (s : H) = 1
  rw [e.map_eq_one_iff]
  exact Subtype.ext_iff

end AlternatingSix.M10
