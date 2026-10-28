module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.Extension
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Canonical
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Involutions of the specified M₁₀ extension

Every involution of the concrete M₁₀ subgroup of Aut(A₆) is inner. To prove
this, place it in the explicit order-32 Sylow model. A kernel-checked
calculation puts every element with square one either in the natural S₆
part or in the coset rD of its inner dihedral subgroup. The latter coset
misses M₁₀, since r times the marked transposition belongs to M₁₀ whereas
the transposition does not. The former intersects M₁₀ in Inn(A₆).

Conjugacy of the involutions of A₆ then supplies an actual permutation
carrying the canonical center (02)(13) to the given automorphism. Both the
Sylow transport and the final conjugacy use the genuine embeddings.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, J.2.7,
printed p.437 (PDF p.448), the Aut(A₆) structure used in its cubic argument.
The explicit Sylow coordinates come from `ShadowLocal.Identification`.
-/

public section

open Subgroup
namespace AlternatingSix.M10.InvolutionAlignment
open ShadowLocal

private theorem square_one_cases (x : Holomorph.Model) (hx : x ^ 2 = 1) :
    x ∈ Holomorph.natural ∨
      ∃ y ∈ Holomorph.innerD, x = Holomorph.rotation * y := by
  have h : ∀ x : Holomorph.Model, x ^ 2 = 1 →
      (∃ i, Holomorph.naturalEmbedding i = x) ∨
        ∃ d, x = Holomorph.rotation * Holomorph.innerEmbedding d := by
    decide +kernel
  rcases h x hx with hn | ⟨d, hd⟩
  · exact Or.inl ((Holomorph.mem_natural x).mpr hn)
  · exact Or.inr ⟨_, (Holomorph.mem_innerD _).mpr ⟨d, rfl⟩, hd⟩

private theorem embedding_inner_mem (x : Holomorph.Model) (hx : x ∈ Holomorph.innerD) :
    Identification.embedding x ∈ ShadowLocal.inner := by
  have h : Holomorph.innerD ≤ ShadowLocal.inner.comap Identification.embedding := by
    apply (closure_le _).mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    change Identification.embedding y ∈ ShadowLocal.inner
    rcases hy with rfl | rfl
    · rw [map_pow, Identification.embedding_rotation, Identification.rotation_sq]
      exact ⟨dihedralRotation, (permutationAction_coe _).symm⟩
    · rw [Identification.embedding_reflection]
      exact ⟨dihedralReflection, (permutationAction_coe _).symm⟩
  exact h hx

private theorem embedding_natural_mem (x : Holomorph.Model) (hx : x ∈ Holomorph.natural) :
    Identification.embedding x ∈ natural := by
  have h : Holomorph.natural ≤ natural.comap Identification.embedding := by
    apply (closure_le _).mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    change Identification.embedding y ∈ natural
    rcases hy with rfl | rfl | rfl
    · rw [map_pow, Identification.embedding_rotation, Identification.rotation_sq]
      exact ⟨_, rfl⟩
    · rw [Identification.embedding_transposition]
      exact ⟨_, rfl⟩
    · rw [Identification.embedding_reflection]
      exact ⟨_, rfl⟩
  exact h hx

private theorem rotation_not_extension : Identification.rotation ∉ extension := by
  intro hr
  have hg : Identification.rotation * Identification.transposition ∈ extension :=
    (le_sup_right : zpowers (Identification.rotation * Identification.transposition) ≤
      extension) (mem_zpowers _)
  have ht : Identification.transposition ∈ extension := by
    simpa only [inv_mul_cancel_left] using extension.mul_mem (extension.inv_mem hr) hg
  exact Action.swap_not_mem_extension Identification.transpositionPerm
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide)) ht

private theorem embedded_involution_inner (x : Holomorph.Model) (hx : x ^ 2 = 1)
    (he : Identification.embedding x ∈ extension) :
    Identification.embedding x ∈ ShadowLocal.inner := by
  rcases square_one_cases x hx with hn | ⟨y, hy, rfl⟩
  · rw [← Action.extension_inf_natural]
    exact ⟨he, embedding_natural_mem x hn⟩
  · have hyi := Action.inner_le_extension (embedding_inner_mem y hy)
    rw [map_mul, Identification.embedding_rotation] at he
    exact (rotation_not_extension (by
      simpa only [mul_inv_cancel_right] using extension.mul_mem he (extension.inv_mem hyi))).elim

/-- Every involution in the specified extension is an inner automorphism. -/
theorem involution_mem_inner (β : AutA6) (hβ : orderOf β = 2) (he : β ∈ extension) :
    β ∈ ShadowLocal.inner := by
  have hp : IsPGroup 2 (zpowers β) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hβ, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨σ, hσ⟩ := Identification.exists_permutation_conjugator P
  have hβP : β ∈ Identification.embedding.range.map
      (MulAut.conj (permutationAction σ)).toMonoidHom := by
    rw [hσ]
    exact hP (mem_zpowers β)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hβP
  change MulAut.conj (permutationAction σ) (Identification.embedding x) = β at hx
  have hx2 : x ^ 2 = 1 := by
    apply Identification.embedding_injective
    apply (MulAut.conj (permutationAction σ)).injective
    simp only [map_pow, map_one]
    rw [show MulAut.conj (permutationAction σ) (Identification.embedding x) = β from hx]
    exact hβ ▸ pow_orderOf_eq_one β
  have hxe : Identification.embedding x ∈ extension := by
    have hi := (inferInstance : extension.Normal).conj_mem β he (permutationAction σ)⁻¹
    have hiEq : (permutationAction σ)⁻¹ * β * ((permutationAction σ)⁻¹)⁻¹ =
        Identification.embedding x := by
      rw [← hx]
      simp only [MulAut.conj_apply, inv_inv]
      group
    exact hiEq ▸ hi
  rw [← hx]
  exact (inferInstance : ShadowLocal.inner.Normal).conj_mem _
    (embedded_involution_inner x hx2 hxe) _

/-- Retain a six-letter permutation conjugating the canonical center to the involution. -/
theorem exists_permutation_alignment (β : AutA6) (hβ : orderOf β = 2)
    (he : β ∈ extension) :
    ∃ σ : Equiv.Perm (Fin 6), β = (MulAut.conj (permutationAction σ))
      (permutationAction (LocalGeometry.standardU * LocalGeometry.standardZ)) := by
  obtain ⟨a, rfl⟩ := involution_mem_inner β hβ he
  have ha : orderOf a = 2 := by
    rwa [orderOf_injective _ inner_injective] at hβ
  have hc : orderOf (dihedralRotation ^ 2) = 2 := by
    apply orderOf_eq_prime <;> decide +kernel
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj (dihedralRotation ^ 2) a hc ha)
  have hcenter : MulAut.conj (dihedralRotation ^ 2) =
      permutationAction (LocalGeometry.standardU * LocalGeometry.standardZ) := by
    rw [← permutationAction_coe]
    congr 1
    decide +kernel
  refine ⟨(g : Equiv.Perm (Fin 6)), ?_⟩
  rw [← hcenter, permutationAction_coe]
  change MulAut.conj a = MulAut.conj g * MulAut.conj (dihedralRotation ^ 2) * (MulAut.conj g)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, hg]

end AlternatingSix.M10.InvolutionAlignment
