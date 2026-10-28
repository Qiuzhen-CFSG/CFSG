module

public import Theory.SpecificGroups.AlternatingSix.M10.Contracts

/-!
# The specified index-two extension of A₆

The marked product of the eighth-root automorphism and the natural
transposition has square in Inn(A₆), and lies outside the natural S₆.
Its image in the outer quotient therefore has order two. This proves
that the literal subgroup in `M10.Contracts` is normal of order 720,
with intersection Inn(A₆) with the natural S₆. In particular it contains
every nine-group and excludes every actual transposition.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), after 4.8, p.41. The generator relations are the
concrete pentad calculations in `ShadowLocal.Identification.Generators`.
-/

public section

open Subgroup
namespace AlternatingSix.M10.Action
open ShadowLocal Identification

private abbrev q := QuotientGroup.mk' ShadowLocal.inner
private noncomputable abbrev g : AutA6 := rotation * transposition

theorem extensionGenerator_sq : (rotation * transposition) ^ 2 = rotation ^ 6 := by
  calc
    g ^ 2 = rotation * (transposition * rotation * transposition⁻¹) * transposition ^ 2 := by
      dsimp [g]
      simp only [pow_two]
      group
    _ = rotation ^ 6 := by
      rw [transposition_rotation, transposition_sq, mul_one, ← pow_succ']

private theorem square_mem : g ^ 2 ∈ ShadowLocal.inner := by
  rw [extensionGenerator_sq]
  have h : rotation ^ 2 ∈ ShadowLocal.inner := by
    rw [rotation_sq]
    exact ⟨dihedralRotation, (permutationAction_coe _).symm⟩
  simpa only [← pow_mul] using ShadowLocal.inner.pow_mem h 3

private theorem outside : g ∉ natural := by
  intro hg
  have ht : transposition ∈ natural := ⟨transpositionPerm, rfl⟩
  apply rotation_not_mem_natural
  simpa only [g, mul_assoc, mul_inv_cancel, mul_one] using natural.mul_mem hg (natural.inv_mem ht)

private theorem image_order : orderOf (q g) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr square_mem
  · intro he
    exact outside (inner_le_natural ((QuotientGroup.eq_one_iff _).mp he))

private theorem image_eq : extension.map q = zpowers (q g) := by
  rw [extension, Subgroup.map_sup, MonoidHom.map_zpowers]
  have h : ShadowLocal.inner.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr hx
  rw [h, bot_sup_eq]

theorem extension_index : extension.index = 2 := by
  have he := (extension.map q).card_mul_index
  rw [image_eq, Nat.card_zpowers, image_order] at he
  have hc : Nat.card (AutA6 ⧸ ShadowLocal.inner) = 4 := ShadowLocal.inner_index
  rw [hc] at he
  have hi : (extension.map q).index = extension.index := by
    apply Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective ShadowLocal.inner)
    rw [QuotientGroup.ker_mk', extension]
    exact le_sup_left
  rw [image_eq] at hi
  rw [hi] at he
  omega

theorem permutationAction_mem_inner_iff (p : Equiv.Perm (Fin 6)) :
    permutationAction p ∈ ShadowLocal.inner ↔ p ∈ alternatingGroup (Fin 6) := by
  constructor
  · rintro ⟨a, ha⟩
    have he : (a : Equiv.Perm (Fin 6)) = p := permutationAction_injective
      ((permutationAction_coe a).trans ha)
    exact he ▸ a.property
  · intro hp
    exact ⟨⟨p, hp⟩, (permutationAction_coe _).symm⟩

private theorem nine_even (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    D ≤ alternatingGroup (Fin 6) := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  have h : x ^ 9 = 1 := by
    have he := pow_card_eq_one' (x := (⟨x, hx⟩ : D))
    rw [hD] at he
    exact congrArg Subtype.val he
  have hs := congrArg Equiv.Perm.sign h
  simp only [map_pow, map_one] at hs
  have he := Int.units_eq_one_or (Equiv.Perm.sign x)
  rcases he with he | he
  · exact he
  · rw [he] at hs
    norm_num at hs

/-- The specified subgroup is normal in the whole genuine automorphism group. -/
instance extension_normal : extension.Normal := normal_of_index_eq_two extension_index

theorem card_extension : Nat.card extension = 720 := by
  have h := extension.card_mul_index
  rw [extension_index, card_aut] at h
  omega

theorem inner_le_extension : ShadowLocal.inner ≤ extension := le_sup_left

/-- The two index-two subgroups meet in precisely the inner automorphisms. -/
theorem extension_inf_natural : extension ⊓ natural = ShadowLocal.inner := by
  classical
  apply le_antisymm ?_ (le_inf inner_le_extension inner_le_natural)
  intro x hx
  have hm : q x ∈ zpowers (q g) := image_eq ▸ mem_map_of_mem q hx.1
  rw [mem_zpowers_iff_mem_range_orderOf, image_order] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hn2 := Finset.mem_range.mp hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · apply (QuotientGroup.eq_one_iff x).mp
    simpa only [pow_zero, q, QuotientGroup.mk'_apply] using he.symm
  · have he' : (x : AutA6 ⧸ ShadowLocal.inner) = g := by
      simpa only [pow_one, q, QuotientGroup.mk'_apply] using he.symm
    have hk : x⁻¹ * g ∈ ShadowLocal.inner := QuotientGroup.eq.mp he'
    have hg : g ∈ natural := by
      simpa only [mul_inv_cancel_left] using (natural.mul_mem hx.2 (inner_le_natural hk))
    exact (outside hg).elim

theorem permutationAction_mem_extension_iff (p : Equiv.Perm (Fin 6)) :
    permutationAction p ∈ extension ↔ p ∈ alternatingGroup (Fin 6) := by
  rw [← permutationAction_mem_inner_iff]
  constructor
  · intro hp
    rw [← extension_inf_natural]
    exact ⟨hp, ⟨p, rfl⟩⟩
  · intro hp
    exact inner_le_extension hp

theorem swap_not_mem_extension (p : Equiv.Perm (Fin 6)) (hp : p.IsSwap) :
    permutationAction p ∉ extension := by
  rw [permutationAction_mem_extension_iff, Equiv.Perm.mem_alternatingGroup, hp.sign_eq]
  decide

theorem nine_le_inner (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    nine D ≤ ShadowLocal.inner := by
  rintro _ ⟨x, hx, rfl⟩
  exact (permutationAction_mem_inner_iff x).mpr (nine_even D hD hx)

theorem nine_le_extension (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    nine D ≤ extension := (nine_le_inner D hD).trans inner_le_extension

theorem card_nine (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    Nat.card (nine D) = 9 := by
  rw [nine, card_map_of_injective permutationAction_injective, hD]

end AlternatingSix.M10.Action
