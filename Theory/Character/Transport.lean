module
public import Theory.Character.ClassFunction
public import Theory.Character.SimpleCriteria

/-!
# Character transport along group maps

Composing a representation with a homomorphism transports its character.
A group equivalence also preserves the normalized scalar product by reindexing
its defining finite sum. These elementary transport identities let concrete
character tables be used on isomorphic groups.
-/

open scoped BigOperators
noncomputable section

public theorem isClassFunction_comp_hom {G H : Type*} [Group G] [Group H]
    (e : H →* G) {f : ClassFunction G} (hf : IsClassFunction f) :
    IsClassFunction (fun h => f (e h)) := by
  intro x g
  simpa only [map_mul, map_inv] using hf (e x) (e g)

public theorem isCharacter_comp_hom {G H : Type*} [Group G] [Group H]
    (e : H →* G) {f : ClassFunction G} (hf : IsCharacter f) :
    IsCharacter (fun h => f (e h)) := by
  obtain ⟨n, ρ, rfl⟩ := hf
  exact ⟨n, ρ.comp e, rfl⟩

public theorem isGeneralizedCharacter_comp_hom {G H : Type*} [Group G] [Group H]
    (e : H →* G) {f : ClassFunction G} (hf : IsGeneralizedCharacter f) :
    IsGeneralizedCharacter (fun h => f (e h)) := by
  obtain ⟨χ, ψ, hχ, hψ, rfl⟩ := hf
  exact ⟨_, _, isCharacter_comp_hom e hχ, isCharacter_comp_hom e hψ, rfl⟩

public theorem scalarProduct_comp_mulEquiv {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : H ≃* G) (f g : ClassFunction G) :
    scalarProduct H (fun h => f (e h)) (fun h => g (e h)) = scalarProduct G f g := by
  unfold scalarProduct
  rw [Nat.card_congr e.toEquiv]
  congr 1
  exact e.toEquiv.sum_comp (fun a => f a * star (g a))

/-- Irreducible characters transport between groups in independent universes. -/
public theorem isIrreducibleCharacter_comp_mulEquiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : H ≃* G) {f : ClassFunction G}
    (hf : IsIrreducibleCharacter f) :
    IsIrreducibleCharacter (fun h => f (e h)) := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite H
  obtain ⟨n, ρ, hρ, rfl⟩ := hf
  refine ⟨n, ρ.comp e.toMonoidHom, ?_, rfl⟩
  apply (irreducible_iff_character_norm_one _).mpr
  change scalarProduct H (fun h => ρ.character (e h))
    (fun h => ρ.character (e h)) = 1
  rw [scalarProduct_comp_mulEquiv]
  exact (irreducible_iff_character_norm_one ρ).mp hρ
