module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.BlockCollection
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.Torus
public import Theory.GroupTheory.CentralExtensionOddSection
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Torus normalization of the actual positive Ree block lifts

Every fixed coroot element normalizes every actual block Xᵢ, by the
split-coordinate calculation in Torus. The coroot torus has odd order.
In a central extension with exponent-two kernel, average a kernel retraction
over this torus. This replaces any family of homomorphic block sections by
one equivariant under every lift of every fixed torus element. The four
nonabelian B₂ groups are retained without changing their multiplication.

The final reduction below separates the four additive and four B₂ splitting
calculations. Their sections are still explicit premises. No splitting of a
Ree cover, including the q = 8 case, is asserted without those inputs.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408; GLS3 §6.1 and
§§2.3–2.4, especially Table 2.4 and the type V multiplication law.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary
open Subgroup ElementaryTwoBound PerfectCentralCovering

/-- The literal fixed coroot torus has odd order, with its diagonal realization
and both subgroup embeddings discharged. -/
theorem fixedTorus_card_odd (m : ℕ) : Odd (Nat.card (Parabolics.fixedTorus m)) := by
  apply Parabolics.fixedTorus_odd_card
  rw [Parabolics.splitTorus_eq_diagonalTorus]
  exact Parabolics.diagonalTorus_odd_card m

/-- Normalize arbitrary block sections simultaneously under all torus actors.
Only the kernel exponent, rather than its exact order, is required here. -/
theorem exists_torusEquivariant_of_block_sections (m : ℕ)
    {E : Type*} [Group E] (f : E →* Model m)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hsq : ∀ k : f.ker, k ^ 2 = 1) (L : BlockSections m f) :
    ∃ M : BlockSections m f, M.TorusEquivariant := by
  have hex (i : BlockIndex) :=
    CentralExtension.exists_odd_normalizer_equivariant_section f hf hk hsq
      (Parabolics.fixedTorus m) (X m (rootIndex i)) (fixedTorus_card_odd m)
      (fixedTorus_normalizes_X m (rootIndex i)) (L.lift i)
      (MonoidHom.ext (L.project i))
  choose s hs he using hex
  exact ⟨⟨s, fun i x => DFunLike.congr_fun (hs i) x⟩, he⟩

/-- Degree-two covers meet the exponent hypothesis of the normalization step. -/
theorem exists_torusEquivariant_of_degree_two_sections (m : ℕ)
    {E : Type*} [Group E] (d : Cover E (Model m))
    (hd : Nat.card d.toMonoidHom.ker = 2) (L : BlockSections m d.toMonoidHom) :
    ∃ M : BlockSections m d.toMonoidHom, M.TorusEquivariant := by
  apply exists_torusEquivariant_of_block_sections m d.toMonoidHom
    d.surjective d.ker_le_center _ L
  intro k
  rw [← hd]
  exact pow_card_eq_one'

/-- Actual consumer of the two independent local splitting families.
The projection triangles use the literal root subgroups and their inclusions;
no equivariance or inter-block relation is required of either input. -/
theorem exists_torusEquivariant_of_pair_and_quartet_sections (m : ℕ)
    {E : Type*} [Group E] (d : Cover E (Model m))
    (hd : Nat.card d.toMonoidHom.ker = 2)
    (hp : ∀ j : Fin 4, ∃ s : X m (rootIndex (.inl j)) →* E,
      d.toMonoidHom.comp s = (X m (rootIndex (.inl j))).subtype)
    (hq : ∀ j : Fin 4, ∃ s : X m (rootIndex (.inr j)) →* E,
      d.toMonoidHom.comp s = (X m (rootIndex (.inr j))).subtype) :
    ∃ L : BlockSections m d.toMonoidHom, L.TorusEquivariant := by
  have hex (i : BlockIndex) : ∃ s : X m (rootIndex i) →* E,
      d.toMonoidHom.comp s = (X m (rootIndex i)).subtype := by
    cases i with
    | inl j => exact hp j
    | inr j => exact hq j
  choose s hs using hex
  exact exists_torusEquivariant_of_degree_two_sections m d hd
    ⟨s, fun i x => DFunLike.congr_fun (hs i) x⟩

end ReeF4.CentralCovers.TwoPrimary
