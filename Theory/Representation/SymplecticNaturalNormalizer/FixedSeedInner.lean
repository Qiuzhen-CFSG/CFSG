module

public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting

/-!
# Centralizing a fixed cover seed removes the field automorphism

Every two-subgroup of the natural symplectic group fixes a nonzero field
vector. Fixed-point lifting in the binary central cover supplies lifts of
every vector on that field line, including the full central attachment.
An ambient operator centralizing the cover seed therefore fixes the entire
natural field line. For a centric normal symplectic component its conjugation
is inner, and the operator belongs to that actual component.

Source: the final containment in MS93 Section 7, p.933, using the seed
C_U(Sstar) of (3.4), p.868. Only the two-group property of Sstar is needed
for this step; its full Sylow geometry belongs to the graph comparison.
-/

public section

open Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

namespace SymplecticNaturalNormalizer
variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]

theorem cover_seed_projects_field_line
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (S : Subgroup (L (K := F))) (hS : IsPGroup 2 S) :
    ∃ v : Vector F, v ≠ 0 ∧ ∀ c : F, ∃ w : W,
      w ∈ fixed (σ.comp S.subtype) ∧ p w = c • v := by
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector
    (F := F) (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using hS)
    ((symplecticDerivedNatural (k := F) 2).comp S.subtype)
  refine ⟨v,hv,fun c => ?_⟩
  obtain ⟨w,hw⟩ := hp.1 (c • v)
  refine ⟨w,?_,hw⟩
  rw [cover_fixed_preimage p hp]
  intro s
  change binaryNatural s.val (p w) = p w
  rw [hw]
  change symplecticDerivedNatural 2 s.val (c • v) = c • v
  rw [map_smul]
  exact congrArg (c • ·) (hfix s)

theorem mem_component_of_fixes_cover_seed
    (B : Subgroup G) [B.Normal]
    (hcent : Subgroup.centralizer (B : Set G) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (S : Subgroup (L (K := F))) (hS : IsPGroup 2 S)
    (x : G) (f : W → W) (hcompat : ∀ w, p (f w) = ρ x (p w))
    (hfix : ∀ w ∈ fixed (σ.comp S.subtype), f w = w) : x ∈ B := by
  obtain ⟨v,hv,hvline⟩ := cover_seed_projects_field_line p hp S hS
  apply mem_component_of_fixes_field_line B hcent hcard e ρ hB x v hv
  intro c
  obtain ⟨w,hw,hpw⟩ := hvline c
  rw [← hpw,← hcompat,hfix w hw]

end SymplecticNaturalNormalizer
