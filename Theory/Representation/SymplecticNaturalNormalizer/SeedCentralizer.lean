module

public import Theory.Representation.SymplecticNaturalNormalizer.FixedSeedInner
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The literal centralizer of a symplectic fixed seed

For the actual elementary subgroup U and two-subgroup S, an element
centralizing U intersect C(S) fixes the natural field line furnished by
central-cover fixed lifting. Its image therefore lies in the centric normal
symplectic component of the supplied quotient. Both action formulas use
literal ambient conjugation, and the conclusion is the original quotient
preimage. No complement to the fixed central attachment is used.

Source: MS93 (3.4) and Section 7, printed pp.868 and 933.
-/

public section

open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative

namespace SymplecticNaturalNormalizer
variable {F G J : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [Group J]

theorem centralizer_cover_seed_le_component_preimage
    (U S : Subgroup G) [U.Normal] [Finite U] [IsElementaryAbelian 2 U]
    (hS : IsPGroup 2 S)
    (q : G →* J) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:J) w = symplecticNatural 2 (e b) w)
    (π : S →* L (K := F))
    (σ : Representation (ZMod 2) (L (K := F)) (Additive U))
    (hact : ∀ s : S, ∀ u : U,
      ((σ (π s) (Additive.ofMul u)).toMul : G) = (s:G)*u*(s:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hproj : ∀ x : G, ∀ u : U,
      p (Additive.ofMul (MulAut.conjNormal x u)) = ρ (q x) (p (Additive.ofMul u))) :
    centralizer (U ⊓ centralizer (S : Set G) : Set G) ≤ B.comap q := by
  intro x hx
  apply mem_component_of_fixes_cover_seed B hcent hcard e ρ hB p hp π.range
    (hS.of_surjective π.rangeRestrict π.rangeRestrict_surjective) (q x) (fun w => Additive.ofMul (MulAut.conjNormal x w.toMul))
    (fun w => hproj x w.toMul)
  intro w hw
  apply Additive.toMul.injective
  apply Subtype.ext
  change x * (w.toMul:G) * x⁻¹ = (w.toMul:G)
  have hseed : (w.toMul:G) ∈ U ⊓ centralizer (S : Set G) := by
    refine ⟨w.toMul.property,?_⟩
    intro s hs
    have h := hw ⟨π ⟨s,hs⟩,⟨⟨s,hs⟩,rfl⟩⟩
    have he := congrArg (fun z : Additive U => (z.toMul:G)) h
    change ((σ (π ⟨s,hs⟩) w).toMul:G) = (w.toMul:G) at he
    rw [show w = Additive.ofMul w.toMul from rfl,hact] at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  rw [← hx _ hseed,mul_inv_cancel_right]

end SymplecticNaturalNormalizer
