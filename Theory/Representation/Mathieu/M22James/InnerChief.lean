module
public import Theory.Representation.InnerCubicInvolution
public import Theory.Mathieu.M22.TripleCover.ConjugateGeneration
public import Theory.Representation.BinaryOffender.CubicCenterChief
public import Theory.Representation.Mathieu.M22James.Classification
public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.BinaryOffender.ConjugateMovedDimension

/-!
# The faithful Mathieu chief section detected by a small inner involution

The cubic center is detected on a genuine chief factor of the given binary
action. Its component restriction is faithful. Inner-involution restriction
makes it irreducible on the component; three conjugates bound its degree by
twelve, while James's lower bound forces equality. The same actor exhausts
four dimensions on this section, and the degree-twelve uniqueness theorem
supplies an actual intertwiner with the constructed James module.

Three conjugates of the original actor also bound the entire moved space by
twelve, allowing fixed vectors and nonsplit extensions in the given module.
Identification of the component commutator with the chief section and the
point-stabilizer argument remain separate steps.
Source: Aschbacher–Smith, H.12.1 and proof of 12.6.26, pp.393–394,832.
-/

public section
namespace Sporadic.Mathieu.M22TripleCover
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- The original action has a faithful degree-twelve component chief section,
with the same small involution and an explicit module isomorphism. -/
theorem inner_chief_twelve
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (B : Subgroup G) [B.Normal] [IsQuasisimple B]
    (hc : Nat.card (center B) = 3) (e : (B ⧸ center B) ≃* M22)
    (t : G) (ht : t ^ 2 = 1) (hgen : B ⊔ zpowers t = ⊤)
    (hi : ∃ b : B, MulAut.conjNormal (H := B) t = MulAut.conj b)
    (hn : MulAut.conjNormal (H := B) t ≠ 1)
    (hr : fixedCodim ρ (zpowers t) ≤ 4) :
    ∃ U N : Subrepresentation ρ,
      let τ := sectionRepresentation ρ U N
      τ.IsIrreducible ∧ IsIrreducible (τ.comp B.subtype) ∧
      Function.Injective (τ.comp B.subtype) ∧
      Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) = 12 ∧
      fixedCodim τ (zpowers t) = 4 ∧
      ∃ ec : B ≃* M22TripleCover,
        Nonempty (Representation.Equiv (τ.comp B.subtype) (representationOfEquiv ec)) := by
  obtain ⟨U,N,hτ,hfaith⟩ := exists_faithful_chief_of_cubic_center ρ B hf hc
  let τ := sectionRepresentation ρ U N
  let := hτ
  obtain ⟨hirr,b,hb2,hb,hbt⟩ := Representation.InnerCubicInvolution.restriction_irreducible_and_involution τ B hc t ht hgen hi
  let := hirr
  let σ := τ.comp B.subtype
  have hb1 : b ≠ 1 := by
    intro hh
    apply hn
    rw [hb,hh,map_one]
  have hbo : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  obtain ⟨g,hg⟩ := three_conjugates_generate e hc b hbo
  have hfix : fixedSpace σ ⊤ = ⊥ := by
    by_contra h
    have hk := le_ker_of_normal_invariants_ne_bot σ ⊤ h
    exact hb1 (hfaith ((hk (mem_top b)).trans (map_one σ).symm))
  have hupp := finrank_le_mul_fixedCodim_of_conjugate_generation σ ⊤ hfix b g hg.ge
  have hcodim : fixedCodim σ (zpowers b) = fixedCodim τ (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_eq_displacement_rank]
    change Module.finrank (ZMod 2) (τ b - LinearMap.id).range = _
    rw [hbt]
  have hdimle : Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) ≤
      3 * fixedCodim (sectionRepresentation ρ U N) (zpowers t) :=
    hupp.trans_eq (congrArg (fun n : ℕ => 3*n) hcodim)
  have hrτ := (fixedCodim_section_le ρ U N (zpowers t)).trans hr
  obtain ⟨ec⟩ := nonempty_mulEquiv hc ⟨e⟩
  have hlow := faithful_irreducible_finrank_ge_twelve_of_equiv ec σ hfaith
  have hdimlow : 12 ≤ Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) := hlow
  have hd : Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) = 12 := by omega
  refine ⟨U,N,hτ,hirr,hfaith,hd,by omega,ec,?_⟩
  exact equiv_representationOfEquiv_of_finrank_twelve ec σ hfaith hd
end Sporadic.Mathieu.M22TripleCover

namespace Sporadic.Mathieu.M22TripleCover
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The whole moved space has degree at most twelve, before passing to a
chief quotient or assuming any splitting of the given representation. -/
theorem inner_moved_finrank_le_twelve
    (ρ : Representation (ZMod 2) G W)
    (B : Subgroup G) [B.Normal] [IsQuasisimple B]
    (hc : Nat.card (center B) = 3) (e : (B ⧸ center B) ≃* M22)
    (t : G) (ht : t ^ 2 = 1) (hgen : B ⊔ zpowers t = ⊤)
    (hi : ∃ b : B, MulAut.conjNormal (H := B) t = MulAut.conj b)
    (hn : MulAut.conjNormal (H := B) t ≠ 1)
    (hr : fixedCodim ρ (zpowers t) ≤ 4) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤ 12 := by
  obtain ⟨g,hg⟩ := three_inner_conjugates_generate B e hc t ht hgen hi hn
  have hd := finrank_coinvariants_le_mul_displacement_of_conjugate_generation ρ t g hg
  rw [←fixedCodim_zpowers_eq_displacement_rank] at hd
  omega
end Sporadic.Mathieu.M22TripleCover
