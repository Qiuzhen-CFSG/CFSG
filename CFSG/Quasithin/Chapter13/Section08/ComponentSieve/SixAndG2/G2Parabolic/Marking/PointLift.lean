module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.Line
public import Theory.Representation.G2OrthogonalCover.PointStabilizers

/-!
# Point stabilizers on the original source cover

The whole-star projection carries the original component marking. Group
commutator generation supplies the perfect covering condition, and the
binary Weyl-cover lifting theorem identifies stabilizers on the literal
U_H/V₁ and its natural quotient. In particular the kernel is fixed by the
whole actor, not merely by its component.

Source: Aschbacher–Smith, 13.8.27, printed p.963, with I.2.3.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension Atlas.G2

variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Stabilizers agree through the actual whole-star natural projection,
including when the original central quotient is seven-dimensional. -/
theorem source_point_fixed_iff
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (f : Source.Hstar H →* Model (ZMod 2))
    (p : Additive (Source.Utilde H V₃ V₁) →ₗ[ZMod 2] Natural.Space (ZMod 2))
    (hp : Function.Surjective p)
    (hfK : ∀ a : Source.starImage H K,
      f a = ((Components.componentStarEquiv H K hKH hK).symm.trans eK a : Model (ZMod 2)))
    (he : ∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v))
    (hk : p.ker = fixedSpace ρ (Source.starImage H K))
    (a : Source.Hstar H) (v : Additive (Source.Utilde H V₃ V₁)) :
    ρ a v = v ↔ Natural.action (ZMod 2) (f a) (p v) = p v := by
  let : (Source.starImage H K).Normal := hfit ▸ inferInstance
  have hfull : Coinvariants.ker (ρ.comp (Source.starImage H K).subtype) = ⊤ := by
    rw [← subspaceCommutator_top_eq_coinvariants]
    exact (commutatorImage_eq_subspaceCommutator K hKH ρ hρ).symm.trans
      (commutatorImage_eq_top hgen)
  exact Natural.OrthogonalCover.binary_cover_point_fixed_iff
    (Source.starImage H K) ((Components.componentStarEquiv H K hKH hK).symm.trans eK)
    f hfK ρ p hp (fun _ hv b => (show _ ∈ fixedSpace ρ (Source.starImage H K) from hk ▸ hv) b)
    hfull he a v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
