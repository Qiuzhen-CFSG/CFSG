module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Orthogonal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.A6Lift.Coordinates

/-!
# Suitability from the original A₆ covering section

The genuine five-dimensional binary cover supplies the fixed-moving vector
on an arbitrary original central covering section. The actor map retains
the exact image of K intersect A and the exact Sylow image of S. Transport
of movement and fixation through that same map permits the section theorem
to lift the vector to the original W and prove (U0)--(U3) there.

Only the source support marking and separated-support geometry remain
inputs. The universal-cover action, cohomology, quadratic form, scalar
commutant and Sylow-line stabilizer assumptions are all discharged in
the A6Lift extensions. The universal cover belongs to L, the component
image after quotienting, and has a nonzero fixed radical.

Source: Aschbacher--Smith I.2.3, printed p.413, and the choice before
14.6.24, printed p.1038. The parent component-support assembly owns the
source construction of the supports and the later classification clauses.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Representation Representation.OneCohomology
variable {G : Type*} [Group G] [Finite G]
variable {J : Type*} [Group J] [Finite J]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- All suitability clauses on the lifted original element. The natural
quotient is marked in matrix coordinates; the original covering space V,
section map, actor quotient and both subgroup images are retained. -/
theorem source_exists_of_a6_cover
    (K W S A : Subgroup G) (π : A →* J) (L : Subgroup J) [L.Normal]
    (hKimage : (K.subgroupOf A).map π = L) (hSA : S ≤ A)
    (d : Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    (eL : L ≃* A6Lift.Core)
    (η : Representation (ZMod 2) J A6Lift.Natural)
    (hη : ∀ l : L, ∀ v, η l v = A6Lift.natural eL l v)
    (τ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection A W (centralInvolutions T) (τ.comp π))
    (q : τ.IntertwiningMap η) (hq : IsCover q)
    (S₀ : Sylow 2 J) (hS : (S.subgroupOf A).map π = (S₀ : Subgroup J)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  obtain ⟨_, _, ⟨v, _, hmove, hfix⟩, _, _⟩ :=
    A6Lift.fixed_moving_vector L eL η hη τ q hq S₀
  have hmove' : v ∉ fixed ((τ.comp π).comp (K.subgroupOf A).subtype) := by
    intro hv
    apply hmove
    intro l
    obtain ⟨k, hk, hkl⟩ :=
      show (l : J) ∈ (K.subgroupOf A).map π from hKimage.symm ▸ l.property
    have he := hv (⟨k, hk⟩ : K.subgroupOf A)
    change τ (π k) v = v at he
    rwa [hkl] at he
  apply source_exists_of_section_vector hG T hempty hM hunique hmany hcard e hab
    K W S A d (τ.comp π) c hSA v _ hmove'
  intro s hs
  have hs' : π ⟨s, hSA hs⟩ ∈ (S₀ : Subgroup J) :=
    hS ▸ mem_map_of_mem π (show (⟨s, hSA hs⟩ : A) ∈ S.subgroupOf A from hs)
  exact hfix ⟨π ⟨s, hSA hs⟩, hs'⟩

/-- The same application with an arbitrary original natural quotient and
its linear marking. The A₆ identification is the actual six-letter polar
isomorphism, and the covering map in coordinates is exactly E composed
with the given q. In particular neither the original V nor its action changes. -/
theorem source_exists_of_marked_a6_cover
    {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    (K W S A : Subgroup G) (π : A →* J) (L : Subgroup J) [L.Normal]
    (hKimage : (K.subgroupOf A).map π = L) (hSA : S ≤ A)
    (d : Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    (eL : L ≃* alternatingGroup (Fin 6))
    (η : Representation (ZMod 2) J N) (E : N ≃ₗ[ZMod 2] A6Lift.Natural)
    (hE : ∀ l : L, ∀ v, E (η l v) =
      A6Lift.natural (eL.trans A6Lift.alternatingEquiv.symm) l (E v))
    (τ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection A W (centralInvolutions T) (τ.comp π))
    (q : τ.IntertwiningMap η) (hq : IsCover q)
    (S₀ : Sylow 2 J) (hS : (S.subgroupOf A).map π = (S₀ : Subgroup J)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  exact source_exists_of_a6_cover hG T hempty hM hunique hmany hcard e hab
    K W S A π L hKimage hSA d (eL.trans A6Lift.alternatingEquiv.symm)
    (A6Lift.coordinateAction η E)
    (A6Lift.coordinateAction_marked L (eL.trans A6Lift.alternatingEquiv.symm) η E hE)
    τ c (A6Lift.coordinateProjection q E) (A6Lift.coordinateProjection_isCover q hq E) S₀ hS

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
