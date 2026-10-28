module

public import CFSG.Quasithin.ChapterD.Section03.SourceInternal
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.TwoQuotient

/-!
# The generalized Fitting subgroup of the local orbit image

Either source actor is contained in the generalized Fitting subgroup:
the component orbit generates a semisimple group, while a normal
odd-prime actor is nilpotent. A two-group supplement and trivial
two-core therefore make the actor precisely F* of the local group.

Apply this to the faithful orbit action from D.3.3. The resulting F*
is exactly the actual restricted actor, with its semisimple or odd-prime
shape proved from the original alternatives. This is the first assertion
of D.3.4(5); the separate seed-stabilizer action is not used here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.194.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterD.Section03
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem ActorCases.le_generalizedFitting
    {T : Sylow 2 G} {X : Subgroup G} [X.Normal]
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : ActorCases T X hTX) : X ≤ generalizedFitting G := by
  rcases hc with ⟨L, hL, rfl⟩ | ⟨p, hp, _, hP, _⟩
  · apply iSup_le
    intro t
    exact component_le_generalizedFitting G _ (hL.map_conj (t : G))
  · let : Fact p.Prime := ⟨hp⟩
    exact (show X ≤ fittingSubgroup G from
      le_sSup ⟨inferInstance, hP.isNilpotent⟩).trans (fitting_le_generalizedFitting G)

omit [Finite G] in
theorem ActorCases.layer_or_prime_group
    {T : Sylow 2 G} {X : Subgroup G}
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : ActorCases T X hTX) :
    componentLayer X = ⊤ ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p X := by
  rcases hc with ⟨L, hL, hX⟩ | ⟨p, hp, ho, hP, _⟩
  · left
    apply top_unique
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [← MonoidHom.range_eq_map, range_subtype]
    rw [hX]
    apply iSup_le
    intro t
    have hLX : L.map (MulAut.conj (t : G)).toMonoidHom ≤ X := by
      rw [hX]
      exact le_iSup (fun s : T => L.map (MulAut.conj (s : G)).toMonoidHom) t
    have hcomp := (hL.map_conj (t : G)).subgroupOf hLX
    have hm := map_mono (f := X.subtype)
      (show (L.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf X ≤ componentLayer X from
        le_sSup hcomp)
    rwa [map_subgroupOf_eq_of_le hLX, hX] at hm
  · exact Or.inr ⟨p, hp, ho, hP⟩

theorem ActorCases.generalizedFitting_eq
    {T : Sylow 2 G} {X : Subgroup G} [X.Normal]
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : ActorCases T X hTX) (hgen : X ⊔ (T : Subgroup G) = ⊤)
    (hcore : pCore 2 G = ⊥) : generalizedFitting G = X :=
  generalizedFitting_eq_of_le_two_quotient X hc.le_generalizedFitting
    (isPGroup_quotient_of_sup_eq_top X T T.isPGroup' hgen) hcore

end CFSG.Quasithin.ChapterD.Section03

namespace CFSG.Quasithin.ChapterD.Section03
open Theory.GroupTheory
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

theorem InternalModuleHypotheses.faithfulOrbit_generalizedFitting
    (h : InternalModuleHypotheses K ρ T X I)
    (hgen : X ⊔ (T : Subgroup G) = ⊤) :
    generalizedFitting (subspaceActionImage ρ (orbitSpan ρ ⊤ I)) =
      restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X := by
  let := h.normal
  let W := orbitSpan ρ ⊤ I
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  have hf : Function.Surjective f := invariantActionHom_surjective ρ W _
  have hsource := h.faithfulOrbit_source
  let : (X.map f).Normal := Normal.map inferInstance f hf
  have hm : X.map f = restrictedSubgroup ρ W X := invariantActionHom_map ρ W _ X
  have hcases : ActorCases (T.mapSurjective hf) (X.map f)
      (by rw [normalizer_eq_top]; exact le_top) := by
    simpa only [hm] using hsource.cases
  have hgenbar : X.map f ⊔ (T.mapSurjective hf : Subgroup _) = ⊤ := by
    change X.map f ⊔ (T : Subgroup G).map f = ⊤
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ hf]
  exact (hcases.generalizedFitting_eq hgenbar h.faithfulOrbit_twoCore_eq_bot).trans hm

/-- The local faithful image has precisely the source's semisimple or odd-prime shape. -/
theorem InternalModuleHypotheses.faithfulOrbit_fitting_structure
    (h : InternalModuleHypotheses K ρ T X I)
    (hgen : X ⊔ (T : Subgroup G) = ⊤) :
    generalizedFitting (subspaceActionImage ρ (orbitSpan ρ ⊤ I)) =
        restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X ∧
      (componentLayer (restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X) = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p
          (restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X)) :=
  ⟨h.faithfulOrbit_generalizedFitting hgen, h.faithfulOrbit_source.cases.layer_or_prime_group⟩

end CFSG.Quasithin.ChapterD.Section03

