module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SelectedEndpoint.Geometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.OrbitMatching.CommutatorImages

/-!
# Selected endpoint application to the original suitable element

The source selection, both denominator identifications, the opposite central
point in the commutator and the two commutator containments are discharged by
the preceding geometry. The remaining inputs are the actual natural/dual
markings, the non-FF and two-rank model facts, and the three low-rank image
profiles. The symmetric cases use the literal commutator images on both
sides; the asymmetric case moves a denominator/support intersection.

The resulting crossing retains the original suitable u. Its conjugator is
x⁻¹g, where g is the selected endpoint representative; every subgroup label
is transported by that same element. This is a conditional bridge, not a
claim that the remaining source model profiles have been constructed.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (sectionModel : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ)
    (hnonff : ¬ IsFFModule ρ) (hrank : primeRank 2 (Source.Hstar Mc) ≤ 2)
    (W W' : Subgroup G)
    (f : (Mc ⊓ normalizer (W : Set G) : Subgroup G) →*
      BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u)
    (K B : Subgroup G) (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (φ : K →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hφ : Function.Surjective φ)
    (d : BinaryConjugationSection K B (centralInvolutions T) (naturalDualRepresentation.comp φ))
    (hW : ∀ v : B, (v : G) ∈ W ↔ (d.coordinates v).toAdd.2 = 0)
    (hW' : ∀ v : B, (v : G) ∈ W' ↔ (d.coordinates v).toAdd.1 = 0)

local notation "U" => conjugateSpanBy (localModule T M) Mc
local notation "h" => ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab

include sectionModel hnonff hrank hf c hs hsW huW hu hK hBU hφ hW hW' in
/-- The selected critical endpoint supplies the original terminal crossing
once the marked low-rank image calculations are supplied. All geometry is
constructed, including the rank split and the opposite central point. -/
theorem source_crossing_of_selected_profiles
    (hB : ⁅U,Mc⁆ ≤ B)
    (himages : ∀ i : (h).CriticalEndpoint,
      CriticalGeometry.Reorientation.QuadraticMember ρ (Source.starImage Mc (i.conjugate U)) →
      0 < rank (Source.starImage Mc (i.conjugate U)) →
      rank (Source.starImage Mc (i.conjugate U)) ≤ 2 →
      Nat.log 2 ((U ⊓ i.conjugate (Mc.pCoreIn 2)).relIndex U) =
        rank (Source.starImage Mc (i.conjugate U)) →
      (∀ v ∈ d.imageSpace ⁅U,i.conjugate U⁆, quadratic v = 0) ∧
      (∀ v ∈ d.imageSpace ((⁅U,i.conjugate U⁆).map
        (MulAut.conj i.representative⁻¹).toMonoidHom), quadratic v = 0) ∧
      ∃ v ∈ d.imageSpace ⁅U,i.conjugate U⁆, IsPure v)
    (hmoving : ∀ i : (h).CriticalEndpoint,
      CriticalGeometry.Reorientation.QuadraticMember ρ (Source.starImage Mc (i.conjugate U)) →
      rank (Source.starImage Mc (i.conjugate U)) = 2 →
      Nat.log 2 ((U ⊓ i.conjugate (Mc.pCoreIn 2)).relIndex U) = 1 →
      ∃ S : Subgroup G, (S = W ∨ S = W') ∧
        i.conjugate U ≤ normalizer (S : Set G) ∧
        ¬ i.conjugate U ≤ centralizer (((U ⊓ i.conjugate (Mc.pCoreIn 2)) ⊓ S) : Set G)) :
    ∃ i : (h).CriticalEndpoint, ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  obtain ⟨q⟩ := source_selected_endpoint hG T hempty hM hunique hmany hcard e hab
    sectionModel hnonff hrank
  have hp : 0 < rank (Source.starImage Mc (q.endpoint.conjugate U)) :=
    q.denominator_pos.trans_le q.comparison
  have symmetric
      (heq : Nat.log 2 ((U ⊓ q.endpoint.conjugate (Mc.pCoreIn 2)).relIndex U) =
        rank (Source.starImage Mc (q.endpoint.conjugate U))) :
      ∃ x ∈ Mc, ∃ k : G,
        k = x⁻¹ * q.endpoint.representative ∧
        (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
          (q.endpoint.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
        ∃ crossing : SourceCrossingGeometry (localModule T M) Mc Mc u,
          crossing.A = U ∧ crossing.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
    obtain ⟨hRB,hRBg,hZR⟩ := q.commutator_inputs B hB
    obtain ⟨hsing,hsing',hpure⟩ := himages q.endpoint q.actor_quadratic hp q.actor_rank_le_two heq
    exact OrbitMatching.source_crossing_of_symmetric_commutator_images
      hG T hempty hM hunique hmany hcard e hab W W' f hf c s hs hsW u huW hu
      K B hK hBU φ hφ d hW hW' q.endpoint hRB hRBg hZR hsing hsing' hpure
  rcases q.rank_cases with h1 | h2 | h21
  · exact ⟨q.endpoint,symmetric (h1.2.trans h1.1.symm)⟩
  · exact ⟨q.endpoint,symmetric (h2.2.trans h2.1.symm)⟩
  · obtain ⟨S,hS,hn,hm⟩ := hmoving q.endpoint q.actor_quadratic h21.1 h21.2
    exact (OrbitMatching.source_false_of_moving_denominator_support
      hG T hempty hM hunique hmany hcard e hab W W' f hf c s hs hsW u huW hu
      q.endpoint S hS hn hm).elim

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
