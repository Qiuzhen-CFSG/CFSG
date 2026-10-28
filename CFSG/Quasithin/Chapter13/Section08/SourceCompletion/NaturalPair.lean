module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.ClosurePair
public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The original source critical pair for the natural A₆ case

The order-two flag line supplies its unique nonidentity generator and the
original point normalizer is its full centralizer. The actual natural A₆
coordinates supply transitivity, through Section 13.7's checked action.
Consequently the original full abelian V-span and F.9 applicability construct
a normalized critical pair with odd length at least three.

The remaining inputs are precisely earlier 13.7.8 and 13.5.7, with active
source producers; no parity, bound, chosen point, transporter or geometry
conclusion is an input. Source: Aschbacher--Smith, 13.8.2--4, pp.946--947.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}

private theorem point_generator (d:NaturalSetup T L V V₁ V₂ V₃ M G₁) :
    ∃z:G,z≠1 ∧ V₁=zpowers z ∧ G₁=centralizer ({z}:Set G) := by
  obtain ⟨z,hz,huniq⟩ := (Nat.card_eq_two_iff' (1:V₁)).mp d.line_card
  have hzG : (z:G)≠1 := fun he=>hz (Subtype.ext he)
  have hp : V₁=zpowers (z:G) := by
    apply le_antisymm
    · intro x hx
      by_cases hx1 : x=1
      · exact hx1 ▸ (zpowers (z:G)).one_mem
      · have he : (⟨x,hx⟩:V₁)=z := huniq _ (fun h=>hx1 (congrArg Subtype.val h))
        rw [show x=(z:G) from congrArg Subtype.val he]
        exact mem_zpowers (z:G)
    · exact zpowers_le.mpr z.property
  have ho : orderOf (z:G)=2 := by rw [←Nat.card_zpowers,←hp]; exact d.line_card
  exact ⟨z,hzG,hp,d.first_normalizer.trans ((congrArg (fun A : Subgroup G => normalizer (A:Set G)) hp).trans (normalizer_zpowers_eq_centralizer_of_order_two _ ho))⟩

theorem NaturalSetup.exists_criticalPair
    (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    ∃c:CriticalPair L (T:Subgroup G) H V, 3≤c.path.length ∧ Odd c.path.length := by
  obtain ⟨z,hz,hpoint,hG₁⟩ := point_generator d
  let : IsMulCommutative (centralizerConjugateClosure V z) := by
    rw [centralizerConjugateClosure_eq_conjugateSpanBy,←hG₁]
    exact hspan
  have hzV:z∈V:=d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) (by rw [hpoint]; exact mem_zpowers z)
  let : IsMulCommutative (centralizerConjugateClosure (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).V z) :=
    show IsMulCommutative (centralizerConjugateClosure V z) from inferInstance
  exact f9_pair_of_abelian_closure _ hF9 z hz hpoint
    (fun v hv hv1=>Section07.natural_nonzero_transitive d hzV hv hz hv1)
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
