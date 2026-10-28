module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.OuterGeometry.Image
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.OuterGeometry.SelectedOrbits

/-!
# Source 13.1.12: the outer A₅-cover branch

Construct the S₅ marking of the original LT-action and apply the selected
orbit computation to its literal centralizers. The source commutator
identity discharges cover generation. Genuine outerness of the original
natural T-action is the remaining earlier input, discharged by the parent
A₅-cover orbit assembly. Central rank two is unnecessary for this deduction.

Source: Aschbacher--Smith, printed p.872 (PDF p.889).
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural SemilinearNormalizer
namespace Marking
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

/-- Original13.1.12's outer A₅-cover branch: an actual S₅ quotient of LT,
with literal conjugation kernel, the original L mapping onto A₅, and
equivariance on the original natural lines. The selected centralizer indices
are two and thirty. The central-rank-two premise is not needed for this
conditional branch once genuine outerness of the natural action is supplied. -/
theorem source_outer_geometry
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (ho : d.HasOuterNaturalAction) :
    ∃ π : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5),
      Function.Surjective π ∧
      π.ker = (centralizer (normalizerMoved L : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      (L.subgroupOf (L ⊔ (T : Subgroup G))).map π = alternatingGroup (Fin 5) ∧
      (∀ (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (i : Fin 5),
        ∃ c : F, c ≠ 0 ∧ d.naturalActor a (lineVector i) = c • lineVector (π a i)) ∧
      ∀ u : normalizerMoved L, u ≠ 1 →
        IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
          (Subgroup.normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)) →
        (¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) →
        (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) =
          if d.projection (d.coordinates u).toAdd = 0 then 2 else 30 := by
  let hm := source_moved_commutator h hL hn
  refine ⟨d.outerQuotient hm,d.outerQuotient_surjective hm ho,
    d.outerQuotient_kernel hm ho,d.outerQuotient_component hm,
    d.outerQuotient_lines hm,?_⟩
  intro u _ hlocal hmove
  exact d.selected_centralizer_index (d.outerMarking hm ho) h hL hn u hlocal hmove


/-- The literal classification consumer: the outer natural-cover branch
supplies 13.1.12(2) and the component four-group used in 13.1.12(1).
The genuine outer-action premise remains with the A₅-cover assembly. -/
theorem source_outer_orbit_and_stabilizer
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (ho : d.HasOuterNaturalAction)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      ∃ S : Sylow 2 SL, (S : Subgroup SL) =
        (((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G)).subgroupOf L).map d.component ∧
        Nat.card S = 4 ∧ ∀ s : S, s ^ 2 = 1 := by
  exact ⟨d.centralizer_sylow_index_le_two
    (d.outerMarking (source_moved_commutator h hL hn) ho) h hL hn u hlocal,
    d.source_selected_four_group h hL hn u hlocal⟩

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
