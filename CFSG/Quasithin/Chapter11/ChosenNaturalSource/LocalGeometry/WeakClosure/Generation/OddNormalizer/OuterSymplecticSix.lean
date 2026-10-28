module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PlacedModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterRemaining
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.BinarySixFrattini

/-!
# Excluding the binary symplectic six-space in both component actions

The Sylow Frattini quotient of the native Sp₆(2) matrix group has order
at most 32. Field transport and the characteristic-two central quotient
identify this with the Sylow quotient of the actual component model.
The proved PSL₃(4) section obstruction then rules out its outer action.
The inner placement already forces twelve factors of two in the central
quotient order, whereas Sp₆(2) has only nine. Thus this row is excluded
on the same original moved component in both actions.

Only the four odd-characteristic outer rows remain. The Source endpoint
applies this to the original odd actor and literal Hall kernel, preserving
the full SL₃(4) cover, cubic center and original module of order 64.
The remaining outer rows and moved J₄ stay with this task; ordinary C.2.8
stays with qt-d-1222-natural-point-fixed-summand and final 11.2.1 assembly
with qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticSix
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The actual binary symplectic six-space component cover cannot carry
an outer section of the original central quotient. -/
theorem moved_outer_not_symplectic_six {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) : False := by
  let P : Sylow 2 (K ⧸ center K) := default
  apply moved_outer_not_of_frattini_le_thirtytwo D S K hK ho (.symplectic_binary hm) P
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let a : (K ⧸ center K) ≃* Sp (ZMod 2) :=
    (e.trans (pspFieldEquivZModTwo F hF)).trans EvenProjective.equiv.symm
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : P ≃* Q := a.subgroupMap (P : Subgroup (K ⧸ center K))
  rw [SylowFrattiniBounds.card_congr b]
  exact BinarySixFrattini.frattini_card_le_thirtytwo Q

open Chapter4 Chapter4.Section04
/-- The same original moved component avoids binary Sp₆ in both actions.
The placed action retains its two-power divisibility from the full cover. -/
theorem moved_component_not_symplectic_six {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) : False := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨_,_,_,_,_,_,hd⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv] at hd
    have hh := hd.trans (card_quotient_dvd_card (center (Sp F)))
    rw [card_sp_of_card_two hF] at hh
    norm_num at hh
  · exact moved_outer_not_symplectic_six D S K hK ho hm

/-- Every surviving outer component row is odd-characteristic. This is
an actual model disjunction with the original source field parameters. -/
theorem moved_outer_odd_models {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) : RemainingOddPlacedModels (K ⧸ center K) := by
  exact (moved_outer_remaining_models D S K hK hm ho).resolve_left
    (fun h => moved_outer_not_symplectic_six D S K hK ho h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
