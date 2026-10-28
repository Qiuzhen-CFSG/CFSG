module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.BlockArgument
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.LowerBound
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal

/-!
# The unique remaining natural-hyperplane case

The completed E.6.3 bound excludes every parameter above two. The SL₃
central kernel vanishes. Together with source uniqueness, this reduces any
escaping hyperplane to the degree-two Sp₄ marking, with a central kernel of
order two complemented by that same hyperplane.

The pointwise E.6.14 application below discharges characteristic-two
inheritance, block selection, Thompson movement and the local index theorem.
Its remaining inputs are precisely the original hyperplane's Sylow-fixed
intersection, faithful cubic actor and maximal stabilizer of index other
than two. Constructing those orthogonal-cover facts is still owned by
qt-d-1222-natural-weak-parameters; the parent weak-closure source task
retains final discharge of the permitted earlier-source premises.

Source: Aschbacher--Smith, 11.2.2, printed pp.767--768.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every escaping hyperplane is the precise exceptional source case.
Neither a numerical bound nor a splitting assumption is supplied. -/
theorem escaping_hyperplane_sp4_four (c : Coordinates D S.field)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∧
      S.field.degree = 2 ∧ Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2 ∧
      U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥ ∧
      U ⊔ (V ⊓ centralizer (L : Set G)) = V := by
  have hsmall : naturalParameter D S c ≤ 2 := by
    by_contra hn
    exact hescape (hyperplane_centralizer_of_parameter_gt_two D S c hE
      (lt_of_not_ge hn) hUV hU)
  have hk := escaping_hyperplane_kernel_card D S c hE hunique hUV hU hescape
  cases c with
  | sl3 m => exact (hescape (centralizer_le_of_central_kernel_eq_bot D S (.sl3 m)
      hE (Preliminary.sl3_centralizer_eq_bot D S m) hUV hU)).elim
  | sp4 m =>
    refine ⟨⟨m⟩, ?_, hk⟩
    have hn := S.nonbinary
    change S.field.degree ≤ 2 at hsmall
    omega
  | g2 m =>
    have hn := S.nonbinary
    change 2 * S.field.degree ≤ 2 at hsmall
    omega

/-- Source E.6.6(4) in the self-centralizing-core convention required by
E.6.14, with the earlier Chapter 1 inheritance supplied. -/
theorem characteristicTwo_of_sylow_fixed_intersection
    {M U : Subgroup G}
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hUV : U ≤ V) (hne : U ≠ ⊥)
    (hint : U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥) :
    HasCharacteristicTwo (centralizer (U : Set G)) := by
  let := hE.elementary
  have hp := (IsElementaryAbelian.isPGroup 2 V).to_le hUV
  have hi : ((T : Subgroup G) ⊓ centralizer (T : Set G)) ⊓ U ≠ ⊥ := by
    intro he
    apply hint
    apply le_bot_iff.mp
    rw [← he]
    exact le_inf (le_inf (inf_le_left.trans (hUV.trans hE.le_sylow))
      (inf_le_right.trans inf_le_right)) inf_le_left
  have earlier := source_earlierLocalFacts hE
  have hc := earlier.centralizers U (normalizer (U : Set G))
    (earlier.central_intersection U hp hne hi) U.le_normalizer hp
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (MulEquiv.subgroupCongr
      (inf_eq_right.mpr (Subgroup.centralizer_le_normalizer (U : Set G))))).mp hc

/-- The literal natural-module E.6.14 application. All local group-theoretic
inputs are proved; the three remaining hypotheses describe the actual
orthogonal-cover geometry and remain with this task's owner. -/
theorem centralizer_le_of_natural_stabilizer (c : Coordinates D S.field)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hint : U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥)
    (hthree : HasFaithfulThreeAction U)
    (hmax : localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G))
    (hindex : (localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex
      (L ⊔ (T : Subgroup G)) ≠ 2) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  have hsmall : subgroupCorank V U < localM V := by
    rw [hU, localM_eq_naturalParameter D S c]
    exact naturalParameter_gt_one D S c
  have hne := nontrivial_of_corank_lt_localM hsmall
  have hQ : L ⊔ (T : Subgroup G) ≤
      normalizer (sylowCentralizer (T : Subgroup G) V : Set G) := by
    change L ⊔ (T : Subgroup G) ≤ normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)
    rw [seed_sylow_centralizer D S]
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact centralizer_le_of_hyperplane_stabilizer hE hne hUV
    (hE.oddCentralizerCondition_of_small hUV hsmall) hU
    (characteristicTwo_of_sylow_fixed_intersection hE hUV hne hint)
    hthree le_sup_right hQ (fun N hN hLN => hunique N hN (le_sup_left.trans hLN))
    hmax hindex

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
