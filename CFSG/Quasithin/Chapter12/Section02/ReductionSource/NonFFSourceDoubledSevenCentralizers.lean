module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenPair
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenCentralizerBounds
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceKnownSimple
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.HeldCenter
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple

/-!
# The doubled A₇ centralizer argument on the chosen orbit

The actual H.8 pair supplies the odd-prime displacement estimates. E.6.23,
with its original known-simple producers, excludes escaping hyperplanes.
The row's cyclic obstruction then proves r ≥ 4 and controls every
centralizer below corank six whose induced action is odd, equivalently
whose original O^{2′} residual centralizes the whole orbit. No generic
E.6.3 bound or assumed numerical callback is used.

Consequently any remaining small escaping centralizer has an actual
involution in its image on the same orbit, with fixed codimension four.
The complementary E.6.27 branch, the mixed-centralizer geometry and the
outside-overgroup bound w ≤ 2 still have to be proved to obtain
DoubledSevenBounds and the final chosen-module contradiction.
Source: Aschbacher–Smith H.8, E.6.11(2), E.6.23 and 7.5.5, p.701.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE ChapterE.Section06
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every odd-prime actor moves at least four dimensions on the literal orbit. -/
theorem sourceOrbit_seven_odd_prime_codim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (x : Automizer D.sourceOrbit) (hp : (orderOf x).Prime) (hodd : orderOf x ≠ 2) :
    4 ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers x) := by
  obtain ⟨_,_,_,P,E,_,_⟩ := D.sourceOrbit_seven_H8_pair h hd σ hσ hmodel
  have hc : fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers x) =
      fixedCodim P.representation (zpowers (E.groupEquiv x)) := by
    simpa only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom] using
      fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit) P.representation
        E.groupEquiv.toMonoidHom E.linearEquiv E.intertwines (zpowers x)
  rw [hc]
  have he := orderOf_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective x
  exact P.odd_prime_fixedCodim _ (he ▸ hp) (he ▸ hodd)

/-- The genuine E.6.23 hyperplane theorem on the original orbit. -/
theorem sourceOrbit_seven_globalR_gt_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    1 < globalR D.sourceOrbit := by
  have hE := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  have hm := (D.sourceOrbit_seven_H8_parameters h hd σ hσ hmodel).1
  have hm' : 2 < localM D.sourceOrbit := by omega
  exact Hyperplanes.source_rank_gt_one_knownSimple hE hm'
    (InvariantSubspaces.source_commonNormalInput_knownSimple T)
    (Hyperplanes.ComponentBalance.sevenExcluded_knownSimple hE (Or.inr hm'))

/-- The initial r ≥ 4 bound, with all source and representation inputs
discharged from the original A₇ marking. -/
theorem sourceOrbit_seven_four_le_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    4 ≤ globalR D.sourceOrbit :=
  doubledSeven_four_le_globalR (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd)
    (D.sourceOrbit_seven_H8_parameters h hd σ hσ hmodel).1
    (D.sourceOrbit_seven_globalR_gt_one h hd σ hσ hmodel)
    (D.sourceOrbit_seven_odd_prime_codim h hd σ hσ hmodel)


/-- The Γ branch of 7.5.5 on the actual chosen orbit, retaining exactly
the original O^{2′}(C_M(U)) ≤ C_M(W) condition. -/
theorem sourceOrbit_seven_small_residual_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {U : Subgroup G} (hU : U ≤ D.sourceOrbit) (hc : subgroupCorank D.sourceOrbit U < 6)
    (hres : oddCentralizerCondition (normalizer (L : Set G)) D.sourceOrbit U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨C⟩ := D.sourceOrbit_seven_action_coordinates h hd σ hσ hmodel
  have hne : U ≠ ⊥ := by
    intro he
    rw [he,corank_bot,D.sourceOrbit_seven_dimension h hd σ hmodel] at hc
    omega
  exact doubledSeven_small_oddCentralizer
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd) C.automizer
    (D.sourceOrbit_seven_globalR_gt_one h hd σ hσ hmodel)
    (D.sourceOrbit_seven_odd_prime_codim h hd σ hσ hmodel) hne hU hc hres


/-- Oddness of the literal centralizer image supplies its O^{2′} condition. -/
theorem sourceOrbit_seven_small_odd_image_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {U : Subgroup G} (hU : U ≤ D.sourceOrbit) (hc : subgroupCorank D.sourceOrbit U < 6)
    (ho : Odd (Nat.card (inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))))) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  apply D.sourceOrbit_seven_small_residual_centralizer h hd σ hσ hmodel hU hc
  apply oddCentralizerCondition_of_odd_image ?_ ho
  exact inf_le_left.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).symm.le

/-- Any remaining small escaping centralizer has an actual involution in
its action image, fixing U and having fixed codimension four on the orbit. -/
theorem sourceOrbit_seven_small_escape_involution
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {U : Subgroup G} (hU : U ≤ D.sourceOrbit) (hc : subgroupCorank D.sourceOrbit U < 6)
    (he : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    ∃ t : Automizer D.sourceOrbit,
      t ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ∧
      orderOf t = 2 ∧ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers t) = 4 := by
  have hn : ¬ Odd (Nat.card (inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G)))) :=
    fun ho => he (D.sourceOrbit_seven_small_odd_image_centralizer h hd σ hσ hmodel hU hc ho)
  have hdvd := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hn)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G)))
    2 hdvd
  have ht' : orderOf (t : Automizer D.sourceOrbit) = 2 := (Subgroup.orderOf_coe t).trans ht
  exact ⟨t,t.property,ht',(D.sourceOrbit_seven_H8_parameters h hd σ hσ hmodel).2.2.2.2.2 t ht'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
