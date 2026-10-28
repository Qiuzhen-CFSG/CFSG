module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.SmallDerived.Central
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeObstruction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeSylowContainment
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder
public import Theory.SpecificGroups.Tits.ThreeSylowContainment

/-!
# The parabolic obstruction for G₂(2)′ and the Tits group

The actual complement image in the central quotient has order nine or 27
if the pair is not reducible. Neither marked parabolic in either concrete
model has order divisible by nine. The G₂ parabolics are restricted to the
actual commutator subgroup. For the Tits group, the proved isomorphism from
Parrott's presentation to the Atlas model supplies the comparison.

The final two theorems prove pair-action reducibility from an actual central
quotient isomorphism with either model. For G₂(2)′, the proved Sylow-overgroup
order obstruction uses simplicity transported from the quasisimple input.
For the Tits group, the proved containment in the second marked parabolic
supplies the obstruction. Central kernels, Sylow transport and conjugacy
are handled by the preceding reductions, with no remaining model premises.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.SmallDerived
universe u
variable {Q : Type u} [Group Q] [Finite Q]
variable {S : Sylow 2 Q} {R : Subgroup Q}

open Atlas.G2.BinaryParabolicPair

/-- A nonreducible complement image fits in neither restricted binary G₂ parabolic. -/
theorem g2_complement_parabolic_obstruction (h : PairInput S R)
    (hn : ¬ PairReducible (S : Subgroup Q) R)
    (e : Q ⧸ center Q ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (¬ R.map (quotientModelMap e) ≤ derivedFirst) ∧
      (¬ R.map (quotientModelMap e) ≤ derivedSecond) :=
  ⟨model_complement_not_le_of_nine_not_dvd h hn e
      ThreeObstruction.derived_first_nine_not_dvd,
    model_complement_not_le_of_nine_not_dvd h hn e
      ThreeObstruction.derived_second_nine_not_dvd⟩

/-- The faithful presentation comparison puts a nonreducible complement image
in neither of the two actual Atlas parabolics. -/
theorem tits_complement_parabolic_obstruction (h : PairInput S R)
    (hn : ¬ PairReducible (S : Subgroup Q) R)
    (e : Q ⧸ center Q ≃* Tits.ParrottGroup) :
    (¬ R.map (quotientModelMap (e.trans Tits.parrottFiniteImageEquiv)) ≤
      Tits.ExceptionalParabolics.first) ∧
    (¬ R.map (quotientModelMap (e.trans Tits.parrottFiniteImageEquiv)) ≤
      Tits.ExceptionalParabolics.second) := by
  constructor
  · apply model_complement_not_le_of_nine_not_dvd h hn
    rw [Tits.ReeLocalBlockOrders.first_card]
    decide
  · apply model_complement_not_le_of_nine_not_dvd h hn
    rw [Tits.RelativeSecondBlockLayers.second_card]
    decide

/-- A conditional containment route for actual proper binary G₂ Sylow overgroups.
All central-cover and conjugacy obligations are discharged by the reduction. -/
theorem g2_pairReducible_of_containment (h : PairInput S R)
    (e : Q ⧸ center Q ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hcont : ∀ H : Subgroup DerivedModel, H ≠ ⊤ → Group.IsSolvable H →
      (derivedSylow : Subgroup DerivedModel) ≤ H →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) →
      H ≤ derivedFirst ∨ H ≤ derivedSecond) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_marked_sylow_overgroups h e derivedSylow
  intro H hH hs hU hprimes hd
  rcases hcont H hH hs hU hprimes with hfirst | hsecond
  · exact ThreeObstruction.derived_first_nine_not_dvd
      (hd.trans (card_dvd_of_le hfirst))
  · exact ThreeObstruction.derived_second_nine_not_dvd
      (hd.trans (card_dvd_of_le hsecond))

/-- A conditional containment route for the marked Sylow subgroup in the
certified Atlas model, reached through the actual Parrott isomorphism. -/
theorem tits_pairReducible_of_containment (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Tits.ParrottGroup)
    (hcont : ∀ H : Subgroup Tits.Atlas1600Group, H ≠ ⊤ → Group.IsSolvable H →
      Tits.atlas1600SylowTwoSubgroup ≤ H →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) →
      H ≤ Tits.ExceptionalParabolics.first ∨ H ≤ Tits.ExceptionalParabolics.second) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_marked_sylow_overgroups h (e.trans Tits.parrottFiniteImageEquiv)
    Tits.atlas1600SylowTwo
  intro H hH hs hU hprimes hd
  rw [Tits.atlas1600SylowTwo_coe] at hU
  rcases hcont H hH hs hU hprimes with hfirst | hsecond
  · have hh := hd.trans (card_dvd_of_le hfirst)
    rw [Tits.ReeLocalBlockOrders.first_card] at hh
    norm_num at hh
  · have hh := hd.trans (card_dvd_of_le hsecond)
    rw [Tits.RelativeSecondBlockLayers.second_card] at hh
    norm_num at hh

/-- The small-field exclusion for the actual derived binary G₂ model.
Simplicity is inherited from the quasisimple central cover, and the proved
Sylow-overgroup order obstruction excludes the nonreducible complement image. -/
theorem g2_pairReducible_of_equiv (h : PairInput S R)
    (e : Q ⧸ center Q ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    PairReducible (S : Subgroup Q) R := by
  let _ : IsSimpleGroup (Q ⧸ center Q) := h.quasisimple.simple
  let _ : IsSimpleGroup DerivedModel := e.symm.isSimpleGroup
  exact reducible_of_marked_sylow_overgroups h e derivedSylow
    ThreeSylowContainment.nine_not_dvd_card_of_sylow_le

/-- The small-field exclusion for the actual Tits group, using the certified
Parrott–Atlas comparison and the proved containment of genuine Sylow overgroups. -/
theorem tits_pairReducible_of_equiv (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Tits.ParrottGroup) :
    PairReducible (S : Subgroup Q) R :=
  tits_pairReducible_of_containment h e Tits.ThreeSylowContainment.containment

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.SmallDerived
