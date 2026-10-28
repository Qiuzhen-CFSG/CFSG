module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Sporadic.Transport
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Sporadic.Numerics

/-!
# Reduction of the sporadic source exclusion to the M₂₂ row

The original component quotient embeds in the literal deleted-point quotient,
with the same two-central involution. Its elementary sixteen and centralizer
order exclude every sporadic model except M₂₂. The remaining interface keeps
the actual component, its commutator identity, central-cover quotient and
original action, as well as all local geometry and Sylow hypotheses.

The final theorem applies this reduction to the original factor consumer.
The M₂₂ structural exclusion remains an explicit source obligation: this
module does not claim the full sporadic exclusion or original 14.3.20.
Source: Aschbacher--Smith, 14.3.20, printed p.998, and 1.1.5(3)(f), p.502.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}

namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- The surviving actual component and two-central action with its M₂₂ quotient. -/
def MathieuTwentyTwoComponent (z : G) : Prop :=
  P.ComponentWithAction z (fun B α =>
    Nonempty (((B.subgroupOf P.globalCentralizer) ⧸
      pCore 2 (B.subgroupOf P.globalCentralizer)) ≃*
        ClassificationModels.SporadicName.m22.Carrier) ∧ TwoCentralInner α)

/-- All other sporadic rows are excluded in the literal marked source quotient. -/
theorem sporadicComponent_mathieuTwentyTwo (hA : ElementaryFactor F L A)
    (z : G) (hz : F.Vi 1 = zpowers z)
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element)
    (hlocal : P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz))
    (h : P.SporadicComponent z) : P.MathieuTwentyTwoComponent z := by
  obtain ⟨B, hBC, hKB, hcomp, hcomm, α, hα, name, hname, he, ha⟩ := h
  have hm : P.ComponentWithAction z (fun B α =>
      Nonempty (((B.subgroupOf P.globalCentralizer) ⧸
        pCore 2 (B.subgroupOf P.globalCentralizer)) ≃* name.Carrier) ∧ TwoCentralInner α) :=
    ⟨B, hBC, hKB, hcomp, hcomm, α, hα, he, ha⟩
  obtain ⟨t, j, hj, _, hmark, ht, htc, hr⟩ :=
    P.exists_marked_model_embedding hA name z hz hcore hm
  let C := centralizer ({P.pointQuotientMap (P.markedGenerator hA.seed_le z hz)} :
    Set P.PointQuotient)
  let k : centralizer ({t} : Set name.Carrier) →* C := {
    toFun x := ⟨j x, by
      apply mem_centralizer_singleton_iff.mpr
      rw [← hmark, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.mp x.property]⟩
    map_one' := Subtype.ext j.map_one
    map_mul' x y := Subtype.ext (j.map_mul x y) }
  have hk : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (hj (congrArg Subtype.val hxy))
  have hd : Nat.card (centralizer ({t} : Set name.Carrier)) ∣ 2304 :=
    (card_dvd_of_injective k hk).trans (P.quotientCentralizer_card_dvd _ hlocal)
  have hn := Sporadic.name_eq_m22_of_rank_and_centralizer name hname hr t ht htc hd
  subst name
  exact hm

end MarkedPoint

/-- Precisely the remaining M₂₂ branch, with the original local inputs. -/
def MathieuTwentyTwoExclusionSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ∀ hA : ElementaryFactor F L A, A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G) (hz : F.Vi 1 = zpowers z),
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.globalCentralizer.pCoreIn 2 = zpowers P.element →
      P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz) →
      P.MathieuTwentyTwoComponent z → False

/-- Assembly awaits only the structural M₂₂ exclusion among the sporadic rows. -/
theorem sporadicExclusionSource_of_mathieuTwentyTwo
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (h22 : MathieuTwentyTwoExclusionSource F L) : SporadicExclusionSource F L := by
  intro A hA hlt P z hz hgeom hSylow hcore hlocal hsporadic
  exact h22 A hA hlt P z hz hgeom hSylow hcore hlocal
    (P.sporadicComponent_mathieuTwentyTwo hA z hz hcore hlocal hsporadic)

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The original factor consumer with all other sporadic rows discharged.
The M₂₂, even-model, local-extension and earlier geometric inputs remain explicit. -/
theorem factorSelfCentralizing_of_local_mathieuTwentyTwo_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hgeometry : FourCenterSource F (sourceResidual M Mc))
    (hcore : CoreComponentSource F (sourceResidual M Mc))
    (hlocal : QuotientCentralizerSource F (sourceResidual M Mc))
    (heven : EvenExclusionSource F (sourceResidual M Mc))
    (h22 : MathieuTwentyTwoExclusionSource F (sourceResidual M Mc)) :
    FactorSelfCentralizing F (sourceResidual M Mc) :=
  factorSelfCentralizing_of_local_model_inputs hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hs hgeometry hcore hlocal heven
    (sporadicExclusionSource_of_mathieuTwentyTwo F (sourceResidual M Mc) h22)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
