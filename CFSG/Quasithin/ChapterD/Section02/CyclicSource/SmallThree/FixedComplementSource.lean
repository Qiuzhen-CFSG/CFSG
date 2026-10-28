module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplement
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplementRepresentation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Canonical
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.RestrictedInverter
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import Theory.Representation.CyclicFixedRank

/-!
# The original small-three fixed-complement conclusion

The canonical family is transported from the original binary representation
without changing its action. Coprime action splits its support from its fixed
subspace. On that fixed subrepresentation, full movement by the odd Fitting
subgroup is inherited from the original source hypothesis. Cyclic preparation
centralizes the complementary primes, so a residual displacement line yields
an inverted element of the actual three-core. The local fixed-complement
theorem excludes that residual action.

This discharges the local geometric assertion for every noncentralizing
small-support involution in Aschbacher--Smith D.2.25, printed p.190,
`refs/quasithin.pdf`. The indecomposable support-generation argument is the
separate consumer; no indecomposability assumption is needed here.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The source D.2.25 fixed-complement step, from the original cyclic
hypotheses. Every small-support involution not centralizing the canonical
three-group fixes its fixed subspace pointwise. -/
theorem CoreHypotheses.fixed_smallThree_complement
    (h : CoreHypotheses ρ)
    (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G)=⊤)
    (hfive : ∀ A∈QhatStar ρ,⁅pCore 5 G,A⁆=⊥)
    (hq : cubicRatio ρ=2) {t : G} (ht : t∈smallSupportInvolutions ρ) :
    letI := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    t∉centralizer (Y:Set G) → fixedSpace ρ Y ≤ fixedSpace ρ (zpowers t) := by
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  change t∉centralizer (Y:Set G) → fixedSpace ρ Y ≤ fixedSpace ρ (zpowers t)
  intro hnc
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  have hti : IsInvolution t := by
    refine ⟨?_,?_⟩
    · intro he
      have hh := ht.1
      rw [he,orderOf_one] at hh
      omega
    · rw [←ht.1]
      exact pow_orderOf_eq_one t
  have hfour : Nat.card (commutatorAction (zpowers t) (Multiplicative V))=4 := by
    rw [BinaryGroupAction.commutator_card,Representation.CyclicFixedRank.commutator_eq_range,
      ←fixedCodim_zpowers_eq_displacement_rank,(h.smallSupport_starred hq ht).2]
    norm_num
  have hYodd : Odd (Nat.card Y) :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot h.twoCore).of_dvd_nat
      (Subgroup.card_dvd_of_le (smallSupportGroup_le_fitting G (Multiplicative V) 1))
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (Multiplicative V)) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (Multiplicative V)).exists_card_eq
    rw [hn]
    exact hYodd.coprime_two_right.pow_right n
  have hsplit := (ActionSupport.fixed_support_isCompl Y hcop).symm
  have hnc' : ¬ ∀y∈Y,Commute t y := by
    intro hh
    apply hnc
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hh y hy).symm.eq)
  have hf := SmallThree.fixed_complement_of_residual_witness
    (V:=Multiplicative V) t hti hfour hsplit hnc' ?_
  · intro v hv
    rw [mem_fixedSpace_zpowers_iff]
    exact congrArg Multiplicative.toAdd (hf (Multiplicative.ofAdd v) hv)
  · intro hline
    let W := normalFixed ρ Y
    have hcard := BinaryGroupAction.subrepresentation_commutator_card ρ W (zpowers t)
    have hr : Module.finrank (ZMod 2) (W.toRepresentation t - 1).range=1 := by
      have he : 2 ^ Module.finrank (ZMod 2)
          (subspaceCommutator W.toRepresentation ⊤ (zpowers t))=2^1 :=
        hcard.symm.trans hline
      have hd := Nat.pow_right_injective (by decide : 2≤2) he
      rw [Representation.CyclicFixedRank.commutator_eq_range] at hd
      exact hd
    obtain ⟨x,hx,hi,w,hw⟩ := exists_three_core_inverted_mover W.toRepresentation
      h.twoCore (normalFixed_fitting_moved ρ Y h.twoCore hmoved) t
      (by simpa only [pow_two] using hti.2)
      (h.complement_central hfive (mem_top t)) hr
    refine ⟨x,hx,hi,Multiplicative.ofAdd (w:V),w.property,?_⟩
    intro he
    apply hw
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd he
end CFSG.Quasithin.ChapterD.CyclicSource
