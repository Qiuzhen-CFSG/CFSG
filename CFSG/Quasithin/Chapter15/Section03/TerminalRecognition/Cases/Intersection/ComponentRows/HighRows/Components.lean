module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Actions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Permutation
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Orders

/-!
# The actual components in the two degree-three rows

The wreathed Sylow in F.6.18(10) has order 32. In (11), the
outside graph involution gives index exactly two above F*, while the
specified Sylow has order 64. Thus in both rows the component order has
two-part 32. The B.5.6 component sieve identifies it with G₂(2)′.

The equivalence between offender F* and ambient F* uses the proved
subgroup equality and their literal inclusions. The full B.5.1 witness is
retained as input. This reduction neither equates the actors nor identifies
the ambient graph extension by order alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6, printed p.105, F.6.18(10)–(11), pp.309–310,
and the final proof of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace ComponentRows.HighRows
universe u

private theorem degreeThree_comap {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) {p : ℕ} (h : FSource.DegreeThree p B) : FSource.DegreeThree p A := by
  cases h with
  | linear F hc hs f => exact .linear F hc hs (e.trans f)
  | projectiveLinear F hc hs f => exact .projectiveLinear F hc hs (e.trans f)
  | unitary F J hc hf hs f => exact .unitary F J hc hf hs (e.trans f)
  | projectiveUnitary F J hc hf hs f => exact .projectiveUnitary F J hc hf hs (e.trans f)

/-- The source's outside involution gives index exactly two, not only a two-group quotient. -/
theorem graphRow_index {D : Type*} [Group D] [Finite D]
    (r : FSource.GraphExtensionRow (D := D)) : (generalizedFitting D).index = 2 := by
  have hd : (generalizedFitting D).index ∣ 2 := by
    have h := (generalizedFitting D).relIndex_dvd_card (zpowers r.element)
    rw [← relIndex_sup_left, r.generated, relIndex_top_right, Nat.card_zpowers,
      r.involution] at h
    exact h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (r.outside (index_eq_one.mp h ▸ mem_top r.element)).elim
  · exact h

private theorem twoPart_of_sylow_card {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) {n : ℕ} (hS : Nat.card S = 2 ^ n) :
    (Nat.card D).factorization 2 = n := by
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) ((S.card_eq_multiplicity).symm.trans hS)

/-- The component of the graph row has two-part 32 under its literal
order-64 Sylow extension. -/
theorem graphRow_fitting_twoPart {D : Type*} [Group D] [Finite D]
    (r : FSource.GraphExtensionRow (D := D)) (S : Sylow 2 D)
    (hs : FSource.Extension S FSource.C4Square FSource.E4) :
    (Nat.card (generalizedFitting D)).factorization 2 = 5 := by
  have hS : Nat.card S = 2 ^ 6 := by
    rw [extension_card hs]
    norm_num [FSource.C4Square, FSource.E4, FSource.C, Nat.card_prod]
  have hD := twoPart_of_sylow_card S hS
  have hc := (generalizedFitting D).card_mul_index
  rw [graphRow_index r] at hc
  have hf := congrArg (fun n : ℕ => n.factorization 2) hc
  rw [Nat.factorization_mul Nat.card_pos.ne' (by decide), Finsupp.add_apply,
    show Nat.factorization 2 2 = 1 by decide +kernel, hD] at hf
  omega

end ComponentRows.HighRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- The canonical component equivalence induced by the original offender inclusion. -/
@[expose] noncomputable def offenderFittingEquiv
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    generalizedFitting d.offenderGroup ≃* generalizedFitting (coreQuotient H) :=
  (MulEquiv.subgroupCongr (d.offender_fitting_eq hL)).trans
    (subgroupOfEquivOfLe ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender))

/-- This equivalence preserves the literal ambient element. -/
theorem offenderFittingEquiv_apply
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (x : generalizedFitting d.offenderGroup) :
    (d.offenderFittingEquiv hL x : coreQuotient H) = (x : d.offenderGroup) := rfl

/-- The degree-three full-component row has the actual G₂(2)′ model.
The full-group action exclusion remains a separate step. -/
theorem component_row_ten_derived
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (hdegree : FSource.DegreeThree p (coreQuotient H))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* FSource.W32)) :
    Nonempty (coreQuotient H ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨s⟩ := hs
  have hS : Nat.card d.quotientSylow = 2 ^ 5 := by
    rw [Nat.card_congr s.toEquiv, RegularWreathProduct.card]
    norm_num [FSource.C]
  have hD := ComponentRows.HighRows.twoPart_of_sylow_card d.quotientSylow hS
  let f : generalizedFitting d.offenderGroup ≃* coreQuotient H :=
    (d.offenderFittingEquiv hL).trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
  have hpL : (Nat.card (generalizedFitting d.offenderGroup)).factorization 2 = 5 := by
    rw [Nat.card_congr f.toEquiv, hD]
  obtain ⟨g⟩ := ComponentRows.HighRows.degreeThree_model_of_twoPart_five hp (by omega)
    (ComponentRows.HighRows.degreeThree_comap f hdegree) hpL (c.fittingModel d.offenderAction)
  exact ⟨f.symm.trans g⟩

/-- The graph row's component is G₂(2)′. No conclusion about the full
graph extension or the Thompson image is inferred from this comparison. -/
theorem component_row_eleven_derived
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.GraphExtensionRow (D := coreQuotient H))
    (hs : FSource.Extension d.quotientSylow FSource.C4Square FSource.E4) :
    Nonempty (generalizedFitting (coreQuotient H) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) := by
  let f := d.offenderFittingEquiv hL
  have hpL : (Nat.card (generalizedFitting d.offenderGroup)).factorization 2 = 5 := by
    rw [Nat.card_congr f.toEquiv]
    exact ComponentRows.HighRows.graphRow_fitting_twoPart r d.quotientSylow hs
  obtain ⟨g⟩ := ComponentRows.HighRows.degreeThree_model_of_twoPart_five r.prime_isPrime
    (by have h := r.congruence; omega)
    (ComponentRows.HighRows.degreeThree_comap f r.model.model) hpL (c.fittingModel d.offenderAction)
  exact ⟨f.symm.trans g⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
