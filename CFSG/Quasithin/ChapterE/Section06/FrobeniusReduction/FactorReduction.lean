module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.ONan
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalGeometry
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction
public import Theory.Representation.RegularCyclicNormalClosure.Basic
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Reducing an E.6.3 obstruction to two exceptional factors

The actual E.6.13 implication forces an involution in the automizer whenever
Γ is nonempty: an odd automizer would make T centralize V and every subgroup
of V normal in T. Rank-nullity for that involution gives 2m ≤ dim(V).

A cyclic decomposition with at most two factors has dimension at most 2r,
contrary to r < m. A single exceptional summand has dimension three, contrary
to m > 2. Thus an obstruction under the E.6.3 hypotheses leaves exactly two
Frobenius factors. This sufficient reduction avoids identifying the whole
automizer in the single-factor branch. The existence of the decomposition
and the separately proved local factor-count theorem remain distinct inputs.

Source: Aschbacher–Smith, E.6.13 and E.6.24–25, printed pp.250,255–256
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open LocalFactors Representation.RegularCyclicNormalClosure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U X : Subgroup G}

/-- A genuine obstruction forces an involution in the actual automizer. -/
theorem automizer_involution_of_obstruction
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T)
    (hU : U ∈ obstructionFamily M V) : ∃ a : Automizer V, orderOf a = 2 := by
  by_contra hn
  have hodd : Odd (Nat.card (Automizer V)) := by
    by_contra hno
    exact hn (exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hno)))
  have hT := sylow_eq_centralizer_of_odd_automizer h hodd
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (hT.le.trans inf_le_right).trans
      ((Subgroup.centralizer_le hU.1).trans (Subgroup.centralizer_le_normalizer _))
  have hUn : (U.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hU.1.trans h.le_sylow)).mpr hTU
  exact hU.2.2.1 (InvariantSubspaces.centralizer_le_of_normal_in_sylow
    h h311 hU.2.1 hU.1 hU.2.2.2 hUn)

/-- The involution codimension gives the dimension bound for every obstruction. -/
theorem twice_localM_le_dimension_of_obstruction [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T)
    (hU : U ∈ obstructionFamily M V) :
    2 * localM V ≤ Module.finrank (ZMod 2) (Additive V) := by
  obtain ⟨a,ha⟩ := automizer_involution_of_obstruction h h311 hU
  have hm := moduleM_le_involution (automizerRepresentation V) ha
  have hd := (involution_actor_rank_and_fixedCodim (automizerRepresentation V) a ha).2.2.2
  change localM V ≤ _ at hm
  omega

/-- The cyclic alternative contradicts the original corank bound r < m. -/
theorem cyclic_decomposition_excluded [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hsmall : subgroupCorank V U < localM V)
    (D : Decomposition (automizerRepresentation V) (inducedAutomizer V X))
    (hcount : D.size ≤ 2)
    (hcyclic : inducedAutomizer V X = D.factor D.distinguished) : False := by
  have hXN := hX.contained.trans (inf_le_left.trans inf_le_right)
  have hnot := cyclic_decomposition_size_ne_one h hU hXN hX.fixed D hcyclic
  have hpos := D.positive
  have hsize : D.size = 2 := by omega
  let j := otherIndex hsize D.distinguished
  have hj := otherIndex_ne hsize D.distinguished
  have hsplit := two_summands_isCompl h hU hX D j hj
    (eq_or_otherIndex hsize D.distinguished)
  have hdist : Module.finrank (ZMod 2) (D.summand D.distinguished) ≤ subgroupCorank V U := by
    rw [← hX.moved_finrank hU.1]
    apply Submodule.finrank_mono
    rw [← D.self_moved D.distinguished, ← hcyclic]
    exact displacementSpan_mono (automizerRepresentation V) le_rfl le_top
  obtain ⟨a,_,ha⟩ := D.transitive D.distinguished j
  have hainj : Function.Injective (automizerRepresentation V a) := by
    intro x y he
    have hh := congrArg (automizerRepresentation V a⁻¹) he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh
  have hdim : Module.finrank (ZMod 2) (D.summand D.distinguished) =
      Module.finrank (ZMod 2) (D.summand j) := by
    rw [← ha]
    exact (Submodule.equivMapOfInjective (automizerRepresentation V a) hainj
      (D.summand D.distinguished)).finrank_eq
  have hsum := Submodule.finrank_add_eq_of_isCompl hsplit
  have hbound := twice_localM_le_dimension_of_obstruction h h311 hU
  omega

/-- A single exceptional summand is too small under the source hypothesis m > 2. -/
theorem exceptional_decomposition_size_ne_one [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hm : 2 < localM V)
    (D : Decomposition (automizerRepresentation V) (inducedAutomizer V X))
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3) : D.size ≠ 1 := by
  intro hs
  have : Subsingleton (Fin D.size) := by rw [hs]; infer_instance
  have htop : D.summand D.distinguished = ⊤ := by
    rw [← decomposition_spans h hU
      (hX.contained.trans (inf_le_left.trans inf_le_right)) hX.fixed D]
    apply le_antisymm (le_iSup _ D.distinguished)
    apply iSup_le
    intro i
    rw [Subsingleton.elim i D.distinguished]
  have hd := hdim D.distinguished
  rw [htop,finrank_top] at hd
  have hb := twice_localM_le_dimension_of_obstruction h h311 hU
  omega

/-- Only the two-factor exceptional alternative remains in an E.6.3 counterexample. -/
theorem exceptional_two_factor_of_counterexample [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hm : 2 < localM V) (hsmall : subgroupCorank V U < localM V)
    (D : Decomposition (automizerRepresentation V) (inducedAutomizer V X))
    (hcount : D.size ≤ 2) :
    D.size = 2 ∧ Nat.card (inducedAutomizer V X) = 3 ∧
      Nonempty (D.factor D.distinguished ≃* Frobenius21.Model) ∧
      normalClosure ((inducedAutomizer V X).subgroupOf
        (D.factor D.distinguished) : Set (D.factor D.distinguished)) = ⊤ ∧
      ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3 := by
  rcases D.alternatives with hc | he
  · exact (cyclic_decomposition_excluded h h311 hU hX hsmall D hcount hc).elim
  · have hnot := exceptional_decomposition_size_ne_one h h311 hU hX hm D he.2.2.2
    have hp := D.positive
    exact ⟨by omega,he⟩
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
