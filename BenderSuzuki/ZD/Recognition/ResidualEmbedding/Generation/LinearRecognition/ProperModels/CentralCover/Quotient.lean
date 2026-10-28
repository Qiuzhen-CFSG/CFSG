module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import BenderSuzuki.SE.Final
public import BenderSuzuki.SE.Lemma312
public import BenderSuzuki.SE.Section11Lemma114Models

/-!
# The odd central cover of the proper residual subgroup

Involution generation and the odd-core containment from Foundations let strong
embedding descend to the simple odd-core quotient. Theorem SE identifies this
literal quotient and its Borel, without assuming strong embedding in the
ambient group. The residual is all of `L`, and its odd core is its center.
Consequently the checked odd-central-cover theorem lifts any PSL/Suzuki
quotient identification to an identification of `L` itself.

The unitary exclusion is separate: it must use the actual generators, not just
the existence of a Bender quotient. Source: GLS4, Chapter 2, Corollary 7.13 and
Lemma 12.2(a); Chapter 4, Lemma 2.8(a).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- SE recognizes the actual odd-core quotient and the image of the local
intersection as a Borel. -/
public theorem proper_residualGenerated_quotient_recognition
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    IsSimpleBenderGroup (residualGenerated M z t ⧸ twoPrimeCore (residualGenerated M z t)) ∧
      IsBorelSubgroup ((M.comap (residualGenerated M z t).subtype).map
        (QuotientGroup.mk' (twoPrimeCore (residualGenerated M z t)))) := by
  let L := residualGenerated M z t
  let N := twoPrimeCore L
  let B := M.comap L.subtype
  let q := QuotientGroup.mk' N
  let BQ := B.map q
  have hs : IsStronglyEmbedded B :=
    stronglyEmbedded_in_proper_residualGenerated h.disconnected r hz hzM ht htM hL
  have hgen : involutionCore L = ⊤ := involutionCore_residualGenerated_eq_top h.disconnected hz ht
  have hNB : N ≤ B := by
    intro x hx
    exact oddCore_le_of_distinguishedClosure_le h r L hAL (mem_map_of_mem L.subtype hx)
  have hodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsQ : IsStronglyEmbedded BQ := hs.map_quotient_of_odd_kernel hNB hodd
  have hsimple : IsSimpleGroup (L ⧸ N) := hs.isSimpleGroup_quotient_twoPrimeCore hgen
  have hgenQ : involutionCore (L ⧸ N) = ⊤ := hsQ.involutionCore_eq_top_of_isSimple hsimple
  have hrQ : TwoRankAtLeastTwo (L ⧸ N) := simpleStronglyEmbeddedRankTwo BQ hsimple hsQ
  let e : (L ⧸ N) ≃* involutionCore (L ⧸ N) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgenQ).symm
  have hr := hrQ.map_of_injective e.toMonoidHom e.injective
  exact recognition_borel_of_simple_theoremSEBenderConclusion BQ hsQ hsimple
    ((theorem_SE BQ hsQ).resolve_left (not_not.mpr hr))

/-- Distinguished involution generation makes `L` its own two-prime residual. -/
public theorem twoPrimeResidual_residualGenerated_eq_top
    (h : IsProductDisconnected Z M) {z t : G} (hz : z ∈ Z) (ht : t ∈ Z) :
    twoPrimeResidual (residualGenerated M z t) = ⊤ := by
  apply top_unique
  rw [← involutionCore_residualGenerated_eq_top h hz ht, involutionCore_eq_closure, closure_le]
  intro x hx
  exact isPGroup_le_twoPrimeResidual (isPGroup_two_zpowers_of_isInvolution hx) (mem_zpowers x)

/-- The odd core is the full center, with relative strong embedding used
only inside the proper residual subgroup. -/
public theorem proper_residualGenerated_oddCore_eq_center
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    twoPrimeCore (residualGenerated M z t) = center (residualGenerated M z t) := by
  apply le_antisymm
  · exact residualGenerated_oddCore_le_center_of_distinguishedClosure_le
      h r ha hz hzM ht htM hL hAL
  · have hs := stronglyEmbedded_in_proper_residualGenerated h.disconnected r hz hzM ht htM hL
    obtain ⟨x, hxB, hx⟩ := hs.exists_involution
    have hcB : center (residualGenerated M z t) ≤ M.comap (residualGenerated M z t).subtype := by
      intro y hy
      exact hs.centralizer_le hxB hx (mem_centralizer_singleton_iff.mpr
        (mem_center_iff.mp hy x).symm)
    exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr (hs.normal_le_card_odd hcB)⟩

/-- Once the unitary quotient has been excluded, the odd central kernel
vanishes and the quotient models lift to the source subgroup itself. -/
public theorem proper_residualGenerated_lift_quotient_models
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel :
      Nonempty ((residualGenerated M z t ⧸ twoPrimeCore (residualGenerated M z t)) ≃*
        MatrixGroups.PSL2BinaryMatrixGroup n) ∨
      ∃ m : ℕ, n = 2 * m + 1 ∧
        Nonempty ((residualGenerated M z t ⧸ twoPrimeCore (residualGenerated M z t)) ≃*
          MatrixGroups.SuzukiMatrixGroup m)) :
    Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
        Nonempty (residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m) := by
  have hlift := lemma114_model_psl_or_suzuki_of_model hn hmodel
    (twoPrimeResidual_residualGenerated_eq_top h.disconnected hz ht)
    (proper_residualGenerated_oddCore_eq_center h r ha hz hzM ht htM hL hAL)
  rcases hlift with hpsl | ⟨m, hnm, hm⟩
  · exact Or.inl hpsl
  · exact Or.inr ⟨m, by omega, hnm, hm⟩

end BenderSuzuki.ZD
