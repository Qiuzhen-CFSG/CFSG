module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.LocalAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Counts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Source

/-!
# The actual covering models at the Section 16 parameter

Proper-subgroup induction recognizes the central quotient of the distinguished
centralizer circle. Its Borel involution count identifies the exponent with
the original distinguished trace, so the odd central-cover theorem gives the
four concrete models at that same exponent. The original circle contains a
Sylow two-subgroup whose ambient image lies in M, by strong embedding.

Source: GLS IV, Chapter 2, Corollary 7.14, Lemma 16.3 and (17B). The source
nonsolvability and trace count remain explicit; no covering model is assumed.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Subgroup PFAppendixIII Theory.GroupTheory
open _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Strong embedding supplies the Sylow subgroup in the original ambient
circle and proves its image lies in M. -/
public theorem exists_sylow_in_centralizerClosure_le
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ centralizer ({v} : Set G) ≤ M) :
    ∃ P : Sylow 2 (centralizerClosure Z v),
      (P : Subgroup _).map (centralizerClosure Z v).subtype ≤ M := by
  let F := centralizer ({v} : Set G)
  let C := localCircle Z F
  let f : C →* centralizerClosure Z v :=
    { toFun := fun x => ⟨localCircleHom Z F x, by
        rw [centralizerClosure_eq_map]
        exact ⟨x.val, x.property, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    have hy := (le_of_eq (centralizerClosure_eq_map Z v)) y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨_, _, hs⟩ := involution_centralizer_local_data h r hv hvM hC
  obtain ⟨Q, hQ⟩ := hs.containsSylowTwo
  refine ⟨Q.mapSurjective (f := f) hf, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  change y ∈ (Q : Subgroup C).map f at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hQ hw

/-- The distinguished trace selects the exponent of the actual simple
central quotient. This prevents an unrelated model parameter from entering
Section 17's divisibility argument. -/
public theorem centralizerCircle_model_at_trace
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ centralizer ({v} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({v} : Set G))))
    {n : ℕ} (htrace : (residualCentralizerTrace Z M v).ncard = 2 ^ n - 1) :
    2 ≤ n ∧ IsSimpleBenderGroupAtExponent n
      (localCircle Z (centralizer ({v} : Set G)) ⧸
        center (localCircle Z (centralizer ({v} : Set G)))) := by
  let F := centralizer ({v} : Set G)
  let C := localCircle Z F
  let Y := M.comap (localCircleHom Z F)
  let q := QuotientGroup.mk' (center C)
  obtain ⟨z, hz, hzM, hzc⟩ := exists_distinguished_commuting_in_M h.disconnected r hv hvM
  have hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M :=
    ⟨z, hz, mem_centralizer_singleton_iff.mpr hzc.eq, hzM⟩
  have hF := r.involution_centralizer_ne_top h.disconnected hv
  obtain ⟨hc, _, hmodel, hB⟩ := localCircle_nonsolvable_structure h r ha F hF hC hne hns
  obtain ⟨k, hk, hm⟩ := hmodel.exists_exponent
  have hcount := bender_borel_involution_card_atExponent hk hm hB
  have hodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk', ← hc]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hker : q.ker ≤ Y := by
    rw [QuotientGroup.ker_mk', ← hc]
    exact localCircle_oddCore_le h.disconnected r F hF hC hne hns
  have hi := involution_card_map_of_central_odd_kernel q
    (QuotientGroup.mk'_surjective _) hodd (by rw [QuotientGroup.ker_mk']) Y hker
  have heq : 2 ^ n - 1 = 2 ^ k - 1 := htrace.symm.trans
    ((residualCentralizerTrace_ncard_eq_circle_involution_card h.disconnected r hv hvM hC).trans
      (hi.trans hcount))
  have hp : 2 ^ n = 2 ^ k := by
    have hn1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hnk := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
  exact hnk.symm ▸ ⟨hk, hm⟩

/-- All four actual covering models of the original ambient circle, with
Section 16's trace parameter retained. The unitary alternatives keep the
matrix-field and fixed-field cardinalities distinct. -/
public theorem centralizerClosure_models_at_trace
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ centralizer ({v} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({v} : Set G))))
    {n : ℕ} (htrace : (residualCentralizerTrace Z M v).ncard = 2 ^ n - 1) :
    Nonempty (centralizerClosure Z v ≃* PSL2BinaryMatrixGroup n) ∨
      (∃ m : ℕ, 1 ≤ m ∧ n = 2*m+1 ∧
        Nonempty (centralizerClosure Z v ≃* SuzukiMatrixGroup m)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
        Nat.card E = (2 ^ n)^2 ∧ Nat.card {x : E // J.conj x = x} = 2^n ∧
        (Nonempty (centralizerClosure Z v ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
         Nonempty (centralizerClosure Z v ≃* J.specialSubgroup))) := by
  let F := centralizer ({v} : Set G)
  let C := localCircle Z F
  obtain ⟨z, hz, hzM, hzc⟩ := exists_distinguished_commuting_in_M h.disconnected r hv hvM
  have hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M :=
    ⟨z, hz, mem_centralizer_singleton_iff.mpr hzc.eq, hzM⟩
  obtain ⟨hc, hp, _, _⟩ := localCircle_nonsolvable_structure h r ha F
    (r.involution_centralizer_ne_top h.disconnected hv) hC hne hns
  have hodd : Odd (Nat.card (center C)) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hn, hm⟩ := centralizerCircle_model_at_trace h r ha hv hvM hC hns htrace
  let e : centralizerClosure Z v ≃* C := (internalCentralizerClosureEquiv Z v).symm
  rcases RankOneModelGeometry.oddCentralCover_model_cases hn hp hodd hm with
    ⟨_, ⟨f⟩⟩ | ⟨_, m, hm, hnm, ⟨f⟩⟩ | ⟨E, hE, hfin, J, _, hcard, hfixed, hf⟩
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr (Or.inl ⟨m, hm, hnm, ⟨e.trans f⟩⟩)
  · refine Or.inr (Or.inr ⟨E, hE, hfin, J, hcard, hfixed, ?_⟩)
    rcases hf with ⟨_, ⟨f⟩⟩ | ⟨_, _, ⟨f⟩⟩
    · exact Or.inl ⟨e.trans f⟩
    · exact Or.inr ⟨e.trans f⟩

end BenderSuzuki.ZD.Section17
