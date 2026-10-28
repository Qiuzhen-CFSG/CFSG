module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Selection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Source

/-!
# Literal centralizer-circle models in Section 16

Corollary 7.13 recognizes the central quotient of the distinguished circle.
The perfect odd-cover theorem then identifies the original circle itself,
including the SU₃ cover with its center of order three. The common exponent
also gives the exact omega subgroup, order and normalizer involution core.
The nonsolvability premise is discharged by the Section 16 source argument.

Source: GLS4, Chapter 2, Lemma 16.3(a), and Chapter 4, Lemmas 2.8 and 3.2.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups RankOneModelGeometry
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The actual four models for the original nonsolvable distinguished
centralizer circle, with one exponent governing its Sylow omega subgroups. -/
public theorem involutionCentralizer_circle_models
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {u : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hC : ¬ centralizer ({u} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G)))) :
    let C := localCircle Z (centralizer ({u} : Set G))
    ∃ n : ℕ, 2 ≤ n ∧
      ((center C = ⊥ ∧ Nonempty (C ≃* PSL2BinaryMatrixGroup n)) ∨
       (center C = ⊥ ∧ ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
         Nonempty (C ≃* SuzukiMatrixGroup m)) ∨
       (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
         J.form = !![0,0,1;0,1,0;1,0,0] ∧ Nat.card E = (2 ^ n) ^ 2 ∧
         Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
         ((center C = ⊥ ∧ Nonempty (C ≃* ProjectiveSpecialUnitaryMatrixGroup J)) ∨
          (Nat.card (center C) = 3 ∧ Odd n ∧ Nonempty (C ≃* J.specialSubgroup))))) ∧
      ∀ P : Sylow 2 C,
        omegaOneAmbient (P : Subgroup C) = (center P).map (P : Subgroup C).subtype ∧
        IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup C)) ∧
        Nat.card (omegaOneAmbient (P : Subgroup C)) = 2 ^ n ∧
        omegaOneAmbient (P : Subgroup C) =
          (involutionCore (normalizer (P : Set C))).map (normalizer (P : Set C)).subtype := by
  let F := centralizer ({u} : Set G)
  obtain ⟨z, hz, hzM, hzu⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huM
  obtain ⟨hc, hp, hm, _⟩ := localCircle_nonsolvable_structure h r ha F
    (r.involution_centralizer_ne_top h.disconnected hu) hC
    ⟨z, hz, mem_centralizer_singleton_iff.mpr hzu.eq, hzM⟩ hns
  obtain ⟨n, hn, hmodel⟩ := hm.exists_exponent
  have hodd : Odd (Nat.card (center (localCircle Z F))) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  exact ⟨n, hn, oddCentralCover_model_cases hn hp hodd hmodel,
    fun P => oddCentralCover_omega_geometry hn hp hodd hmodel P⟩

/-- Lemma 16.3(c), after one genuine nonsolvable escaping centralizer has
been obtained. Corollary 7.14 removes any additional solvability comparison. -/
public theorem involutionCentralizer_le_of_solvable_circle
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {u v : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hC : ¬ centralizer ({u} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))))
    (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M)
    (hsol : Group.IsSolvable (localCircle Z (centralizer ({v} : Set G)))) :
    centralizer ({v} : Set G) ≤ M := by
  by_contra hCv
  exact hns ((centralizerCircle_solvable_iff h r ha hu huM hC hv hvM hCv).mpr hsol)


/-- Lemma 16.3(b), retaining the original marked t and literal D.
Nonsolvability supplies double transitivity of the actual circle. -/
public theorem involutionCentralizer_twoPoint_factorization
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {u t : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (htu : Commute t u)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G)))) :
    let B := centralizer ({u} : Set G)
    (B : Set G) = (localCircleIn Z B : Set G) * (B ⊓ residualPairStabilizer M t : Subgroup G) := by
  let B := centralizer ({u} : Set G)
  have htB : t ∈ B := mem_centralizer_singleton_iff.mpr htu.eq
  have hBM : ¬ B ≤ M := fun hle => htM (hle htB)
  obtain ⟨z,hz,hzM,hzu⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huM
  have hmove : t • (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    intro he
    exact htM ((baseCoset_stabilizer M) ▸ (MulAction.mem_stabilizer_iff.mpr he))
  have hstab : MulAction.stabilizer G (t • (QuotientGroup.mk 1 : G ⧸ M)) = rightConjugate M t := by
    simpa [MulAction.Quotient.smul_mk, smul_eq_mul, (h.disconnected.involutions t ht).inv_eq_self]
      using conjugateCoset_stabilizer M t
  have hf := localCircle_twoPoint_factorization h r B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩ hns
    (show InOrbit B (QuotientGroup.mk 1) (t • (QuotientGroup.mk 1 : G ⧸ M)) from ⟨⟨t,htB⟩,rfl⟩) hmove
  simpa only [hstab, residualPairStabilizer, inf_assoc] using hf

end BenderSuzuki.ZD
