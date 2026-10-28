module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Basic

/-!
# Centralizer circles and their solvable traces

Two-centrality supplies a distinguished involution commuting with every
involution in `M`. Thus every noncontained involution centralizer meets the
local hypotheses. The solvable alternative makes its distinguished trace
a singleton, giving one of the two cardinalities in the parity argument.

Source: GLS, Volume 4, Chapter 2, Corollary 7.14, first paragraph of the proof.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Two-centrality gives a distinguished involution in each involution
centralizer in `M`. -/
public theorem exists_distinguished_commuting_in_M
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : IsInvolution v) (hvM : v ∈ M) :
    ∃ z ∈ Z, z ∈ M ∧ Commute z v := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  obtain ⟨S, _, hSc⟩ := r.two_central z hz
  have hSM : (S : Subgroup G) ≤ M := by
    intro s hs
    exact mem_of_commute h hz hzM (hSc ⟨s, hs⟩)
  let vM : M := ⟨v, hvM⟩
  obtain ⟨T, hT⟩ := (isPGroup_zpowers_of_involution (IsInvolution.subtype hv hvM)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M T (S.subtype hSM)
  have hvT : vM ∈ T := hT (Subgroup.mem_zpowers vM)
  have hvS : MulAut.conj m vM ∈ (S.subtype hSM : Subgroup M) := by
    rw [← hm]
    exact Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hvT
  let w : G := MulAut.conj (m : G)⁻¹ z
  refine ⟨w, h.invariant (m : G)⁻¹ z hz, ?_, ?_⟩
  · simpa only [w, MulAut.conj_apply, inv_inv] using
      M.mul_mem (M.mul_mem (M.inv_mem m.property) hzM) m.property
  · have hc := (hSc ⟨_, hvS⟩).map (MulAut.conj (m : G)⁻¹).toMonoidHom
    simpa [w, vM, MulAut.conj_apply, mul_assoc] using hc

/-- The noncontainment assertion of Corollary 7.14 for the ambient circle. -/
public theorem centralizerClosure_not_le
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ Subgroup.centralizer ({v} : Set G) ≤ M) :
    ¬ centralizerClosure Z v ≤ M := by
  obtain ⟨z, hz, hzM, hzc⟩ := exists_distinguished_commuting_in_M h r hv hvM
  rw [centralizerClosure_eq_map]
  exact localCircleIn_not_le h _ hC
    ⟨z, hz, Subgroup.mem_centralizer_singleton_iff.mpr hzc.eq, hzM⟩

/-- Properness, relative noncontainment, and local embedding, retaining
the exact internal circle needed by the Section 16 consumer. -/
public theorem involution_centralizer_local_data
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ Subgroup.centralizer ({v} : Set G) ≤ M) :
    let F := Subgroup.centralizer ({v} : Set G)
    F ≠ ⊤ ∧ ¬ localCircle Z F ≤ M.comap F.subtype ∧
      IsStronglyEmbedded (M.comap (localCircleHom Z F)) := by
  let F := Subgroup.centralizer ({v} : Set G)
  obtain ⟨z, hz, hzM, hzc⟩ := exists_distinguished_commuting_in_M h r hv hvM
  have hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M :=
    ⟨z, hz, Subgroup.mem_centralizer_singleton_iff.mpr hzc.eq, hzM⟩
  have hF := r.involution_centralizer_ne_top h hv
  exact ⟨hF, local_closure_not_le h F hC hne, r.local_embedding F hF hC hne⟩

/-- The solvable centralizer circle has exactly one distinguished involution
commuting with `v` in `M`, the first cardinality in Corollary 7.14. -/
public theorem residualCentralizerTrace_ncard_eq_one_of_solvable
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ Subgroup.centralizer ({v} : Set G) ≤ M)
    (hsol : Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v} : Set G)))) :
    (residualCentralizerTrace Z M v).ncard = 1 := by
  let F := Subgroup.centralizer ({v} : Set G)
  obtain ⟨w, hw, hwM, hwc⟩ := exists_distinguished_commuting_in_M h r hv hvM
  obtain ⟨z, hz, hzF, hzM, hunique, _⟩ := localCircle_solvable_alternative h r ha F
    (r.involution_centralizer_ne_top h hv) hC
    ⟨w, hw, Subgroup.mem_centralizer_singleton_iff.mpr hwc.eq, hwM⟩ hsol
  apply Set.ncard_eq_one.mpr
  refine ⟨z, ?_⟩
  ext x
  constructor
  · rintro ⟨hxZ, hxM, hxc⟩
    exact hunique x hxZ (Subgroup.mem_centralizer_singleton_iff.mpr hxc.eq) hxM
  · rintro rfl
    exact ⟨hz, hzM, Subgroup.mem_centralizer_singleton_iff.mp hzF⟩

end BenderSuzuki.ZD
