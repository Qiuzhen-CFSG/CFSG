module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.InvolutionPlacement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Frattini.OmegaProducts

/-!
# The literal Sylow census in Corollary 16.6

Intersect the selected centralizer Sylow with its normal distinguished circle.
The result is a Sylow of the circle, so the concrete models make its Omega
subgroup elementary. Strong embedding in the actual circle conjugates its
nonidentity root elements. Together with the involution placement theorem,
these facts discharge the earlier census inputs and give global involution
fusion and the four-group incidence assertion.

Source: GLS IV, Chapter 2, Corollary 16.6(a,c,d). Proposition 16.5 remains
an explicit preceding source premise until its independent proof is assembled.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The source circle Sylow is the literal intersection with the selected
Sylow of its local overgroup; Omega is transported through the same map. -/
public theorem source16_sylow_circle_intersection
    (h : IsProductDisconnected Z M) (B : Subgroup G) (hBM : ¬ B ≤ M)
    (hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M) (T : Sylow 2 B) :
    ∃ P : Sylow 2 (localCircle Z B),
      (P : Subgroup (localCircle Z B)).map (localCircleHom Z B) =
        (T : Subgroup B).map B.subtype ⊓ localCircleIn Z B ∧
      (omegaOneAmbient (P : Subgroup (localCircle Z B))).map (localCircleHom Z B) =
        omegaOneAmbient ((T : Subgroup B).map B.subtype ⊓ localCircleIn Z B) := by
  let C := localCircle Z B
  let : C.Normal := localCircle_normal h B hBM hne
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal C
  have he : (P : Subgroup C).map (localCircleHom Z B) =
      (T : Subgroup B).map B.subtype ⊓ localCircleIn Z B := by
    rw [localCircleHom, ← map_map, hP, subgroupOf_map_subtype,
      map_inf _ _ _ B.subtype_injective]
    rfl
  refine ⟨P,he,?_⟩
  rw [map_omegaOneAmbient_injective _ (localCircleHom_injective Z B), he]

/-- The actual root Omega has one nonidentity conjugacy class inside B.
Both elementarity and conjugacy are derived on the literal source maps. -/
public theorem source16_sylow_root_conjugacy
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u z : G} (ht : t ∈ Z) (htM : t ∉ M) (hu : PFAppendixIII.IsInvolution u)
    (huD : u ∈ residualPairStabilizer M t) (hz : z ∈ Z) (hzu : Commute z u)
    (T : Sylow 2 (centralizer ({u} : Set G))) :
    let B := centralizer ({u} : Set G)
    let Q := omegaOneAmbient ((T : Subgroup B).map B.subtype ⊓ localCircleIn Z B)
    _root_.IsElementaryAbelian 2 Q ∧
      ∀ q ∈ Q, q ≠ 1 → ∃ b ∈ B, MulAut.conj b q = z := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  let Q := omegaOneAmbient ((T : Subgroup B).map B.subtype ⊓ localCircleIn Z B)
  have hBM := residualInvolution_centralizer_not_le h.disconnected r ht htM hu huD
  obtain ⟨z₀,hz₀,hz₀M,hz₀u⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huD.1
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M :=
    ⟨z₀,hz₀,mem_centralizer_singleton_iff.mpr hz₀u.eq,hz₀M⟩
  obtain ⟨P,_,hQ⟩ := source16_sylow_circle_intersection h.disconnected B hBM hne T
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  obtain ⟨_,_,_,hgeom⟩ := involutionCentralizer_circle_models h r ha hu huD.1 hBM hns
  have hQE : _root_.IsElementaryAbelian 2 Q := by
    change _root_.IsElementaryAbelian 2 (omegaOneAmbient ((T : Subgroup B).map B.subtype ⊓ localCircleIn Z B))
    rw [← hQ]
    let := (hgeom P).2.1
    exact _root_.IsElementaryAbelian.map f
  refine ⟨hQE,?_⟩
  intro q hq hq1
  have hqL : q ∈ localCircleIn Z B := ((omegaOneAmbient_le _).trans inf_le_right) hq
  obtain ⟨qB,hqC,rfl⟩ := hqL
  let qC : C := ⟨qB,hqC⟩
  let zC : C := ⟨⟨z,mem_centralizer_singleton_iff.mpr hzu.eq⟩,subset_closure hz⟩
  let := hQE
  have hqi : PFAppendixIII.IsInvolution qC := by
    refine ⟨fun he => hq1 (congrArg f he), ?_⟩
    apply localCircleHom_injective Z B
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (f qC) hq
  have hzi : PFAppendixIII.IsInvolution zC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions z hz) _) _
  have hs : IsStronglyEmbedded (M.comap f) :=
    r.local_embedding B (r.involution_centralizer_ne_top h.disconnected hu) hBM hne
  obtain ⟨b,hb⟩ := hs.involutions_conjugate hqi hzi
  refine ⟨(f b)⁻¹, B.inv_mem b.val.property, ?_⟩
  have he := congrArg f hb
  simp only [rightConjugateElem,map_mul,map_inv] at he
  simpa only [MulAut.conj_apply,inv_inv,f,localCircleHom,
    MonoidHom.comp_apply,subtype_apply] using he

/-- Corollary 16.6(c,d), with the Omega and root-conjugacy premises
fully discharged. Only the genuine preceding rank-one proposition remains. -/
public theorem source16_fusion_and_four_of_pair_rank_one
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (T : Sylow 2 (centralizer ({u} : Set G)))
    (hTM : (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ M)
    (huT : u ∈ (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype) :
    IsConj u (u * z) ∧
      (∀ v : G, PFAppendixIII.IsInvolution v → v ∈ Z ∨ IsConj u v) ∧
      ∀ E : Subgroup G, Nat.card E = 4 → (∀ x : E, x ^ 2 = 1) →
        ∃ z ∈ E, z ∈ Z := by
  let B := centralizer ({u} : Set G)
  let T₁ := (T : Subgroup B).map B.subtype
  let Q := omegaOneAmbient (T₁ ⊓ localCircleIn Z B)
  have hQB : Q ≤ B := ((omegaOneAmbient_le _).trans inf_le_left).trans (map_subtype_le _)
  have hOmega := source16_omega_of_pair_rank_one h r ha hg hz hzM ht htM hu huD hzu htu
    hmax hrank T₁ (map_subtype_le _) hTM huT
  exact source16_global_classes_of_sylow_omega h.disconnected r ha htM huD hu hz hrank T Q hQB
    (by
      intro w hw
      rw [← hOmega]
      exact (omegaOneAmbient_le_iff T₁ (omegaOneAmbient T₁)).mp le_rfl ((w : B) : G)
        (mem_map_of_mem B.subtype w.property) hw.sq_eq_one)
    (source16_sylow_root_conjugacy h r ha ht htM hu huD hz hzu T).2

end BenderSuzuki.ZD
