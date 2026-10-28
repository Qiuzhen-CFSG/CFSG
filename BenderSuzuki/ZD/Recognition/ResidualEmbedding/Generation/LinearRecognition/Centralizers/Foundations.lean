module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion

/-!
# Proper centralizers in the residual ZD argument

Fusion control proves that an involution in the two-point stabilizer has a
centralizer outside `M`. Two-centrality supplies a distinguished involution
in its intersection with `M`; local embedding then applies to its actual
distinguished closure. In particular the involutions in that closure are
exactly its distinguished elements, and the original involution is outside
it. The closure is normal only inside the centralizer.

These are the setup and clause (a) of GLS4, Chapter 2, Lemma 12.4. The
containment `L ≤ Lᵤ`, the model alternatives, shearing, and the numerical
counts require the subsequent source analysis. The nonidentity-centralizer
bridge at the end also supplies the opening containment of Lemma 12.3.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.3–12.4; the local
embedding argument is Lemma 4.4. The two-centrality transport also appears
in `LocalResidual/NormalComplements/RankOne/LocalRecognition/Centralizers`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Lemma 12.4(a), from fusion control and the literal two-point stabilizer.
The swapping element need not itself be an involution for this implication. -/
public theorem pair_involution_centralizer_not_le
    (r : SimpleReduction Z M) {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    ¬ centralizer ({v} : Set G) ≤ M := by
  intro hc
  obtain ⟨S, hSM, hf⟩ := r.fusion
  apply htM
  apply involution_transporter_mem S hSM hf hv hvD.1 hc
  have hg : v ∈ rightConjugate M t := hvD.2
  rw [rightConjugate, Subgroup.conjBy, mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  simpa [MulAut.conj_apply, mul_assoc] using hx

private theorem nonidentity_centralizer_ne_top
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : v ≠ 1) : centralizer ({v} : Set G) ≠ ⊤ := by
  intro hc
  have hvc : v ∈ center G := centralizer_eq_top_iff_subset.mp hc (Set.mem_singleton v)
  rcases r.simple.eq_bot_or_eq_top_of_normal (center G) inferInstance with hbot | htop
  · exact hv (mem_bot.mp (hbot ▸ hvc))
  · obtain ⟨z, hz, hzM⟩ := h.nonempty
    have hzC : z ∈ center G := htop ▸ mem_top z
    apply h.proper
    apply top_le_iff.mp
    intro x _
    exact h.centralizer_le hz hzM (mem_centralizer_singleton_iff.mpr
      (mem_center_iff.mp hzC x))

private theorem distinguished_commuting_in_M
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M) :
    ∃ w ∈ Z, w ∈ M ∧ Commute w v := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  obtain ⟨S, _, hSc⟩ := r.two_central z hz
  have hSM : (S : Subgroup G) ≤ M := fun s hs =>
    mem_of_commute h hz hzM (hSc ⟨s, hs⟩)
  have ho : orderOf (⟨v, hvM⟩ : M) = 2 ^ 1 := by
    rw [← Subgroup.orderOf_coe]
    simpa using orderOf_eq_prime hv.sq_eq_one hv.ne_one
  obtain ⟨a, ha⟩ := (S.subtype hSM).exists_isConj_of_orderOf_eq_prime_pow ho
  obtain ⟨m, hm⟩ := isConj_iff.mp ha
  have hm' : MulAut.conj (m : G) v = ((a : M) : G) := congrArg Subtype.val hm
  refine ⟨MulAut.conj (m : G)⁻¹ z, h.invariant _ _ hz, ?_, ?_⟩
  · simpa only [MulAut.conj_apply, inv_inv] using
      M.mul_mem (M.mul_mem (M.inv_mem m.property) hzM) m.property
  · have hc0 : Commute z ((a : M) : G) := hSc ⟨_, a.property⟩
    rw [← hm'] at hc0
    have hc := hc0.map (MulAut.conj (m : G)⁻¹).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using hc

omit [Finite G] in
/-- Taking distinguished closure twice leaves the same ambient subgroup. -/
public theorem centralizerClosure_distinguished_generation (v : G) :
    closure (Z ∩ (centralizerClosure Z v : Set G)) = centralizerClosure Z v := by
  apply le_antisymm ((closure_le _).mpr fun _ hx => hx.2)
  apply Subgroup.closure_mono
  intro x hx
  exact ⟨hx.1, subset_closure hx⟩

omit [Finite G] in
/-- Internal distinguished generation of the centralizer closure. -/
public theorem centralizerClosure_local_generation (v : G) :
    closure ((centralizerClosure Z v).subtype ⁻¹' Z) = ⊤ := by
  let F := centralizerClosure Z v
  apply top_unique
  intro x _
  have hx : (x : G) ∈
      (closure (F.subtype ⁻¹' Z)).map F.subtype := by
    have hle : F ≤ (closure (F.subtype ⁻¹' Z)).map F.subtype := by
      apply (centralizerClosure_distinguished_generation (Z := Z) v).ge.trans
      apply (closure_le _).mpr
      intro y hy
      exact ⟨⟨y, hy.2⟩, subset_closure hy.1, rfl⟩
    exact hle x.property
  obtain ⟨y, hy, he⟩ := hx
  exact (Subtype.ext he : y = x) ▸ hy

omit [Finite G] in
/-- Relative normality of the distinguished closure inside its centralizer. -/
public theorem centralizerClosure_normal_in_centralizer
    (h : IsProductDisconnected Z M) (v : G) :
    ((centralizerClosure Z v).subgroupOf (centralizer ({v} : Set G))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨h.invariant g x hx.1,
    (centralizer ({v} : Set G)).mul_mem
      ((centralizer ({v} : Set G)).mul_mem hg hx.2)
      ((centralizer ({v} : Set G)).inv_mem hg)⟩

omit [Finite G] in
/-- The distinguished centralizer closure is generated by its own involutions. -/
public theorem centralizerClosure_involutionCore_eq_top
    (h : IsProductDisconnected Z M) (v : G) :
    involutionCore (centralizerClosure Z v) = ⊤ := by
  apply top_unique
  rw [← centralizerClosure_local_generation (Z := Z) v, involutionCore_eq_closure]
  apply Subgroup.closure_mono
  intro x hx
  exact IsInvolution.subtype (h.involutions x hx) x.property

private theorem stronglyEmbedded_from_top_comap {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) (hs : IsStronglyEmbedded (N.comap (⊤ : Subgroup H).subtype)) :
    IsStronglyEmbedded N := by
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    exact hs.ne_top (by rw [hn, comap_top])
  · obtain ⟨x, hx, hxi⟩ := hs.exists_involution
    exact ⟨x, hx, IsInvolution.map_of_injective hxi
      (⊤ : Subgroup H).subtype Subtype.val_injective⟩
  · intro g hg x hx hxg hxi
    let g' : (⊤ : Subgroup H) := ⟨g, mem_top _⟩
    let x' : (⊤ : Subgroup H) := ⟨x, mem_top _⟩
    have hxg' : x' ∈ rightConjugate (N.comap (⊤ : Subgroup H).subtype) g' := by
      rw [rightConjugate, Subgroup.conjBy, mem_map] at hxg ⊢
      obtain ⟨y, hy, he⟩ := hxg
      exact ⟨⟨y, mem_top _⟩, hy, Subtype.ext he⟩
    exact hs.2.2 (g := g') hg (x := x') hx hxg' (IsInvolution.subtype hxi _)

/-- Local embedding in the ambient distinguished centralizer closure.
All normality and embedding statements concern the proper local group. -/
public theorem pair_involution_centralizerClosure_local
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    centralizerClosure Z v ≠ ⊤ ∧ ¬ centralizerClosure Z v ≤ M ∧
      IsStronglyEmbedded (M.comap (centralizerClosure Z v).subtype) := by
  have hc := pair_involution_centralizer_not_le r htM hvD hv
  obtain ⟨w, hw, hwM, hwc⟩ := distinguished_commuting_in_M h r hv hvD.1
  have hwF : w ∈ centralizerClosure Z v := mem_centralizerClosure hw hwc
  have hF : centralizerClosure Z v ≠ ⊤ := fun he =>
    nonidentity_centralizer_ne_top h r hv.ne_one
      (top_le_iff.mp (he ▸ centralizerClosure_le Z v))
  have hFM : ¬ centralizerClosure Z v ≤ M := by
    rw [centralizerClosure_eq_map, map_le_iff_le_comap]
    exact local_closure_not_le h _ hc
      ⟨w, hw, mem_centralizer_singleton_iff.mpr hwc.eq, hwM⟩
  have hs := r.local_embedding (centralizerClosure Z v) hF hFM ⟨w, hw, hwF, hwM⟩
  rw [centralizerClosure_local_generation] at hs
  exact ⟨hF, hFM, stronglyEmbedded_from_top_comap _ hs⟩

/-- Every involution of `Lᵥ` is distinguished. This does not replace `Lᵥ`
by the full involution core of `C_G(v)`. -/
public theorem pair_involution_centralizerClosure_involutions
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    {x : G} (hx : x ∈ centralizerClosure Z v) : PFAppendixIII.IsInvolution x ↔ x ∈ Z := by
  refine ⟨?_, h.involutions x⟩
  intro hi
  obtain ⟨w, hw, _, hwc⟩ := distinguished_commuting_in_M h r hv hvD.1
  have hwF := mem_centralizerClosure hw hwc
  have hs := (pair_involution_centralizerClosure_local h r htM hvD hv).2.2
  obtain ⟨g, hg⟩ := hs.involutions_conjugate
    (IsInvolution.subtype (h.involutions w hw) hwF) (IsInvolution.subtype hi hx)
  have hg' : MulAut.conj ((g : G)⁻¹) w = x := by
    simpa only [rightConjugateElem, MulAut.conj_apply, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hg
  exact hg' ▸ h.invariant _ _ hw

/-- The original involution lies outside its distinguished centralizer closure. -/
public theorem pair_involution_not_mem_centralizerClosure
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    v ∉ centralizerClosure Z v := by
  intro hvF
  exact not_mem_Z_of_mem_residualPairStabilizer h htM hvD
    ((pair_involution_centralizerClosure_involutions h r htM hvD hv hvF).mp hv)

omit [Finite G] in
/-- The opening containment of Lemma 12.3, using distinguished generation of `L`. -/
public theorem residualGenerated_le_centralizerClosure_of_centralizes
    (h : IsProductDisconnected Z M) {z t v : G} (hz : z ∈ Z) (ht : t ∈ Z)
    (hv : v ∈ centralizer (residualGenerated M z t : Set G)) :
    residualGenerated M z t ≤ centralizerClosure Z v := by
  rw [← closure_Z_inter_residualGenerated h hz ht]
  apply (closure_le _).mpr
  intro x hx
  apply mem_centralizerClosure hx.1
  exact (mem_centralizer_iff.mp hv x hx.2)

/-- The distinguished trace in `C_M(v)` is the full fixed subgroup of
`A = ⟨Z ∩ M⟩`. This justifies the equality defining `qᵥ` before Lemma 12.4. -/
public theorem proper_distinguished_centralizer_trace
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) (v : G) :
    closure (Z ∩ ((M ⊓ centralizer ({v} : Set G) : Subgroup G) : Set G)) =
      closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) := by
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    exact ⟨subset_closure ⟨hx.1, hx.2.1⟩, hx.2.2⟩
  · intro x hx
    by_cases he : x = 1
    · subst x
      exact one_mem _
    · have hxZM : x ∈ Z ∩ (M : Set G) := by
        rw [hZ]
        exact ⟨hx.1, he⟩
      exact subset_closure ⟨hxZM.1, hxZM.2, hx.2⟩

end BenderSuzuki.ZD
