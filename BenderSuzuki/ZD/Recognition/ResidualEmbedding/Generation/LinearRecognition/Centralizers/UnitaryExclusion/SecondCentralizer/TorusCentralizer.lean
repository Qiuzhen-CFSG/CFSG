module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.TorusCentralizer.ResidualRoot
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.TorusCentralizer.Centralization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.TorusCentralizer.IntrinsicCentralizer

/-!
# The centralizer of the actual ambient fixed unitary torus

The literal torus `Lᵤ ∩ D ∩ C_G(t)` centralizes the residual subgroup L.
The proof identifies L with the image of the local root-generated PSL₂,
and transports the norm-one matrix calculation through the same local
unitary model and inclusion into G. Neither centralization nor that
embedded root identification is an assumption.

Consequently `L ⊔ B ≤ Lᵤ ∩ C_G(B)`. The intrinsic matrix upper bound
`C(B) ≤ rootGenerated ⊔ B`, applied inside Lᵤ, gives the reverse inclusion.
The final theorem proves the literal ambient equality from the supplied
source context, with no additional centralizer or geometric premise.

Source: GLS4, Chapter 2, the paragraph preceding Lemma 13.2, using
Chapter 4, Lemmas 3.2(h), 3.5(d), and 3.6(d). Both SU₃ and PSU₃ covers
retain matrix-field order (2ⁿ)² and fixed-field order 2ⁿ.
-/

namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory RankOneModelGeometry
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t u : G} {n : ℕ}

private theorem unitaryCover_fixed_centralizes_root
    (hc : IsUnitaryCentralizerCoverAt n G) (hn : 2 ≤ n)
    (P : Sylow 2 G) (t : G) (ht : PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set G)) :
    twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G) ≤
      centralizer (rootGenerated (P : Subgroup G) t : Set G) := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    exact UnitaryTorusCentralization.projective_of_equiv J hJ hn hcard hfixed e P t ht htB
  · obtain ⟨e⟩ := he
    exact UnitaryTorusCentralization.special_of_equiv J hJ hn hcard hfixed e P t ht htB

/-- The canonical ambient fixed torus centralizes the actual residual L.
The proof is independent of the full centralizer calculation. -/
public theorem ambientFixedTorus_centralizes_residualGenerated
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    ambientFixedTorus Z M t u ≤ centralizer (residualGenerated M z t : Set G) := by
  let F := centralizerClosure Z u
  have hLF := (hunitary u huD hu).1.le
  have htF : t ∈ F := hLF (mem_sup_left (mem_sup_right (mem_zpowers t)))
  obtain ⟨_, P, hP⟩ := pair_involution_unitary_borel h r htM huD hu hn (hunitary u huD hu).2
  change M.comap F.subtype = normalizer (P : Set F) at hP
  have hroot := residualGenerated_eq_unitary_root_map h hz hzM ht htM hn eL hLF
    (hunitary u huD hu).2 P hP
  have hC := unitaryCover_fixed_centralizes_root (hunitary u huD hu).2 hn P
    (⟨t, htF⟩ : F) (BenderSuzuki.IsInvolution.subtype (h.involutions t ht) htF)
    (by rw [← hP]; exact htM)
  intro b hb x hx
  rw [ambientFixedTorus_eq_map htF] at hb
  rw [hroot] at hx
  obtain ⟨b, hb, rfl⟩ := hb
  obtain ⟨x, hx, rfl⟩ := hx
  rw [hP] at hb
  exact congrArg F.subtype (hC hb x hx)

/-- The source product lies in the centralizer inside Lᵤ, with no additional
geometric assumption beyond the supplied unitary alternative. -/
public theorem residualGenerated_sup_torus_le_local_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    residualGenerated M z t ⊔ ambientFixedTorus Z M t u ≤
      centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) := by
  have hc := ambientFixedTorus_centralizes_residualGenerated h r hz hzM ht htM hn eL
    hunitary huD hu
  have : IsCyclic (ambientFixedTorus Z M t u) :=
    (ambientFixedTorus_cyclic_card h r ht htM hn hunitary huD hu).1
  let := IsCyclic.commGroup (α := ambientFixedTorus Z M t u)
  exact sup_le (le_inf (hunitary u huD hu).1.le (le_centralizer_iff.mp hc))
    (le_inf ambientFixedTorus_placement.1 (Subgroup.le_centralizer _))

/-- A conditional adapter for the intrinsic centralizer bound.
The root identification and reverse inclusion are proved here from the
source assumptions. The unconditional theorem below supplies the intrinsic
bound using the actual special or projective unitary cover. -/
public theorem ambientFixedTorus_centralizer_eq_of_root_bound
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hbound : ∀ (P : Sylow 2 (centralizerClosure Z u)) (s : centralizerClosure Z u),
      PFAppendixIII.IsInvolution s → s ∉ normalizer (P : Set (centralizerClosure Z u)) →
      let D := twoPoint (normalizer (P : Set (centralizerClosure Z u))) s
      centralizer (D ⊓ centralizer ({s} : Set (centralizerClosure Z u)) : Set (centralizerClosure Z u)) ≤
        rootGenerated (P : Subgroup (centralizerClosure Z u)) s ⊔
          (D ⊓ centralizer ({s} : Set (centralizerClosure Z u)))) :
    centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) =
      residualGenerated M z t ⊔ ambientFixedTorus Z M t u := by
  apply le_antisymm _ (residualGenerated_sup_torus_le_local_centralizer
    h r hz hzM ht htM hn eL hunitary huD hu)
  let F := centralizerClosure Z u
  have hLF := (hunitary u huD hu).1.le
  have htF : t ∈ F := hLF (mem_sup_left (mem_sup_right (mem_zpowers t)))
  let tF : F := ⟨t, htF⟩
  obtain ⟨_, P, hP⟩ := pair_involution_unitary_borel h r htM huD hu hn (hunitary u huD hu).2
  change M.comap F.subtype = normalizer (P : Set F) at hP
  have hroot := residualGenerated_eq_unitary_root_map h hz hzM ht htM hn eL hLF
    (hunitary u huD hu).2 P hP
  let C := twoPoint (normalizer (P : Set F)) tF ⊓ centralizer ({tF} : Set F)
  have hC : C.map F.subtype = ambientFixedTorus Z M t u := by
    rw [ambientFixedTorus_eq_map htF, hP]
  intro x hx
  have hxC : (⟨x, hx.1⟩ : F) ∈ centralizer (C : Set F) := by
    intro c hc
    apply Subtype.ext
    exact hx.2 c (hC ▸ mem_map_of_mem F.subtype hc)
  have hxR := hbound P tF (BenderSuzuki.IsInvolution.subtype (h.involutions t ht) htF)
    (by rw [← hP]; exact htM) hxC
  have hxmap := mem_map_of_mem F.subtype hxR
  rw [Subgroup.map_sup, ← hroot, hC] at hxmap
  exact hxmap

/-- The local centralizer identity preceding GLS4, Chapter 2, Lemma 13.2.
The torus is the literal ambient fixed torus and L is generated using
`[O₂′(D), t]`. Both unitary covers are handled by the intrinsic bound;
neither the root identification nor torus centralization is assumed.
For a minimal counterexample, apply this theorem to `h.disconnected`. -/
public theorem ambientFixedTorus_centralizer_eq
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) =
      residualGenerated M z t ⊔ ambientFixedTorus Z M t u := by
  apply ambientFixedTorus_centralizer_eq_of_root_bound h r hz hzM ht htM hn eL hunitary huD hu
  exact unitaryCover_fixed_torus_centralizer_le hn (hunitary u huD hu).2

end BenderSuzuki.ZD.UnitaryExclusion
