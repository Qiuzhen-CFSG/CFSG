module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.RootQuotient.Models

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.RelativeCore

/-!
# The source unitary Frattini layer and full-torus quotient action

The actual unitary cover identifies a Sylow subgroup of Lᵤ with Hermitian
root coordinates. Its Frattini elements are exactly its square-one elements;
the distinguished-involution theorem identifies their ambient image with
A=⟨Z∩M⟩. The coordinate kernel is central, proving T≤C_G(A).

For irreducibility, the recognized local Borel gives the same literal Sylow
image T and two-point subgroup D∩Lᵤ. Pair normalization transports the full
torus calculation to these subgroups. No fixed-torus generation assertion is
used. The final theorem applies all three conclusions to the original setup.

Source: GLS4, Chapter 4, Lemma 3.5(a,c), and Chapter 2, Lemma 13.4,
lines 2397–2420.
-/

public section
noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory PFchapter1section1 PFAppendixIII RankOneModelGeometry
open MatrixGroups.HermitianForm.BinaryRootFrattini
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- In the literal source subgroup, the Frattini layer is the distinguished A,
and T centralizes it. Both unitary covers are retained. -/
theorem localT_frattini_and_centralizes
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    (frattini (localT Z M u)).map (localT Z M u).subtype = closure (Z ∩ (M : Set G)) ∧
      localT Z M u ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  obtain ⟨hAL, hMA, hA, hZ⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hAM : closure (Z ∩ (M : Set G)) ≤ M := (closure_le _).mpr fun _ hx => hx.2
  have hLH : residualGenerated M z t ≤ centralizerClosure Z u := d.intersection ▸ inf_le_right
  have hAT : closure (Z ∩ (M : Set G)) ≤ localT Z M u :=
    le_pCoreIn_of_normalizes hA (le_inf hAM (hAL.trans hLH)) (inf_le_left.trans hMA)
  obtain ⟨P, hP⟩ := sylow_T h.disconnected r htM huD hu hn hunitary
  let e := ((P : Subgroup (centralizerClosure Z u)).equivMapOfInjective
    (centralizerClosure Z u).subtype Subtype.val_injective).trans (MulEquiv.subgroupCongr hP)
  obtain ⟨hs, hc⟩ := frattini_structure_transport e
    (RootQuotient.cover_sylow_structure hn (hunitary u huD hu).2 P)
  have heq : (frattini (localT Z M u)).map (localT Z M u).subtype =
      closure (Z ∩ (M : Set G)) := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact (localT_involutions h.disconnected r htM huD hu hZ y).mpr ((hs y).mp hy)
    · intro x hx
      let y : localT Z M u := ⟨x, hAT hx⟩
      exact ⟨y, (hs y).mpr ((localT_involutions h.disconnected r htM huD hu hZ y).mp hx), rfl⟩
  refine ⟨heq, ?_⟩
  intro x hx a ha
  rw [← heq] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact congrArg Subtype.val ((mem_center_iff.mp (hc hb) (⟨x, hx⟩ : localT Z M u)).symm)

/-- The full literal D ∩ Lᵤ acts irreducibly on T/Φ(T). -/
theorem localPair_frattini_irreducible
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (W : Subgroup G) (hW : W ≤ localT Z M u)
    (hN : residualPairStabilizer M t ⊓ centralizerClosure Z u ≤ normalizer (W : Set G)) :
    W ≤ (frattini (localT Z M u)).map (localT Z M u).subtype ∨
      W ⊔ (frattini (localT Z M u)).map (localT Z M u).subtype = localT Z M u := by
  let H := centralizerClosure Z u
  have htH : t ∈ H := (hunitary u huD hu).1.le
    ((show zpowers t ≤ residualGenerated M z t from le_sup_right.trans le_sup_left)
      (mem_zpowers t))
  obtain ⟨_, P, hB⟩ := pair_involution_unitary_borel h r htM huD hu hn (hunitary u huD hu).2
  change M.comap H.subtype = normalizer (P : Set H) at hB
  have hP : (P : Subgroup H).map H.subtype = localT Z M u := by
    apply sylow_map_eq_pCoreIn_of_normalizer_map_eq P H.subtype H.subtype_injective (M ⊓ H)
    change (normalizer (P : Set H)).map H.subtype = _
    rw [← hB, map_comap_eq, range_subtype, inf_comm]
  let W' := W.comap H.subtype
  have hWH : W ≤ H := hW.trans ((localTwoCore_le _ _).trans inf_le_right)
  have hWmap : W'.map H.subtype = W := by
    rw [map_comap_eq, range_subtype, inf_eq_right.mpr hWH]
  have hWP : W' ≤ P := by
    intro x hx
    have hh : (x : G) ∈ (P : Subgroup H).map H.subtype := hP.symm ▸ hW hx
    obtain ⟨y, hy, he⟩ := hh
    exact (Subtype.ext he : y = x) ▸ hy
  have hDN : twoPoint (normalizer (P : Set H)) (⟨t, htH⟩ : H) ≤ normalizer (W' : Set H) := by
    rw [← hB]
    intro a ha
    have haD : (a : G) ∈ residualPairStabilizer M t ⊓ H := by
      rw [localPair_eq_map (M := M) htH]
      exact ⟨a, ha, rfl⟩
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hN haD) (x : G)
  have htB : (⟨t, htH⟩ : H) ∉ normalizer (P : Set H) := by
    rw [← hB]
    exact htM
  obtain hs | he := RootQuotient.cover_pair_invariant hn (hunitary u huD hu).2 P
    ⟨t, htH⟩ (IsInvolution.subtype (h.involutions t ht) htH) htB W' hWP hDN
  · left
    have hm := map_mono (f := H.subtype) hs
    rw [hWmap, map_map] at hm
    let e := ((P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
    have hp : (frattini P).map (H.subtype.comp (P : Subgroup H).subtype) =
        (frattini (localT Z M u)).map (localT Z M u).subtype := by
      rw [← frattini_map_equiv e, map_map]
      rfl
    rwa [hp] at hm
  · right
    have heq : W = localT Z M u := by rw [← hWmap, he, hP]
    rw [heq, sup_eq_left.mpr (map_subtype_le _)]

/-- The three root-quotient conclusions in the full Section 13 source setup.
The local, fusion, order and PSL₂ data are retained in this application; the
root calculation itself needs only the already recognized unitary covers. -/
theorem rootQuotient_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (_hlocal : ResidualCentralizerLocalData Z M z t)
    (_hshear : ResidualCentralizerShearing Z M t)
    (_hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w)
    (hn : 2 ≤ n) (_hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (_e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    (frattini (localT Z M u)).map (localT Z M u).subtype = closure (Z ∩ (M : Set G)) ∧
      localT Z M u ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) ∧
      ∀ W : Subgroup G, W ≤ localT Z M u →
        residualPairStabilizer M t ⊓ centralizerClosure Z u ≤ normalizer (W : Set G) →
        W ≤ (frattini (localT Z M u)).map (localT Z M u).subtype ∨
          W ⊔ (frattini (localT Z M u)).map (localT Z M u).subtype = localT Z M u := by
  obtain ⟨hPhi, hTA⟩ := localT_frattini_and_centralizes h r ha hz hzM ht htM hL heven
    hn hunitary huD hu d
  exact ⟨hPhi, hTA, localPair_frattini_irreducible h.disconnected r ht htM hn hunitary huD hu⟩

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
