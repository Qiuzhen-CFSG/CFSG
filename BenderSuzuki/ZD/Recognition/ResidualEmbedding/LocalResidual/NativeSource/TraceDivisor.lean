module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.Models

/-!
# The source degree divisor at the Section 17 trace parameter

The normal Sylow intersection supplies the actual circle Sylow. Its Omega
image is the distinguished circle of the selected two-subgroup. Recognition
at the trace parameter therefore identifies its order with trace plus one.
Transport the same Sylow through the literal circle equivalence to obtain
the divisor required by the Section 17 counting argument.

Source: GLS IV, Chapter 2, Lemma 16.4(c) and the notation (17B).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 RankOneModelGeometry
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The literal source 16.4(c) divisor supplies exactly the selected Sylow
and trace divisor consumed by the Section 17 source theorem. -/
public theorem source17_trace_divisor_of_selected_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u z : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (htu : Commute t u) (hz : z ∈ Z)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hSM : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ M)
    (huS : u ∈ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hzS : z ∈ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hSz : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ centralizer ({z} : Set G))
    (hcentral : ∃ SD : Sylow 2 (residualPairStabilizer M t),
      (SD : Subgroup (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype ≤ centralizer ({u} : Set G))
    (hconj : IsConj u (u * z)) :
    ∃ P : Sylow 2 (centralizerClosure Z u),
      ((residualCentralizerTrace Z M u).ncard + 1) * Nat.card P ∣
        Nat.card (G ⧸ M) - 1 := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  let T := (S : Subgroup B).map B.subtype
  have hTB : T ≤ B := map_subtype_le _
  have hBM := residualInvolution_centralizer_not_le h.disconnected r ht htM hu huD
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M := ⟨z,hz,hTB hzS,hSM hzS⟩
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  obtain ⟨P,hP,_⟩ := source16_sylow_circle_intersection h.disconnected B hBM hne S
  have hQ := source16_sylow_omega_map_eq_localCircle h.disconnected r B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM hne T hTB P hP
  obtain ⟨n,hn,htrace⟩ := residualCentralizerTrace_ncard_eq_two_pow_sub_one_of_nonsolvable
    h r ha hu huD.1 hBM hns
  have hm := (Section17.centralizerCircle_model_at_trace h r ha hu huD.1 hBM hns htrace).2
  obtain ⟨hc,hperfect,_,_⟩ := localCircle_nonsolvable_structure h r ha B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM hne hns
  have hodd : Odd (Nat.card (center C)) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  have hcardQ : Nat.card (localCircleIn Z T) = (residualCentralizerTrace Z M u).ncard + 1 := by
    rw [← hQ, card_map_of_injective (localCircleHom_injective Z B),
      (oddCentralCover_omega_geometry hn hperfect hodd hm P).2.2.1, htrace]
    have hp := Nat.one_le_two_pow (n := n)
    omega
  let e : C ≃* centralizerClosure Z u := Section17.internalCentralizerClosureEquiv Z u
  let P' : Sylow 2 (centralizerClosure Z u) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcardP : Nat.card P' = Nat.card (T ⊓ localCircleIn Z B : Subgroup G) := by
    change Nat.card ((P : Subgroup C).map e.toMonoidHom) = _
    rw [card_map_of_injective e.injective, ← hP, card_map_of_injective (localCircleHom_injective Z B)]
  have hd := source16_degree_divisibility h r ha ht htM hu huD htu hz S hSM huS hzS hSz
    hcentral hconj
  change Nat.card (localCircleIn Z T) * Nat.card (T ⊓ localCircleIn Z B : Subgroup G) ∣ _ at hd
  exact ⟨P', by rwa [hcardQ, ← hcardP] at hd⟩

end BenderSuzuki.ZD
