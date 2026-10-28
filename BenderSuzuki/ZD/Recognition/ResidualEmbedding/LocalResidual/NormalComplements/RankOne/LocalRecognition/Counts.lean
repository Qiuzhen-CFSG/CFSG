module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Model
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Centralizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Counts.Models

/-!
# Nonsolvable distinguished centralizer counts

All involutions of the distinguished circle are distinguished. This identifies
the ambient trace with the involutions in the circle's intersection with `M`.
The nonsolvable recognition theorem makes its image a Borel of an actual
simple Bender quotient. The odd core is central and lies in the intersection,
so quotienting preserves its involution count. The three concrete model
counts therefore give `2^n - 1` for some `n ≥ 2`.

Source: GLS, Volume 4, Chapter 2, Corollary 7.14, using Chapter 4,
Lemma 3.2(b). The simultaneous-solvability argument remains in the parent.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The literal ambient distinguished trace counts exactly the involutions
in the circle's intersection with `M`. -/
public theorem residualCentralizerTrace_ncard_eq_circle_involution_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ Subgroup.centralizer ({v} : Set G) ≤ M) :
    (residualCentralizerTrace Z M v).ncard =
      Nat.card {x : M.comap (localCircleHom Z (Subgroup.centralizer ({v} : Set G))) //
        IsInvolution x} := by
  let F := Subgroup.centralizer ({v} : Set G)
  let C := localCircle Z F
  let Y := M.comap (localCircleHom Z F)
  obtain ⟨z, hz, hzM, hzc⟩ := exists_distinguished_commuting_in_M h r hv hvM
  have hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M :=
    ⟨z, hz, Subgroup.mem_centralizer_singleton_iff.mpr hzc.eq, hzM⟩
  have hF := r.involution_centralizer_ne_top h hv
  let f : {x : Y // IsInvolution x} → residualCentralizerTrace Z M v := fun x =>
    ⟨localCircleHom Z F x.val.val, by
      have hxi : IsInvolution x.val.val :=
        ⟨fun he => x.property.1 (Subtype.ext he), congrArg Subtype.val x.property.2⟩
      exact ⟨localCircle_involution_mem h r F hF hC hne hxi, x.val.property,
        Subgroup.mem_centralizer_singleton_iff.mp x.val.val.val.property⟩⟩
  rw [← Nat.card_coe_set_eq]
  apply (Nat.card_congr (Equiv.ofBijective f ?_)).symm
  constructor
  · intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact localCircleHom_injective Z F
      (congrArg (fun z : residualCentralizerTrace Z M v => z.val) he)
  · intro x
    have hxF : x.val ∈ F :=
      Subgroup.mem_centralizer_singleton_iff.mpr x.property.2.2.eq
    let xF : F := ⟨x.val, hxF⟩
    have hxC : xF ∈ C := Subgroup.subset_closure x.property.1
    let xC : C := ⟨xF, hxC⟩
    have hxY : xC ∈ Y := x.property.2.1
    have hxi := IsInvolution.subtype
      (IsInvolution.subtype (IsInvolution.subtype (h.involutions x.val x.property.1) hxF) hxC) hxY
    exact ⟨⟨⟨xC, hxY⟩, hxi⟩, rfl⟩


/-- The nonsolvable centralizer-circle count in the proof of Corollary 7.14.
No model-count or lifting hypothesis remains: recognition supplies the actual
Borel, and its central odd kernel gives a bijection on involutions. -/
public theorem residualCentralizerTrace_ncard_eq_two_pow_sub_one_of_nonsolvable
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v : G} (hv : IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ Subgroup.centralizer ({v} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v} : Set G)))) :
    ∃ n : ℕ, 2 ≤ n ∧ (residualCentralizerTrace Z M v).ncard = 2 ^ n - 1 := by
  let F := Subgroup.centralizer ({v} : Set G)
  let C := localCircle Z F
  let Y := M.comap (localCircleHom Z F)
  obtain ⟨z, hz, hzM, hzc⟩ := exists_distinguished_commuting_in_M h.disconnected r hv hvM
  have hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M :=
    ⟨z, hz, Subgroup.mem_centralizer_singleton_iff.mpr hzc.eq, hzM⟩
  have hF := r.involution_centralizer_ne_top h.disconnected hv
  obtain ⟨hc, _, hmodel, hB⟩ := localCircle_nonsolvable_structure h r ha F hF hC hne hns
  let q := QuotientGroup.mk' (Subgroup.center C)
  obtain ⟨n, hn, hcount⟩ := bender_borel_involution_card hmodel hB
  have hodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk', ← hc]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hker : q.ker ≤ Y := by
    rw [QuotientGroup.ker_mk', ← hc]
    exact localCircle_oddCore_le h.disconnected r F hF hC hne hns
  refine ⟨n, hn, ?_⟩
  rw [residualCentralizerTrace_ncard_eq_circle_involution_card h.disconnected r hv hvM hC]
  exact (involution_card_map_of_central_odd_kernel q
    (QuotientGroup.mk'_surjective _) hodd (by rw [QuotientGroup.ker_mk']) Y hker).trans hcount

end BenderSuzuki.ZD
