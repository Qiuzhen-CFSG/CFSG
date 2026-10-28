module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.LocalCore
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddContainment

/-!
# Rank and odd-core control for the proper residual subgroup

Write `A = ⟨Z ∩ M⟩`. Its normalizer is exactly `M`, so its normality is
relative to `M`, not to the ambient group. In a minimal ZD counterexample,
Z-star and the already proved ambient odd-core containment show that every
chosen distinguished involution in `M` has a distinct commuting distinguished
involution. These two elements give an elementary four in `A`.

Consequently every subgroup containing `A` has rank at least two in its
intersection with `M`, and its odd core lies in `M`: the four-group acts on
the odd core, and product disconnection controls its three centralizers.
For proper `L = residualGenerated M z t`, LocalCore then centralizes that
odd core. The premise `A ≤ L` remains explicit; the orbit-counting argument
of Lemma 3.10 must discharge it before Lemma 12.2 is assembled.

Source: GLS, Volume 4, Chapter 2, Lemmas 3.3, 3.10, 3.13, 4.5 and the
opening of the proof of Lemma 12.2, in `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open Subgroup
universe u
variable {G : Type u} [Group G] {Z : Set G} {M : Subgroup G}

/-- The distinguished closure in `M` is a subgroup of `M`. -/
public theorem distinguishedClosure_le : closure (Z ∩ (M : Set G)) ≤ M :=
  (closure_le _).mpr fun _ hx => hx.2

/-- The ambient normalizer of the distinguished closure is exactly `M`. -/
public theorem distinguishedClosure_normalizer (h : IsProductDisconnected Z M) :
    normalizer (closure (Z ∩ (M : Set G)) : Set G) = M := by
  apply le_antisymm
  · apply normalizer_le h distinguishedClosure_le
    obtain ⟨z, hz, hzM⟩ := h.nonempty
    exact ⟨z, hz, subset_closure ⟨hz, hzM⟩⟩
  · apply le_normalizer_closure_iff.mpr
    intro g hg z hz
    exact subset_closure ⟨h.invariant g z hz.1,
      M.mul_mem (M.mul_mem hg hz.2) (M.inv_mem hg)⟩

/-- The distinguished closure is normal inside `M`. -/
public theorem distinguishedClosure_normal (h : IsProductDisconnected Z M) :
    ((closure (Z ∩ (M : Set G))).subgroupOf M).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [distinguishedClosure_normalizer h]

variable [Finite G]

/-- Every distinguished involution in `M` has a distinct commuting distinguished
involution in `M`. Isolation would make the distinguished class constant modulo
the odd core, forcing its entire closure into `M`. -/
public theorem exists_commuting_distinguished_of_minimal
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) :
    ∃ y ∈ Z, y ∈ M ∧ z ≠ y ∧ Commute z y := by
  classical
  by_contra hn
  have hiso : ∀ y ∈ Z, Commute z y → y = z := by
    intro y hy hc
    by_contra hne
    exact hn ⟨y, hy, mem_of_commute h.disconnected hz hzM hc, Ne.symm hne, hc⟩
  obtain ⟨S, hzS, hcentral⟩ := r.two_central z hz
  have hweak : Glauberman.ZStar.IsWeaklyClosedInSylow z (S : Subgroup G) := by
    refine ⟨hzS, ?_⟩
    intro g hg
    exact hiso _ (h.disconnected.invariant g z hz) (hcentral ⟨_, hg⟩)
  let q := QuotientGroup.mk' (pPrimeCore 2 G)
  have hcz : q z ∈ center (G ⧸ pPrimeCore 2 G) :=
    Glauberman.ZStar.glauberman_zstar_local S z (h.disconnected.involutions z hz) hzS
      (fun s hs => (hcentral ⟨s, hs⟩).symm.eq) hweak
  have hcoreM := h.oddCore_le r.generated r.one_class r.two_central
  apply h.disconnected.closure_not_le
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (r.one_class z hz x hx)
  have he : q x = q z := by
    rw [← hg, map_mul, map_mul, map_inv,
      mem_center_iff.mp hcz (q g), mul_assoc, mul_inv_cancel, mul_one]
  have hxz : x * z⁻¹ ∈ pPrimeCore 2 G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (x * z⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  change x ∈ M
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using M.mul_mem (hcoreM hxz) hzM

/-- The source subgroup `M° = ⟨Z ∩ M⟩` has two-rank at least two. -/
public theorem distinguishedClosure_twoRank
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) :
    TwoRankAtLeastTwo (closure (Z ∩ (M : Set G))) := by
  obtain ⟨z, hz, hzM⟩ := h.disconnected.nonempty
  obtain ⟨y, hy, hyM, hne, hc⟩ := exists_commuting_distinguished_of_minimal h r hz hzM
  let A := closure (Z ∩ (M : Set G))
  let zA : A := ⟨z, subset_closure ⟨hz, hzM⟩⟩
  let yA : A := ⟨y, subset_closure ⟨hy, hyM⟩⟩
  have hzI : PFAppendixIII.IsInvolution zA := IsInvolution.subtype (h.disconnected.involutions z hz) zA.property
  have hyI : PFAppendixIII.IsInvolution yA := IsInvolution.subtype (h.disconnected.involutions y hy) yA.property
  have hcA : Commute zA yA := by apply Subtype.ext; exact hc.eq
  have hneA : zA ≠ yA := fun he => hne (congrArg Subtype.val he)
  let E := closure ({zA, yA} : Set A)
  let _ : IsKleinFour E := isKleinFour_closure_pair zA yA
    (by simpa [pow_two] using hzI.sq_eq_one)
    (by simpa [pow_two] using hyI.sq_eq_one) hzI.ne_one hyI.ne_one hneA hcA
  exact ⟨E, IsKleinFour.card_four, fun x => by
    simpa only [IsKleinFour.exponent_two] using Monoid.pow_exponent_eq_one x⟩

/-- Containment of `M°` transfers its elementary four into the local intersection. -/
public theorem localIntersection_twoRank_of_distinguishedClosure_le
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (H : Subgroup G) (hAH : closure (Z ∩ (M : Set G)) ≤ H) :
    TwoRankAtLeastTwo (M.comap H.subtype) := by
  let A := closure (Z ∩ (M : Set G))
  let f : A →* M.comap H.subtype := {
    toFun a := ⟨⟨a, hAH a.property⟩, distinguishedClosure_le (Z := Z) (M := M) a.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply (distinguishedClosure_twoRank h r).map_of_injective f
  intro a b he
  exact Subtype.ext (congrArg (fun x : M.comap H.subtype => ((x : H) : G)) he)

/-- A subgroup containing `M°` has its odd core in `M`, by four-group coprime action. -/
public theorem oddCore_le_of_distinguishedClosure_le
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (H : Subgroup G) (hAH : closure (Z ∩ (M : Set G)) ≤ H) :
    (twoPrimeCore H).map H.subtype ≤ M := by
  obtain ⟨z, hz, hzM⟩ := h.disconnected.nonempty
  obtain ⟨y, hy, hyM, hne, hc⟩ := exists_commuting_distinguished_of_minimal h r hz hzM
  let W := (twoPrimeCore H).map H.subtype
  have hWH : W ≤ H := by rintro _ ⟨w, _, rfl⟩; exact w.property
  have hWsub : W.subgroupOf H = twoPrimeCore H :=
    comap_map_eq_self_of_injective Subtype.val_injective _
  have hWnormal : (W.subgroupOf H).Normal := by rw [hWsub]; infer_instance
  have hHnorm : H ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hWH).mp hWnormal
  have hodd : Odd (Nat.card W) := by
    rw [show Nat.card W = Nat.card (twoPrimeCore H) from
      card_map_of_injective Subtype.val_injective]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))
  apply odd_le_of_commuting_distinguished h.disconnected W hodd hz hzM hy hne hc
  apply le_trans ?_ hHnorm
  apply (closure_le H).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hAH (subset_closure ⟨hz, hzM⟩)
  · have he : x = y := Set.mem_singleton_iff.mp hx
    subst x
    exact hAH (subset_closure ⟨hy, hyM⟩)

/-- For proper residual `L`, the remaining containment `M° ≤ L` suffices
to centralize the odd core. The premise is the unproved orbit-counting step,
not an extra hypothesis of source Lemma 12.2. -/
public theorem residualGenerated_oddCore_le_center_of_distinguishedClosure_le
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    twoPrimeCore (residualGenerated M z t) ≤ center (residualGenerated M z t) :=
  residualGenerated_oddCore_le_center h.disconnected r ha hz hzM ht htM hL
    (oddCore_le_of_distinguishedClosure_le h r _ hAL)

end BenderSuzuki.ZD
