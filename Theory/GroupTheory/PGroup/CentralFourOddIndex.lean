module
public import Theory.GroupAction.OddInvariantSylow
public import Theory.GroupTheory.PGroup.CentralFourCoprimeIndex

/-!
# Fourth-power fixed indices on odd groups

A nontrivial action of the center of a two-group on an odd finite group is
detected on a compatible invariant Sylow subgroup. First choose an invariant
Sylow subgroup of the common fixed group and extend it to an invariant Sylow
subgroup of the whole group. The two intersection indices give divisibility
of its fixed index into the original fixed index.

For an actor of order 64 with central four-group and the intrinsic Lyons
centralizer profile, the existing extraspecial theorem supplies a fourth-power
prime divisor without assuming that the odd group is nilpotent.

Source: Lyons, A Characterization of the Group U₃(4) (1972), §5, p.386.
-/

namespace CentralFourCoprimeIndex

open Subgroup

private theorem central_fixed_invariant
    {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K] :
    IsInvariant A K (FixedPoints.subgroup (center A) K) := by
  have hf (a : A) (x : K) (hx : x ∈ FixedPoints.subgroup (center A) K) :
      a • x ∈ FixedPoints.subgroup (center A) K := by
    intro z
    change (z : A) • (a • x) = a • x
    rw [← mul_smul, ← mem_center_iff.mp z.property a, mul_smul]
    exact congrArg (fun y : K => a • y) (hx z)
  exact ⟨fun a x => ⟨hf a x, fun hx => by simpa using hf a⁻¹ (a • x) hx⟩⟩

/-- Detect a nontrivial central action on a compatible invariant Sylow subgroup. -/
public theorem exists_invariant_sylow_center_fixed_index
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K] (hA : IsPGroup 2 A) (hodd : Odd (Nat.card K))
    (hne : FixedPoints.subgroup (center A) K ≠ ⊤) :
    ∃ p : ℕ, ∃ _hp : p.Prime, ∃ P : Sylow p K,
      ∃ hPI : IsInvariant A K (P : Subgroup K),
      let := hPI
      p ≠ 2 ∧ FixedPoints.subgroup (center A) P ≠ ⊤ ∧
        (FixedPoints.subgroup (center A) P).index ∣
          (FixedPoints.subgroup (center A) K).index := by
  classical
  let F := FixedPoints.subgroup (center A) K
  have hi : F.index ≠ 1 := by
    intro he
    exact hne (index_eq_one.mp he)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hi
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd.not_two_dvd_nat (hpd.trans F.index_dvd_card)
  let : IsInvariant A K F := central_fixed_invariant
  have hbot : IsInvariant A F (⊥ : Subgroup F) := by
    refine ⟨fun a x => ?_⟩
    simp only [mem_bot]
    exact ⟨fun hx => by simp [hx], fun hx => by
      have hh := congrArg (fun y : F => a⁻¹ • y) hx
      simpa using hh⟩
  obtain ⟨R, _, hRI⟩ := exists_invariant_sylow_le_of_isPGroup (p := p) hA
    (hodd.of_dvd_nat F.card_subgroup_dvd_card) (⊥ : Subgroup F) IsPGroup.of_bot hbot
  let : IsInvariant A F (R : Subgroup F) := hRI
  let R' := (R : Subgroup F).map F.subtype
  obtain ⟨P, hRP, hPI⟩ := exists_invariant_sylow_le_of_isPGroup (p := p) hA hodd R'
    (R.isPGroup'.map F.subtype) (isInvariant_map_subtype F (R : Subgroup F))
  let : IsInvariant A K (P : Subgroup K) := hPI
  let E := FixedPoints.subgroup (center A) P
  have hE : E = F.subgroupOf (P : Subgroup K) := by
    ext x
    change (∀ z : center A, z • x = x) ↔ ∀ z : center A, z • (x : K) = x
    simp only [Subtype.ext_iff]
    rfl
  have hR : (P : Subgroup K).subgroupOf F = (R : Subgroup F) :=
    R.is_maximal' (P.isPGroup'.comap_of_injective F.subtype F.subtype_injective)
      (fun x hx => hRP ⟨x, hx, rfl⟩)
  have hindex : E.index * (P : Subgroup K).index = (R : Subgroup F).index * F.index := by
    rw [hE]
    change F.relIndex (P : Subgroup K) * (P : Subgroup K).index = _
    rw [← inf_relIndex_right, relIndex_mul_index inf_le_right]
    conv_rhs => rw [← hR]
    change _ = (P : Subgroup K).relIndex F * F.index
    rw [← inf_relIndex_right, relIndex_mul_index inf_le_right, inf_comm]
  obtain ⟨k, hk⟩ := P.isPGroup'.index E
  have hcop : Nat.Coprime E.index (R : Subgroup F).index := by
    rw [hk]
    exact (hp.coprime_iff_not_dvd.mpr R.not_dvd_index).pow_left k
  have hdiv : E.index ∣ F.index :=
    hcop.dvd_of_dvd_mul_left ⟨(P : Subgroup K).index, hindex.symm⟩
  have hEnot : E ≠ ⊤ := by
    intro he
    rw [he, index_top, one_mul] at hindex
    exact P.not_dvd_index (hindex ▸ dvd_mul_of_dvd_right hpd _)
  exact ⟨p, hp, P, hPI, hp2, hEnot, hdiv⟩

/-- The intrinsic fourth-power obstruction holds on arbitrary finite odd groups. -/
public theorem exists_prime_fourth_pow_dvd_center_fixed_index
    {T K : Type*} [Group T] [Finite T] [Group K] [Finite K]
    (hT : IsPGroup 2 T)
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hfrattini : frattini T = center T)
    [IsElementaryAbelian 2 (center T)]
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    (hodd : Odd (Nat.card K)) (ρ : T →* MulAut K)
    (hkernel : ∃ z : T, z ∈ center T ∧ z ≠ 1 ∧ ρ z = 1)
    (hnontrivial : ¬ center T ≤ ρ.ker) :
    letI : MulDistribMulAction T K := MulDistribMulAction.compHom K ρ
    ∃ p : ℕ, p.Prime ∧ p ^ 4 ∣ (FixedPoints.subgroup (center T) K).index := by
  let : MulDistribMulAction T K := MulDistribMulAction.compHom K ρ
  have hne : FixedPoints.subgroup (center T) K ≠ ⊤ := by
    intro he
    apply hnontrivial
    intro z hz
    apply MulEquiv.ext
    intro x
    exact (show x ∈ FixedPoints.subgroup (center T) K from he ▸ mem_top x) ⟨z, hz⟩
  obtain ⟨p, hp, P, hPI, hp2, hPne, hdiv⟩ :=
    exists_invariant_sylow_center_fixed_index hT hodd hne
  let : Fact p.Prime := ⟨hp⟩
  let : IsInvariant T K (P : Subgroup K) := hPI
  let σ : T →* MulAut P := MulDistribMulAction.toMulAut T P
  have hker : ∃ z : T, z ∈ center T ∧ z ≠ 1 ∧ σ z = 1 := by
    obtain ⟨z, hz, hz1, hρ⟩ := hkernel
    refine ⟨z, hz, hz1, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun hρ (x : K)
  have hnot : ¬ center T ≤ σ.ker := by
    intro hh
    apply hPne
    apply top_unique
    intro x _ z
    exact DFunLike.congr_fun (hh z.property) x
  exact ⟨p, hp, (fourth_pow_dvd_center_fixed_index_of_frattini_eq_center
    hT hcard hcenter hfrattini hcentralizer hp2 P.isPGroup' σ hker hnot).trans hdiv⟩

end CentralFourCoprimeIndex
