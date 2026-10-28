module
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.LocalSetup
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.KernelGeneration.SuzukiActions
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# The Sz(8) kernel is the local third commutator

Write P for the full preimage of the standard root subgroup under the actual
universal projection and J = [P,[P,P]]. The inclusion J ≤ ker is supplied by
`LocalSetup`. Quotienting by the central subgroup J gives another finite
perfect central cover, whose full root preimage has class at most two.

A nontrivial remaining kernel is a two-group and admits an index-two subgroup.
The resulting double cover still has a root preimage of class at most two.
The intrinsic Suzuki Sylow-center criterion identifies its Sylow center with
its kernel. Its derived subgroup therefore maps trivially to the base root
group, contradicting the nonabelian root-coordinate theorem. Hence the
quotient kernel is trivial, and the original kernel equals J.

Sources: Huppert--Blackburn III XI.3.1--3.3; the intrinsic proof of the
Sylow-center conclusion in GLS4, Chapter 4, Lemma 2.8(c). The central
index-two quotient construction follows `PerfectCentralCoverSylowRigidityTwoKernel`.
This is the kernel-generation input for the exceptional upper bound in
Aschbacher--Smith I.1.3(5), printed p.407/PDF p.418, citing GLS3 §6.1.
Neither the multiplier table nor a numerical kernel bound is assumed.
-/

noncomputable section
open Subgroup PerfectCentralCovering
namespace BenderSuzuki.MatrixGroups.SchurCover.EightLocal

private def quotientCover {E B : Type*} [Group E] [Group B]
    (f : Cover E B) (N : Subgroup E) [N.Normal] (hN : N ≤ f.toMonoidHom.ker) :
    Cover (E ⧸ N) B where
  toMonoidHom := QuotientGroup.lift N f.toMonoidHom hN
  surjective := by
    intro b
    obtain ⟨x, hx⟩ := f.surjective b
    exact ⟨QuotientGroup.mk' N x, hx⟩
  isPerfect := by
    let := f.isPerfect
    infer_instance
  ker_le_center := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ f.toMonoidHom.ker := hx
    rw [mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact congrArg (QuotientGroup.mk' N) (mem_center_iff.mp (f.ker_le_center hy) w)

private theorem quotientCover_preimage {E B : Type*} [Group E] [Group B]
    (f : Cover E B) (N : Subgroup E) [N.Normal] (hN : N ≤ f.toMonoidHom.ker)
    (T : Subgroup B) :
    (T.comap f.toMonoidHom).map (QuotientGroup.mk' N) =
      T.comap (quotientCover f N hN).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨y, hx, rfl⟩

private theorem exists_kernel_half {E B : Type*} [Group E] [Finite E] [Group B]
    (f : Cover E B) (hp : IsPGroup 2 f.toMonoidHom.ker)
    (hne : f.toMonoidHom.ker ≠ ⊥) :
    ∃ N : Subgroup E, N ≤ f.toMonoidHom.ker ∧ N.Normal ∧
      Nat.card f.toMonoidHom.ker = 2 * Nat.card N := by
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hnpos : 0 < n := by
    have hcard := (Subgroup.one_lt_card_iff_ne_bot (H := f.toMonoidHom.ker)).mpr hne
    change 1 < Nat.card f.toMonoidHom.ker at hcard
    by_contra h
    have hzero : n = 0 := by omega
    rw [hn, hzero] at hcard
    norm_num at hcard
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := f.toMonoidHom.ker) 2
    (n := k) (by rw [hn, pow_succ]; exact dvd_mul_right _ _)
  let N := R.map f.toMonoidHom.ker.subtype
  have hNA : N ≤ f.toMonoidHom.ker := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hNc : N ≤ center E := hNA.trans f.ker_le_center
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hNc hn) g, mul_inv_cancel_right]
    exact hn⟩
  refine ⟨N, hNA, hNn, ?_⟩
  have hNc : Nat.card N = Nat.card R :=
    Subgroup.card_map_of_injective f.toMonoidHom.ker.subtype_injective
  rw [hNc, hR, hn, pow_succ, Nat.mul_comm]

private theorem doubleCover_root_third_ne_bot {E : Type*} [Group E] [Finite E]
    (f : Cover E (SuzukiMatrixGroup 1)) (hc : Nat.card f.toMonoidHom.ker = 2) :
    ⁅(SuzukiRootSubgroup 1).comap f.toMonoidHom,
      ⁅(SuzukiRootSubgroup 1).comap f.toMonoidHom,
        (SuzukiRootSubgroup 1).comap f.toMonoidHom⁆⁆ ≠ ⊥ := by
  intro hthird
  let R := (SuzukiRootSubgroup 1).comap f.toMonoidHom
  obtain ⟨Q, hQ⟩ := suzukiRootSubgroup_isSylow 1 (by decide)
  let P := Q.comapOfKerIsPGroup f.toMonoidHom (kernel_isTwoGroup (by decide) f)
    (by rw [MonoidHom.range_eq_top.mpr f.surjective]; exact le_top)
  have hP : (P : Subgroup E) = R := by
    change (Q : Subgroup (SuzukiMatrixGroup 1)).comap f.toMonoidHom = R
    rw [hQ]
  have hcenter : (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker :=
    f.sylow_center_eq_kernel_of_model_sylow hc (MulEquiv.refl _) Q
      (by rw [hQ]; exact KernelActions.root_sylow_center_action 1 (by decide)) P
  have hdP : commutator P ≤ center P := by
    apply commutator_top_left_eq_bot_iff_le_center.mp
    apply (map_injective (f := (P : Subgroup E).subtype) Subtype.val_injective)
    rw [map_commutator, ← MonoidHom.range_eq_map, (P : Subgroup E).range_subtype,
      map_subtype_commutator, Subgroup.map_bot, hP]
    exact hthird
  have hd : ⁅R, R⁆ ≤ f.toMonoidHom.ker := by
    rw [← hP, ← map_subtype_commutator, ← hcenter]
    exact map_mono hdP
  have hmap : R.map f.toMonoidHom = SuzukiRootSubgroup 1 :=
    map_comap_eq_self_of_surjective f.surjective _
  apply KernelActions.root_not_isMulCommutative 1 (by decide)
  apply commutator_self_eq_bot_iff.mp
  apply bot_unique
  rw [← hmap, ← map_commutator]
  exact map_le_iff_le_comap.mpr hd

/-- A perfect central cover of Sz(8) whose full root preimage has class at
most two has trivial kernel. The remaining central two-group, if nontrivial,
would admit a double-cover quotient with the same class bound. -/
public theorem kernel_eq_bot_of_root_third_eq_bot {E : Type*} [Group E] [Finite E]
    (f : Cover E (SuzukiMatrixGroup 1))
    (hthird : ⁅(SuzukiRootSubgroup 1).comap f.toMonoidHom,
      ⁅(SuzukiRootSubgroup 1).comap f.toMonoidHom,
        (SuzukiRootSubgroup 1).comap f.toMonoidHom⁆⁆ = ⊥) :
    f.toMonoidHom.ker = ⊥ := by
  by_contra hne
  obtain ⟨N, hN, hNn, hcard⟩ :=
    exists_kernel_half f (kernel_isTwoGroup (by decide) f) hne
  let : N.Normal := hNn
  let c := quotientCover f N hN
  let q := QuotientGroup.mk' N
  have hc : Nat.card c.toMonoidHom.ker = 2 := by
    have hh := Theory.GroupTheory.kernel_card_eq_mul_of_surjective_factor
      f.toMonoidHom c.toMonoidHom q c.surjective (QuotientGroup.mk'_surjective N)
      (by ext x; rfl)
    rw [QuotientGroup.ker_mk'] at hh
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  apply doubleCover_root_third_ne_bot c hc
  have hh := congrArg (Subgroup.map q) hthird
  rw [map_commutator, map_commutator, Subgroup.map_bot,
    quotientCover_preimage f N hN] at hh
  exact hh

local instance : Fact (0 < (1 : ℕ)) := ⟨by decide⟩

/-- The universal Sz(8) kernel is generated by the actual local third
commutators. This uses no cardinality bound or pairing data. -/
public theorem kernel_le_third : Kernel 1 ≤ ThirdCommutator := by
  let f := PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)
  let : ThirdCommutator.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (third_le_center hn) g, mul_inv_cancel_right]
    exact hn⟩
  let c := quotientCover f ThirdCommutator third_le_kernel
  let q := QuotientGroup.mk' ThirdCommutator
  have hclass : ⁅(SuzukiRootSubgroup 1).comap c.toMonoidHom,
      ⁅(SuzukiRootSubgroup 1).comap c.toMonoidHom,
        (SuzukiRootSubgroup 1).comap c.toMonoidHom⁆⁆ = ⊥ := by
    rw [← quotientCover_preimage f ThirdCommutator third_le_kernel,
      ← map_commutator, ← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact le_rfl)
  have hker := kernel_eq_bot_of_root_third_eq_bot c hclass
  intro x hx
  have hqx : q x ∈ c.toMonoidHom.ker := hx
  have hq1 : q x = 1 := mem_bot.mp (hker ▸ hqx)
  exact (QuotientGroup.eq_one_iff x).mp hq1

/-- The precise identification consumed by the exceptional multiplier bound. -/
public theorem kernel_eq_third : Kernel 1 = ThirdCommutator :=
  le_antisymm kernel_le_third third_le_kernel

end BenderSuzuki.MatrixGroups.SchurCover.EightLocal
end
