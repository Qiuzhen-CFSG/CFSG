module
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Placing a central cubic from a perfect subgroup

If a finite group has Sylow p-subgroups of order p³, a perfect subgroup
whose order is divisible by p³ contains a full Sylow subgroup. Transfer puts
its central p-elements in that Sylow subgroup's Frattini subgroup. Sylow
conjugacy then places each such element in every subgroup of order divisible
by p², since every subgroup of index at most p contains the Frattini subgroup.

This supplies the placement step for the central cubic in the M₂₂ covering
residual inside the full J₄ component in Aschbacher--Smith 4.2.13, p.612.
-/

public noncomputable section
open Subgroup

private theorem sylow_power_dvd {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (n : ℕ)
    (h : p ^ n ∣ Nat.card G) : p ^ n ∣ Nat.card P := by
  have hc : Nat.Coprime (p ^ n) P.index :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index).pow_left n
  rw [← P.toSubgroup.card_mul_index] at h
  exact hc.dvd_of_dvd_mul_right h

private theorem frattini_le_of_large {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p P) (hc : Nat.card P = p ^ 3)
    (U : Subgroup P) (hU : p ^ 2 ≤ Nat.card U) : frattini P ≤ U := by
  rcases eq_top_or_exists_le_coatom U with rfl | ⟨M,hM,hUM⟩
  · exact le_top
  let : Fact (IsPGroup p P) := ⟨hp⟩
  let := coatom_normal_of_isPGroup (p := p) hM
  have hi : M.index = p := card_quotient_coatom_eq_prime (p := p) hM
  have hcard : Nat.card M = p ^ 2 := by
    have hh := M.card_mul_index
    rw [hi,hc,pow_succ] at hh
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hh
  have he : U = M := eq_of_le_of_card_ge hUM (hcard ▸ hU)
  rw [he]
  exact frattini_le_coatom hM

/-- A central prime element in a perfect seed of full cubic Sylow order
has a conjugate in every subgroup whose order is divisible by p². -/
theorem perfect_central_cubic_conjugate_mem
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : Nat.card P = p ^ 3)
    (S : Subgroup G) [Group.IsPerfect S] (hS : p ^ 3 ∣ Nat.card S)
    (x : S) (hx : orderOf x = p) (hz : x ∈ center S)
    (F : Subgroup G) (hF : p ^ 2 ∣ Nat.card F) :
    ∃ g : G, g * (x : G) * g⁻¹ ∈ F := by
  let Q : Sylow p S := default
  let Rg := (Q : Subgroup S).map S.subtype
  obtain ⟨R,hR⟩ := (Q.isPGroup'.map S.subtype).exists_le_sylow
  have hcR : Nat.card R = p ^ 3 :=
    (Nat.card_congr (Sylow.equiv R P).toEquiv).trans hP
  have hcardQ : Nat.card Q = p ^ 3 := by
    have hd := sylow_power_dvd Q 3 hS
    have hu := card_dvd_of_le hR
    rw [card_map_of_injective S.subtype_injective,hcR] at hu
    exact Nat.dvd_antisymm hu hd
  have heR : Rg = (R : Subgroup G) := eq_of_le_of_card_ge hR (by
    rw [card_map_of_injective S.subtype_injective,hcardQ,hcR])
  let eR : Q ≃* R := ((Q : Subgroup S).equivMapOfInjective S.subtype
    S.subtype_injective).trans (MulEquiv.subgroupCongr heR)
  have hxQ : x ∈ (Q : Subgroup S) := by
    let Z := zpowers x
    have hZ : Z ≤ center S := zpowers_le.mpr hz
    let : Z.Normal := ⟨fun y hy g => by
      rw [mem_center_iff.mp (hZ hy) g,mul_inv_cancel_right]
      exact hy⟩
    have hp : IsPGroup p Z := IsPGroup.of_card (n := 1)
      (by simpa only [Z,Nat.card_zpowers,pow_one] using hx)
    exact hp.le_sylow_of_normal Q (mem_zpowers x)
  let xQ : Q := ⟨x,hxQ⟩
  have hxPhi : xQ ∈ frattini Q :=
    PerfectCentralCovering.central_subgroup_le_frattini_sylow Q
      ((center S).subgroupOf (Q : Subgroup S)) (by rintro y ⟨z,hz,rfl⟩; exact hz) hz
  let U : Sylow p F := default
  let Ug := (U : Subgroup F).map F.subtype
  obtain ⟨T,hUT⟩ := (U.isPGroup'.map F.subtype).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G R T
  let a := MulAut.conj g
  have hRT : (R : Subgroup G).map a.toMonoidHom = (T : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  let e : Q ≃* T := eR.trans ((a.subgroupMap (R : Subgroup G)).trans
    (MulEquiv.subgroupCongr hRT))
  have hxPhiT : e xQ ∈ frattini T :=
    frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective hxPhi
  have hcT : Nat.card T = p ^ 3 :=
    (Nat.card_congr (Sylow.equiv T P).toEquiv).trans hP
  have hcardU : p ^ 2 ≤ Nat.card (Ug.subgroupOf (T : Subgroup G)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv,
      card_map_of_injective F.subtype_injective]
    exact Nat.le_of_dvd Nat.card_pos (sylow_power_dvd U 2 hF)
  have hmem := frattini_le_of_large T.isPGroup' hcT
    (Ug.subgroupOf (T : Subgroup G)) hcardU hxPhiT
  refine ⟨g,?_⟩
  have hh : ((e xQ : T) : G) ∈ F := (map_subtype_le (U : Subgroup F)) hmem
  exact hh
