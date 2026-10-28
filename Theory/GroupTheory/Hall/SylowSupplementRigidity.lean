module

public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.SolvableRadical
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normalization from a coprime solvable supplement

Let N be normal and solvable, with H = NW, and let E be solvable of
order coprime to N. If P lies in both E and W and C_N(P) lies in W,
then E lies in W. No solvability assumption on H or W is needed.

Work in the solvable product NE. The intersection W ∩ NE supplements N,
so its index divides |N|. Hall existence extends P to a Hall subgroup U
of this intersection, which is also Hall in NE for the primes dividing
|E|. Hall conjugacy gives U = n E n⁻¹ for n in N. Since P lies in both U
and E and N ∩ U = 1, n centralizes P. Thus n lies in W, and E lies in W.

Taking W = N_H(B) gives the exact nilpotent-supplement and Sylow contract
used in the A.3.6 rigidity reduction. Oddness and Sylow maximality are
retained in that interface, although the argument needs only a shared
subgroup. This is a Hall-conjugacy auxiliary to Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.3.6, printed pp.43–45,
and the ambient normalization reduction for 13.6.20, printed p.931.
-/

public section
open Subgroup

private theorem supplement_index_dvd {H : Type*} [Group H] [Finite H]
    (N W : Subgroup H) [N.Normal] (hsup : N ⊔ W = ⊤) : W.index ∣ Nat.card N := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes N W le_normalizer_of_normal
  rw [hsup, card_top, ← W.card_mul_index] at h
  have he : Nat.card N = Nat.card (N ⊓ W : Subgroup H) * W.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := W))
    calc
      Nat.card N * Nat.card W = Nat.card (N ⊓ W : Subgroup H) *
          (Nat.card W * W.index) := h
      _ = (Nat.card (N ⊓ W : Subgroup H) * W.index) * Nat.card W := by ac_rfl
  rw [he]
  exact dvd_mul_left _ _

private theorem solvable_supplement_control {H : Type*} [Group H] [Finite H]
    [Group.IsSolvable H]
    (N W E P : Subgroup H) [N.Normal]
    (hNW : N ⊔ W = ⊤) (hNE : N ⊔ E = ⊤)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card E))
    (hPW : P ≤ W) (hPE : P ≤ E)
    (hfixed : N ⊓ centralizer (P : Set H) ≤ W) : E ≤ W := by
  classical
  let π : Set Nat.Primes := {p | p.val ∣ Nat.card E}
  have hEHall : IsHallSubgroup π E := by
    refine isHallSubgroup_of π E (fun _ h => h) ?_
    intro p hp hi
    exact p.property.ne_one (Nat.eq_one_of_dvd_coprimes hcop
      (hi.trans (supplement_index_dvd N E hNE)) hp)
  let PW := P.subgroupOf W
  let _ : MulDistribMulAction Unit W := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  have hPWpi : IsPiSubgroup π PW := by
    intro p hp
    have hc : Nat.card PW = Nat.card P :=
      Nat.card_congr (subgroupOfEquivOfLe hPW).toEquiv
    exact (hc ▸ hp).trans (card_dvd_of_le hPE)
  obtain ⟨J, hJ, _, hPJ⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) (inferInstance : Group.IsSolvable W) (by simp) π PW hPWpi
    (⟨fun _ _ => Iff.rfl⟩ : IsInvariant Unit W PW)
  let U := J.map W.subtype
  have hUW : U ≤ W := map_subtype_le J
  have hPU : P ≤ U := by
    intro x hx
    exact ⟨⟨x, hPW hx⟩, hPJ hx, rfl⟩
  have hUHall : IsHallSubgroup π U := by
    refine isHallSubgroup_of π U ?_ ?_
    · intro p hp
      exact hJ.p_in_pi_of_p_dvd_card p (hp.trans (card_map_dvd J W.subtype))
    · intro p hp hi
      change p.val ∣ (J.map W.subtype).index at hi
      rw [index_map_subtype] at hi
      rcases p.property.dvd_mul.mp hi with hi | hi
      · exact hJ.p_in_pi_of_p_dvd_index p hi hp
      · exact p.property.ne_one (Nat.eq_one_of_dvd_coprimes hcop
          (hi.trans (supplement_index_dvd N W hNW)) hp)
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (inferInstance : Group.IsSolvable H) hEHall hUHall
  obtain ⟨n, hn, e, he, hne⟩ := (mem_sup_of_normal_left (s := N) (t := E)).mp
    (show g ∈ N ⊔ E by rw [hNE]; trivial)
  have hconj : U = E.map (MulAut.conj n).toMonoidHom := by
    rw [← hne] at hg
    exact hg.trans (map_conj_mul_right_eq_of_mem_normalizer n ⟨e, E.le_normalizer he⟩)
  have hNU : Disjoint N U := by
    apply disjoint_of_coprime_natCard
    apply Nat.coprime_of_dvd
    intro p hp hn hu
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hn
      (hUHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hu))
  have hnC : n ∈ centralizer (P : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hxU : n * x * n⁻¹ ∈ U := by
      rw [hconj]
      exact ⟨x, hPE hx, rfl⟩
    have hcN : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have hni := (inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) x
      simpa only [mul_assoc] using N.mul_mem hn hni
    have hcU : n * x * n⁻¹ * x⁻¹ ∈ U := U.mul_mem hxU (U.inv_mem (hPU hx))
    have hc : n * x * n⁻¹ * x⁻¹ = 1 := (disjoint_def.mp hNU) hcN hcU
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)).symm
  have hnW : n ∈ W := hfixed ⟨hn, hnC⟩
  intro x hx
  have hc : n * x * n⁻¹ ∈ W := hUW (by rw [hconj]; exact ⟨x, hx, rfl⟩)
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
    W.mul_mem (W.mul_mem (W.inv_mem hnW) hc) hnW

/-- Fixed points control a coprime solvable subgroup over a normal solvable supplement. -/
theorem Subgroup.le_of_coprime_solvable_supplement_fixed_points
    {H : Type*} [Group H] [Finite H]
    (N W E P : Subgroup H) [N.Normal] [Group.IsSolvable N] [Group.IsSolvable E]
    (hNW : N ⊔ W = ⊤) (hcop : Nat.Coprime (Nat.card N) (Nat.card E))
    (hPW : P ≤ W) (hPE : P ≤ E)
    (hfixed : N ⊓ centralizer (P : Set H) ≤ W) : E ≤ W := by
  let M : Subgroup H := N ⊔ E
  have hNM : N ≤ M := le_sup_left
  have hEM : E ≤ M := le_sup_right
  have hPM : P ≤ M := hPE.trans hEM
  let : Group.IsSolvable M := Group.isSolvable_sup_of_normal_left N E
  have hNE' : N.subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup hNM hEM]
    exact subgroupOf_self M
  have hNW' : N.subgroupOf M ⊔ W.subgroupOf M = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn, w, hw, hnw⟩ := (mem_sup_of_normal_left (s := N) (t := W)).mp
      (show x.val ∈ N ⊔ W by rw [hNW]; trivial)
    have hnM : n ∈ M := hNM hn
    have hwM : w ∈ M := by
      have hh := M.mul_mem (M.inv_mem hnM) x.property
      rw [← hnw, inv_mul_cancel_left] at hh
      exact hh
    exact mem_sup_of_normal_left.mpr
      ⟨⟨n, hnM⟩, hn, ⟨w, hwM⟩, hw, Subtype.ext hnw⟩
  have hcN : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv
  have hcE : Nat.card (E.subgroupOf M) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv
  have hcop' : Nat.Coprime (Nat.card (N.subgroupOf M)) (Nat.card (E.subgroupOf M)) := by
    rwa [hcN, hcE]
  have hfixed' : N.subgroupOf M ⊓ centralizer (P.subgroupOf M : Set M) ≤ W.subgroupOf M := by
    intro x hx
    apply hfixed
    refine ⟨hx.1, mem_centralizer_iff.mpr ?_⟩
    intro p hp
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hx.2) ⟨p, hPM hp⟩ hp)
  have hEW := solvable_supplement_control (N.subgroupOf M) (W.subgroupOf M)
    (E.subgroupOf M) (P.subgroupOf M) hNW' hNE' hcop'
    (comap_mono hPW) (comap_mono hPE) hfixed'
  intro x hx
  exact hEW (show (⟨x, hEM hx⟩ : M) ∈ E.subgroupOf M from hx)

/-- Hall conjugacy and fixed-point control normalize a subgroup with a nilpotent supplement. -/
theorem normalizes_of_nilpotent_supplement_of_sylow_fixed_points
    {H : Type*} [Group H] [Finite H] (N B E : Subgroup H) (S : Sylow 2 H)
    (hN : N.Normal) (hnil : Group.IsNilpotent N)
    (_hodd : Nat.Coprime 2 (Nat.card N)) (hNB : N ⊔ B = ⊤)
    (hSB : (S : Subgroup H) ≤ normalizer (B : Set H)) (hSE : (S : Subgroup H) ≤ E)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card E)) (hsolv : Group.IsSolvable E)
    (hfixed : N ⊓ centralizer (S : Set H) ≤ normalizer (B : Set H)) :
    E ≤ normalizer (B : Set H) := by
  let := hN
  let := hnil
  let := hsolv
  apply Subgroup.le_of_coprime_solvable_supplement_fixed_points N (normalizer (B : Set H)) E
    (S : Subgroup H) ?_ hcop hSB hSE hfixed
  apply top_unique
  rw [← hNB]
  exact sup_le_sup_left B.le_normalizer N
