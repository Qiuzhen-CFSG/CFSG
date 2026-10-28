module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Seven-letter stabilizers and simultaneous transposition labels

A subgroup of S₇ of order 720 is a point stabilizer: an orbit of size k
bounds its order by k!(7-k)!, while the orbit size divides 720. Hence
orbits have size one or six, and a fixed letter exists.

For four transpositions forming a three-edge path and a disjoint edge,
a common fixed letter completes their six distinct endpoints to a
labeling of all seven letters. Conjugation by this single labeling
marks every edge at once.

These elementary permutation arguments supply the finite step at the
start of Held, Illinois J. Math. 13 (1969), Lemma 5.11, p.238,
DOI 10.1215/ijm/1256053756.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.MarkingConstruction

open Equiv Subgroup MulAction

private theorem orbit_card_bound (H : Subgroup (Perm (Fin 7))) (x : Fin 7) :
    Nat.card H ≤ (Nat.card (orbit H x)).factorial * (7 - Nat.card (orbit H x)).factorial := by
  classical
  let p : Fin 7 → Prop := fun y => y ∈ orbit H x
  have hinv (g : Perm (Fin 7)) (hg : g ∈ H) (a : Fin 7) : p (g a) ↔ p a := by
    change g • a ∈ orbit H x ↔ a ∈ orbit H x
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨⟨g, hg⟩⁻¹ * h, by
        change (⟨g, hg⟩⁻¹ : H) • (h • x) = a
        change h • x = (⟨g, hg⟩ : H) • a at hh
        rw [hh, inv_smul_smul]⟩
    · rintro ⟨h, hh⟩
      exact ⟨⟨g, hg⟩ * h, by simp [mul_smul, hh]⟩
  have hle : H ≤ (Perm.subtypeCongrHom p).range := by
    intro g hg
    refine ⟨(g.subtypePerm (hinv g hg), g.subtypePerm (fun a => not_congr (hinv g hg a))), ?_⟩
    apply Equiv.ext
    intro a
    change (Perm.subtypeCongr _ _) a = g a
    by_cases ha : p a
    · rw [Perm.subtypeCongr.left_apply _ _ ha]; rfl
    · rw [Perm.subtypeCongr.right_apply _ _ ha]; rfl
  have hcard := Subgroup.card_le_of_le hle
  have hr : Nat.card (Perm.subtypeCongrHom p).range =
      Nat.card (Perm {a // p a} × Perm {a // ¬ p a}) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coeSort_range
      (Perm.subtypeCongrHom_injective p)]
  rw [hr] at hcard
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_subtype_compl, p] using hcard

open scoped Classical in
private theorem orbit_card_options (H : Subgroup (Perm (Fin 7))) (hH : Nat.card H = 720)
    (x : Fin 7) : Fintype.card (orbit H x) = 1 ∨ Fintype.card (orbit H x) = 6 := by
  classical
  have hb := orbit_card_bound H x
  rw [hH, Nat.card_eq_fintype_card] at hb
  have hpos : 0 < Fintype.card (orbit H x) := Fintype.card_pos_iff.mpr
    ⟨⟨x, mem_orbit_self x⟩⟩
  have hle : Fintype.card (orbit H x) ≤ 7 := by
    simpa using Fintype.card_subtype_le (fun y => y ∈ orbit H x)
  have hd : Fintype.card (orbit H x) ∣ 720 := by
    rw [← hH, Nat.card_eq_fintype_card]
    exact ⟨_, (card_orbit_mul_card_stabilizer_eq_card_group H x).symm⟩
  interval_cases hn : Fintype.card (orbit H x) <;> norm_num [hn, Nat.factorial] at *

private theorem exists_fixed (H : Subgroup (Perm (Fin 7))) (hH : Nat.card H = 720) :
    ∃ x : Fin 7, ∀ g : H, (g : Perm (Fin 7)) x = x := by
  classical
  rcases orbit_card_options H hH 0 with h | h
  · exact ⟨0, mem_fixedPoints_iff_card_orbit_eq_one.mpr h⟩
  have hc : Fintype.card ↥(orbit H (0 : Fin 7))ᶜ = 1 := by
    rw [Fintype.card_compl_set, Fintype.card_fin, h]
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hc
  refine ⟨x, fun g => ?_⟩
  have hn : (g : Perm (Fin 7)) x ∉ orbit H (0 : Fin 7) := by
    intro hm
    apply x.property
    change g • (x : Fin 7) ∈ orbit H (0 : Fin 7) at hm
    have hm' := mem_orbit_of_mem_orbit g⁻¹ hm
    simpa using hm'
  exact congrArg Subtype.val (hx ⟨(g : Perm (Fin 7)) x, hn⟩)

private theorem stabilizer_card (x : Fin 7) : Nat.card (stabilizer (Perm (Fin 7)) x) = 720 := by
  classical
  have h := (stabilizer (Perm (Fin 7)) x).card_mul_index
  rw [index_stabilizer_of_transitive, Nat.card_perm] at h
  norm_num [Nat.factorial, Nat.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {g : Perm (Fin 7) // g x = x} = 720
  omega

public theorem exists_stabilizer_of_card_eq_720 (H : Subgroup (Perm (Fin 7))) (hH : Nat.card H = 720) :
    ∃ x : Fin 7, H = stabilizer (Perm (Fin 7)) x := by
  obtain ⟨x, hx⟩ := exists_fixed H hH
  refine ⟨x, eq_of_le_of_card_ge (fun g hg => hx ⟨g, hg⟩) ?_⟩
  rw [stabilizer_card, hH]

variable {α : Type*} [DecidableEq α]

private theorem commute_swaps_same_left {a b d : α} (hab : a ≠ b) (had : a ≠ d)
    (h : Commute (swap a b) (swap a d)) : b = d := by
  by_contra hbd
  have he := Equiv.congr_fun h.eq a
  simp only [Perm.mul_apply, swap_apply_left] at he
  simp [swap_apply_def, hbd, Ne.symm hab, Ne.symm had, Ne.symm hbd] at he

private theorem disjoint_swaps_of_commute {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Commute (swap a b) (swap c d)) (hne : swap a b ≠ swap c d) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have hac : a ≠ c := by
    rintro rfl
    exact hne (congrArg (swap a) (commute_swaps_same_left hab hcd hcomm))
  have had : a ≠ d := by
    rintro rfl
    rw [swap_comm c a] at hcomm hne
    exact hne (congrArg (swap a) (commute_swaps_same_left hab hcd.symm hcomm))
  have hbc : b ≠ c := by
    rintro rfl
    rw [swap_comm a b] at hcomm hne
    exact hne (congrArg (swap b) (commute_swaps_same_left hab.symm hcd hcomm))
  have hbd : b ≠ d := by
    rintro rfl
    rw [swap_comm a b, swap_comm c b] at hcomm hne
    exact hne (congrArg (swap b) (commute_swaps_same_left hab.symm hcd.symm hcomm))
  exact ⟨hac, had, hbc, hbd⟩

private theorem pair_path {s t : Perm α} (hs : s.IsSwap) (ht : t.IsSwap)
    (h : ¬ Commute s t) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = swap a b ∧ t = swap b c := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  have hne : swap a b ≠ swap c d := fun he => h (he ▸ Commute.refl _)
  by_cases hac : a = c
  · subst c
    refine ⟨b, a, d, hab.symm, ?_, hcd, swap_comm _ _, rfl⟩
    intro he
    exact hne (he ▸ rfl)
  by_cases had : a = d
  · subst d
    refine ⟨b, a, c, hab.symm, ?_, hcd.symm, swap_comm _ _, swap_comm _ _⟩
    intro he
    exact hne (he ▸ swap_comm _ _)
  by_cases hbc : b = c
  · subst c
    exact ⟨a, b, d, hab, had, hcd, rfl, rfl⟩
  by_cases hbd : b = d
  · subst d
    exact ⟨a, b, c, hab, hac, hcd.symm, rfl, swap_comm _ _⟩
  exact (h (Perm.disjoint_swap_swap (by simp_all)).commute).elim

private theorem triple_path {s t u : Perm α} (hs : s.IsSwap) (ht : t.IsSwap) (hu : u.IsSwap)
    (hst : ¬ Commute s t) (htu : ¬ Commute t u) (hsu : Commute s u) (hne : s ≠ u) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      s = swap a b ∧ t = swap b c ∧ u = swap c d := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl, rfl⟩ := pair_path hs ht hst
  obtain ⟨d, e, hde, rfl⟩ := hu
  obtain ⟨had, hae, hbd, hbe⟩ := disjoint_swaps_of_commute hab hde hsu hne
  by_cases hcd : c = d
  · subst d
    exact ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hde, rfl, rfl, rfl⟩
  by_cases hce : c = e
  · subst e
    exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hde.symm, rfl, rfl, swap_comm _ _⟩
  exact (htu (Perm.disjoint_swap_swap (by simp_all)).commute).elim

private theorem swap_fixed_ne {a b x : α} (hab : a ≠ b) (h : swap a b x = x) :
    a ≠ x ∧ b ≠ x := by
  constructor
  · rintro rfl
    exact hab (by simpa using h.symm)
  · rintro rfl
    exact hab (by simpa using h)

public theorem simultaneous_labels (s t u v : Perm (Fin 7)) (x : Fin 7)
    (hs : s.IsSwap) (ht : t.IsSwap) (hu : u.IsSwap) (hv : v.IsSwap)
    (hst : ¬ Commute s t) (htu : ¬ Commute t u)
    (hsu : Commute s u) (hsv : Commute s v) (htv : Commute t v) (huv : Commute u v)
    (hnsu : s ≠ u) (hnsv : s ≠ v) (hnuv : u ≠ v)
    (hsx : s x = x) (htx : t x = x) (hux : u x = x) (hvx : v x = x) :
    ∃ p : Perm (Fin 7), p 6 = x ∧
      MulAut.conj p (swap 0 1) = s ∧ MulAut.conj p (swap 1 2) = t ∧
      MulAut.conj p (swap 2 3) = u ∧ MulAut.conj p (swap 4 5) = v := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl, rfl, rfl⟩ :=
    triple_path hs ht hu hst htu hsu hnsu
  obtain ⟨e, f, hef, rfl⟩ := hv
  obtain ⟨hae, haf, hbe, hbf⟩ := disjoint_swaps_of_commute hab hef hsv hnsv
  obtain ⟨hce, hcf, hde, hdf⟩ := disjoint_swaps_of_commute hcd hef huv hnuv
  obtain ⟨hax, hbx⟩ := swap_fixed_ne hab hsx
  obtain ⟨hcx, hdx⟩ := swap_fixed_ne hcd hux
  obtain ⟨hex, hfx⟩ := swap_fixed_ne hef hvx
  let labels : Fin 7 → Fin 7 := ![a,b,c,d,e,f,x]
  have hinj : Function.Injective labels := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [labels]
  let p := Equiv.ofBijective labels (⟨hinj, Finite.surjective_of_injective hinj⟩)
  refine ⟨p, rfl, ?_, ?_, ?_, ?_⟩
  all_goals
    change p * swap _ _ * p⁻¹ = _
    rw [← Equiv.swap_apply_apply]
    rfl

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.MarkingConstruction
