module

public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import GorensteinWalter.PSL2PerfectSubnormal
public import GorensteinWalter.PGL2PerfectSubnormal
public import Theory.GroupTheory.CComponent.Basic

/-!
# Nonsolvable Sylow overgroups in quadratic PSL₂

Dickson's proper nonsolvable alternatives in PSL₂(p²) are A₅, PSL₂(p), and
PGL₂(p). The full Sylow hypothesis excludes A₅: its two-part is at most four,
whereas the odd square field has order one modulo eight. A nontrivial perfect
subnormal subgroup of either remaining model is the actual PSL₂(p) subgroup.

Source: Huppert II.8.27; Aschbacher–Smith A.3.12(8), printed pp.47–48.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.PSL2

/-- The nonsolvable proper full-Sylow overgroups in the quadratic field case
have the actual prime-field PSL₂ or PGL₂ model. -/
theorem quadratic_nonsolvable_proper_sylow_models
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (S : Sylow 2 (PSL2MatrixGroup F)) (H : Subgroup (PSL2MatrixGroup F))
    (hSH : (S : Subgroup _) ≤ H) (hne : H ≠ ⊤) (hns : ¬ Group.IsSolvable H) :
    Nonempty (H ≃* PSL2MatrixGroup (GaloisField p 1)) ∨
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p 1)) := by
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hF H with hEl | hCyc | hDih | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · let := hEl
    exact (hns inferInstance).elim
  · obtain ⟨n, _, _, hc⟩ := hCyc
    let := hc
    exact (hns inferInstance).elim
  · obtain ⟨n, _, _, ⟨e⟩⟩ := hDih
    let := GLS3.Chapter5.dihedralGroup_isSolvable n
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨e⟩ := hA4.2
    let := Equiv.Perm.isSolvable_fin_four
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨e⟩ := hS4.2
    let := Equiv.Perm.isSolvable_fin_four
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨e⟩ := hA5.2
    have hcard : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hnot : ¬ 8 ∣ Nat.card (PSL2MatrixGroup F) := by
      intro hd
      have hh := (S.pow_dvd_card_of_pow_dvd_card (n := 3) hd).trans
        (card_dvd_of_le hSH)
      rw [hcard] at hh
      norm_num at hh
    have hm := mod_eight_of_not_eight_dvd_card (hF ▸ ho.pow) hnot
    rw [hF] at hm
    have hodd : p % 2 = 1 := Nat.odd_iff.mp ho
    have hb : p % 8 < 8 := Nat.mod_lt _ (by decide)
    have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases hr with he | he | he | he <;> norm_num [Nat.pow_mod, he] at hm
  · obtain ⟨m, t, _, _, N, C, hn, he, _, hc, _, _, hg⟩ := hAff
    let := hn
    let := he
    let := hc
    exact (hns (Group.isSolvable_of_normal_sup_eq_top N C hg)).elim
  · obtain ⟨m, hm, hd, ⟨e⟩⟩ := hPSL
    have hb := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with rfl | rfl
    · exact .inl ⟨e⟩
    have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by decide)
    apply (hne (H.eq_top_of_card_eq ?_)).elim
    rw [Nat.card_congr e.toEquiv,
      GorensteinWalter.psl2_card_formula (GaloisField p 2)
        ⟨p, 2, Fact.out, ho, by decide, hK⟩,
      GorensteinWalter.psl2_card_formula F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩, hK, hF]
  · obtain ⟨m, hm, hd, e⟩ := hPGL
    have hb := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hm1 : m = 1 := by omega
    subst m
    exact .inr e

/-- A C-component of either prime-field overgroup is PSL₂(p), and its
nontrivial perfectness rules out the exceptional prime three. -/
theorem cComponent_prime_linear_model
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (C : Subgroup H) (hC : C.IsCComponent)
    (hmodel : Nonempty (H ≃* PSL2MatrixGroup (GaloisField p 1)) ∨
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p 1))) :
    3 < p ∧ Nonempty (C ≃* PSL2MatrixGroup (GaloisField p 1)) := by
  have hcard : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 (by decide)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p 1)) :=
    ⟨p, 1, Fact.out, ho, by decide, by simpa using hcard⟩
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    have hc := hC.map_equiv e
    obtain ⟨hp, he⟩ := GorensteinWalter.psl2_perfect_subnormal_eq_top
      (GaloisField p 1) hodd _ hc.ne_bot hc.perfect hc.subnormal
    refine ⟨hcard ▸ hp, ⟨?_⟩⟩
    exact ((C.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)).trans topEquiv
  · obtain ⟨e⟩ := hmodel
    let : Finite (GorensteinWalter.PGL2 (GaloisField p 1)) :=
      Finite.of_surjective e e.surjective
    have hc := hC.map_equiv e
    obtain ⟨hp, he⟩ := GorensteinWalter.pgl2_perfect_subnormal_eq_commutator
      (GaloisField p 1) hodd _ hc.ne_bot hc.perfect hc.subnormal
    obtain ⟨d⟩ := GorensteinWalter.commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      (GaloisField p 1) hodd hp (MulEquiv.refl _)
    exact ⟨hcard ▸ hp, ⟨((C.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)).trans d⟩⟩

end Theory.PSL2
