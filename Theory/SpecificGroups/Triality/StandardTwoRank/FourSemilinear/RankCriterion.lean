module

public import Theory.GroupTheory.AutomorphismRankCyclicOuter
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.ElementaryAbelian.Join
public import Mathlib.GroupTheory.Sylow

/-!
# A central-subgroup criterion for sharp automorphism two-rank

An elementary automorphism subgroup fixes a Sylow two-subgroup, because the
number of Sylow subgroups is odd. Its inner kernel is elementary and lies in
that Sylow subgroup. If the ambient two-rank is at most a positive bound r
and the kernel has rank r, adjoining any central elementary subgroup cannot
enlarge it.
Consequently the kernel contains that subgroup. An outer involution in the
same elementary automorphism group would fix it pointwise, a contradiction
when the actual local action moves it. The cyclic outer image adds at most
one to the remaining kernel rank at most r - 1.

The triality application uses the highest-root subgroup; its semilinear
movement is established separately on the genuine coefficient field.
Source: the automorphism-rank step in Aschbacher--Smith G.9.3, printed p.356
(`refs/quasithin.pdf`), and the Sylow and root structure of GLS3 §§2.3--2.5
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.TwoRank.FourSemilinear

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_inj (hz : center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : G →* MulAut G).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hc : x ∈ center G := by
    rw [mem_center_iff]
    intro y
    have hy := MulEquiv.congr_fun (show MulAut.conj x = 1 from hx) y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [hz, mem_bot] using hc

private theorem normalized_rank_le (r : ℕ) (hrpos : 0 < r) (hz : center G = ⊥) [IsCyclic (MulAut.Outer G)]
    (hr : primeRank 2 G ≤ r) (U : Sylow 2 G) (Z : Subgroup G)
    [IsElementaryAbelian 2 Z]
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z)
    (hnonfix : ∀ a : MulAut G, a ^ 2 = 1 → a ∉ MulAut.innerSubgroup G →
      (U : Subgroup G).map a.toMonoidHom = U → ¬ Z ≤ a.fixedSubgroup)
    (E : Subgroup (MulAut G)) [IsElementaryAbelian 2 E]
    (hnorm : ∀ a ∈ E, (U : Subgroup G).map a.toMonoidHom = U) :
    primeRank 2 E ≤ r := by
  let e : G ≃* MulAut.innerSubgroup G := MonoidHom.ofInjective (conj_inj hz)
  by_cases hi : E ≤ MulAut.innerSubgroup G
  · let f : E →* G := e.symm.toMonoidHom.comp (Subgroup.inclusion hi)
    exact (primeRank_le_of_injective 2 f
      (e.symm.injective.comp (Subgroup.inclusion_injective hi))).trans hr
  obtain ⟨a, haE, ha⟩ := SetLike.not_le_iff_exists.mp hi
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haE
  let H := E.comap (MulAut.conj : G →* MulAut G)
  let : IsElementaryAbelian 2 H := {
    toIsMulCommutative := E.comap_injective_isMulCommutative (conj_inj hz)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      apply conj_inj hz
      change MulAut.conj (x.val ^ 2) = MulAut.conj (1 : G)
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian _ x.property) }
  have hHU : H ≤ U := by
    have hHN : H ≤ normalizer (U : Set G) := by
      intro x hx
      exact mem_normalizer_iff_map_conj_eq.mpr (hnorm _ hx)
    have h := (IsElementaryAbelian.isPGroup 2 H).inf_normalizer_sylow U
    rw [inf_eq_left.mpr hHN] at h
    exact h.le.trans inf_le_right
  have hHfix : H ≤ a.fixedSubgroup := by
    intro x hx
    rw [MulAut.mem_fixedSubgroup]
    apply conj_inj hz
    have hcomm : a * MulAut.conj x = MulAut.conj x * a :=
      setLike_mul_comm haE hx
    have hn : a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by ext y; simp
    rw [← hn, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hHC : Z ≤ centralizer (H : Set G) := by
    intro z hz
    exact mem_centralizer_iff.mpr (fun x hx => (hZc z hz x (hHU hx)).symm)
  let : IsElementaryAbelian 2 (H ⊔ Z : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hHC
  have hsup : Nat.card (H ⊔ Z : Subgroup G) ≤ 2 ^ r :=
    (primeRank_le_iff_elementary_card_le G).mp hr _ inferInstance
  have hcard : Nat.card H ≤ 2 ^ (r - 1) := by
    by_contra h
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 H).exists_card_eq
    have hbig : r - 1 < k := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      simpa only [hk] using Nat.lt_of_not_ge h
    have hlo : 2 ^ r ≤ Nat.card H := by
      rw [hk]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have heq : H = H ⊔ Z := Subgroup.eq_of_le_of_card_ge le_sup_left (hsup.trans hlo)
    exact hnonfix a ha2 ha (hnorm a haE) (le_sup_right.trans (heq.ge.trans hHfix))
  have hHr : primeRank 2 H ≤ r - 1 := IsElementaryAbelian.primeRank_le_of_card_le H hcard
  let π : E →* MulAut.Outer G :=
    (QuotientGroup.mk' (MulAut.innerSubgroup G)).comp E.subtype
  let j : π.ker →* MulAut.innerSubgroup G := {
    toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let k : π.ker →* G := e.symm.toMonoidHom.comp j
  have hk (x : π.ker) : MulAut.conj (k x) = x.val.val :=
    congrArg Subtype.val (e.apply_symm_apply (j x))
  let f : π.ker →* H := k.codRestrict H (fun x => by
    change MulAut.conj (k x) ∈ E
    rw [hk]
    exact x.val.property)
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : H => MulAut.conj z.val) h
    change MulAut.conj (k x) = MulAut.conj (k y) at hh
    rw [hk, hk] at hh
    exact Subtype.ext (Subtype.ext hh)
  have hker := (primeRank_le_of_injective 2 f hf).trans hHr
  let P : Sylow 2 (MulAut.Outer G) := Classical.choice inferInstance
  have ho : primeRank 2 (MulAut.Outer G) ≤ 1 := P.primeRank_le_one_of_isCyclic inferInstance
  have hb := primeRank_le_ker_add (p := 2) π
  omega

private theorem exists_normalized_elementary (U : Sylow 2 G)
    (E : Subgroup (MulAut G)) [IsElementaryAbelian 2 E] :
    ∃ F : Subgroup (MulAut G), IsElementaryAbelian 2 F ∧
      Nonempty (E ≃* F) ∧ ∀ a ∈ F, (U : Subgroup G).map a.toMonoidHom = U := by
  let : MulDistribMulAction E G := MulDistribMulAction.compHom G E.subtype
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 E).nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow 2 G) (not_dvd_card_sylow 2 G)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S U
  let b : MulAut G := MulAut.conj g
  let F := E.map (MulAut.conj b).toMonoidHom
  refine ⟨F, IsElementaryAbelian.map _, ⟨E.equivMapOfInjective _ (MulAut.conj b).injective⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hsa : a • S = S := hS ⟨a, ha⟩
  have hgu : b • S = U := hg
  have hf : (b * a * b⁻¹) • U = U := by
    rw [← hgu, mul_smul, mul_smul, inv_smul_smul, hsa]
  exact congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hf

private theorem rank_le_of_normalized (r : ℕ) (U : Sylow 2 G)
    (h : ∀ E : Subgroup (MulAut G), IsElementaryAbelian 2 E →
      (∀ a ∈ E, (U : Subgroup G).map a.toMonoidHom = U) → primeRank 2 E ≤ r) :
    primeRank 2 (MulAut G) ≤ r := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  obtain ⟨F, hF, ⟨e⟩, hn⟩ := exists_normalized_elementary U E
  have hr : primeRank 2 E ≤ r := by rw [primeRank_equiv 2 e]; exact h F hF hn
  let : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using
    (primeRank_le_iff_elementary_card_le E).mp hr ⊤ inferInstance

/-- A moved central elementary subgroup rules out a maximal-rank inner kernel. -/
theorem automorphism_twoRank_le_of_moved_central_bound (r : ℕ) (hrpos : 0 < r)
    (hz : center G = ⊥) [IsCyclic (MulAut.Outer G)] (hr : primeRank 2 G ≤ r)
    (U : Sylow 2 G) (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z)
    (hnonfix : ∀ a : MulAut G, a ^ 2 = 1 → a ∉ MulAut.innerSubgroup G →
      (U : Subgroup G).map a.toMonoidHom = U → ¬ Z ≤ a.fixedSubgroup) :
    primeRank 2 (MulAut G) ≤ r := by
  apply rank_le_of_normalized r U
  intro E hE hnorm
  let := hE
  exact normalized_rank_le r hrpos hz hr U Z hZc hnonfix E hnorm

/-- A moved central elementary subgroup rules out a maximal-rank inner kernel. -/
theorem automorphism_twoRank_le_of_moved_central
    (hz : center G = ⊥) [IsCyclic (MulAut.Outer G)] (hr : primeRank 2 G ≤ 10)
    (U : Sylow 2 G) (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z)
    (hnonfix : ∀ a : MulAut G, a ^ 2 = 1 → a ∉ MulAut.innerSubgroup G →
      (U : Subgroup G).map a.toMonoidHom = U → ¬ Z ≤ a.fixedSubgroup) :
    primeRank 2 (MulAut G) ≤ 10 :=
  automorphism_twoRank_le_of_moved_central_bound 10 (by decide) hz hr U Z hZc hnonfix

end Triality.Standard.TwoRank.FourSemilinear
