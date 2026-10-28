module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.OriginalAction
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup

/-!
# Cubic fixed points in the original marked A₅ module

A cube-one permutation on five letters has at least two fixed letters, by
the orbit congruence modulo three. Their complement vectors span a plane in
the actual binary augmentation core, giving at least four fixed vectors.
This includes the identity permutation; no faithfulness of a cubic actor
is required.

For the marked quotient A → A/⟨z⟩, every lift of a fixed vector is fixed:
its displacement lies in the fixed kernel of exponent two, whereas the
conjugating automorphism has cube one. The quotient has order sixteen and
the kernel order two, so |A|=32 and at least eight elements of A are fixed.
Since the elementary group D=A⟨i⟩ has order 64 and the residual centralizes
i, adjoining i doubles this bound. The final theorem has exactly the
fixed-point contract consumed by `swaps_of_original_cubic_bound`.

The earlier coordinate marking remains explicit. This proves the cubic
calculation, not the earlier construction of that marking or the whole
source lemma.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

noncomputable section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel

private theorem cube_has_two_fixed_letters (g : Equiv.Perm (Fin 5)) (hg : g ^ 3 = 1) :
    ∃ a b : Fin 5, a ≠ b ∧ g a = a ∧ g b = b := by
  let P := zpowers g
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hP : IsPGroup 3 P := isPGroup_iff_card_dvd_pow.mpr ⟨1, by
    simpa only [P, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hg⟩
  have hc := hP.card_modEq_card_fixedPoints (Fin 5)
  have htwo : 1 < Nat.card (MulAction.fixedPoints P (Fin 5)) := by
    have he : 5 % 3 = Nat.card (MulAction.fixedPoints P (Fin 5)) % 3 := by
      simpa only [Nat.ModEq, Nat.card_eq_fintype_card, Fintype.card_fin] using hc
    omega
  let : Nontrivial (MulAction.fixedPoints P (Fin 5)) :=
    Finite.one_lt_card_iff_nontrivial.mp htwo
  obtain ⟨a,b,hab⟩ := exists_pair_ne (MulAction.fixedPoints P (Fin 5))
  exact ⟨a,b,fun he => hab (Subtype.ext he),
    a.property ⟨g,mem_zpowers g⟩, b.property ⟨g,mem_zpowers g⟩⟩

private def five_point_complement (a : Fin 5) : core (Fin 5) :=
  ⟨fun j => 1 - (Pi.single a 1 : Fin 5 → ZMod 2) j, by
    rw [mem_core, Finset.sum_sub_distrib]
    norm_num [Finset.sum_pi_single]
    decide⟩

private theorem five_point_complement_apply (a j : Fin 5) :
    (five_point_complement a).val j = if j = a then 0 else 1 := by
  by_cases h : j = a
  · subst j; simp [five_point_complement]
  · simp [five_point_complement, Pi.single_apply, h]

private theorem five_point_complement_fixed (g : Equiv.Perm (Fin 5)) (a : Fin 5)
    (ha : g a = a) : coreRepresentation (Fin 5) g (five_point_complement a) = five_point_complement a := by
  apply Subtype.ext
  ext j
  change (five_point_complement a).val (g.symm j) = (five_point_complement a).val j
  rw [five_point_complement_apply, five_point_complement_apply]
  have he : g.symm j = a ↔ j = a := by
    rw [Equiv.symm_apply_eq, ha]
  simp only [he]

private theorem cube_core_fixed_card (g : Equiv.Perm (Fin 5)) (hg : g ^ 3 = 1) :
    4 ≤ Nat.card {v : core (Fin 5) // coreRepresentation (Fin 5) g v = v} := by
  obtain ⟨a,b,hab,ha,hb⟩ := cube_has_two_fixed_letters g hg
  let f : ZMod 2 × ZMod 2 →
      {v : core (Fin 5) // coreRepresentation (Fin 5) g v = v} := fun p =>
    ⟨p.1 • five_point_complement a + p.2 • five_point_complement b, by
      rw [map_add, map_smul, map_smul, five_point_complement_fixed g a ha, five_point_complement_fixed g b hb]⟩
  have hinj : Function.Injective f := by
    intro p q he
    have h1 := congrArg (fun v => v.val.val b) he
    have h2 := congrArg (fun v => v.val.val a) he
    apply Prod.ext
    · simpa [f, five_point_complement_apply, hab, Ne.symm hab] using h1
    · simpa [f, five_point_complement_apply, hab, Ne.symm hab] using h2
  have hc := Nat.card_le_card_of_injective f hinj
  simpa only [Nat.card_prod, Nat.card_zmod] using hc

private theorem cubic_fixed_of_kernel_fixed
    {P Q : Type*} [Group P] [Group Q] (f : P →* Q) (a : MulAut P)
    (ha : a ^ 3 = 1) (hfix : ∀ c ∈ f.ker, a c = c)
    (hsq : ∀ c ∈ f.ker, c ^ 2 = 1)
    (x : P) (hx : f (a x) = f x) : a x = x := by
  let c := x⁻¹ * a x
  have hc : c ∈ f.ker := by
    change f (x⁻¹ * a x) = 1
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  have hax : a x = x * c := by simp [c]
  have haa : a (a x) = x := by
    calc
      a (a x) = a (x * c) := congrArg a hax
      _ = a x * c := by rw [map_mul, hfix c hc]
      _ = x * (c * c) := by rw [hax, mul_assoc]
      _ = x := by rw [← pow_two, hsq c hc, mul_one]
  have hh := DFunLike.congr_fun ha x
  simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, haa] using hh


variable {G : Type*} [Group G] [Finite G]

/-- Every cubic element of the original residual fixes at least sixteen elements
of the literal common lift. This supplies the `hfix` premise of
`swaps_of_original_cubic_bound`, with the earlier module marking still explicit. -/
public theorem OriginalMovedAction.sixteen_le_fixed_card
    {U : Subgroup G} {z i : G} (d : OriginalMovedAction U z i)
    (hz : orderOf z = 2) (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hDcard : Nat.card (centralizerLift U z i) = 64)
    (k : diagonalResidual (centralizer ({z} : Set G)) i) (hk : orderOf k = 3) :
    16 ≤ Nat.card (centralizerLift U z i ⊓ centralizer ({(k:G)} : Set G) : Subgroup G) := by
  let A := liftBase U z i
  let D := centralizerLift U z i
  let B := Multiplicative (BinaryPermutation.core (Fin 5))
  let q : A →* B := d.quotient
  let : IsElementaryAbelian 2 D := hD
  have hDA : D = A ⊔ zpowers i := by
    dsimp [D,A,centralizerLift,liftBase]
    ac_rfl
  have hAD : A ≤ D := hDA ▸ le_sup_left
  have hiD : i ∈ D := hDA ▸ mem_sup_right (mem_zpowers i)
  have hZA : zpowers z ≤ A := le_sup_right
  have hker : Nat.card q.ker = 2 := by
    rw [d.kernel, Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, Nat.card_zpowers, hz]
  have hB : Nat.card B = 16 := by
    change Nat.card (BinaryPermutation.core (Fin 5)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      BinaryPermutation.finrank_core]
    rfl
  have hA : Nat.card A = 32 := by
    have hh := q.ker.index_mul_card
    rw [index_ker, MonoidHom.range_eq_top.mpr d.surjective, card_top, hB, hker] at hh
    exact hh.symm
  have hKC : diagonalResidual (centralizer ({z} : Set G)) i ≤
      centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G) := map_subtype_le _
  have hkz : (k:G) ∈ centralizer ({z} : Set G) := (hKC k.property).1
  have hki : (k:G) ∈ centralizer ({i} : Set G) := (hKC k.property).2
  have hk3 : k ^ 3 = 1 := hk ▸ pow_orderOf_eq_one k
  let n : normalizer (A : Set G) := ⟨k,d.normalizes k.property⟩
  let a : MulAut A := A.normalizerMonoidHom n
  have ha3 : a ^ 3 = 1 := by
    have hn : n ^ 3 = 1 := Subtype.ext (congrArg (fun r : diagonalResidual (centralizer ({z} : Set G)) i => (r:G)) hk3)
    change (A.normalizerMonoidHom n) ^ 3 = 1
    rw [← map_pow, hn, map_one]
  have hkerfix : ∀ c ∈ q.ker, a c = c := by
    intro c hc
    have hcz : (c:G) ∈ zpowers z := by
      change c ∈ d.quotient.ker at hc
      rw [d.kernel] at hc
      exact hc
    have hzc : zpowers z ≤ centralizer ({(k:G)} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hkz).symm)
    apply Subtype.ext
    change (k:G) * (c:G) * (k:G)⁻¹ = (c:G)
    rw [← mem_centralizer_singleton_iff.mp (hzc hcz), mul_inv_cancel_right]
  have hkersq : ∀ c ∈ q.ker, c ^ 2 = 1 := by
    intro c _
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A := D) c (hAD c.property)
  let g : Equiv.Perm (Fin 5) := (d.actor k).val
  have hg : g ^ 3 = 1 := by
    change (alternatingGroup (Fin 5)).subtype (d.actor k) ^ 3 = 1
    rw [← map_pow, ← map_pow, hk3, map_one, map_one]
  let t : B →* B := AddMonoidHom.toMultiplicative
    (BinaryPermutation.coreRepresentation (Fin 5) g).toAddMonoidHom
  let F : Subgroup B := t.eqLocus (MonoidHom.id B)
  have hF : 4 ≤ Nat.card F := by
    let e : F ≃ {v : BinaryPermutation.core (Fin 5) //
        BinaryPermutation.coreRepresentation (Fin 5) g v = v} :=
      { toFun v := ⟨v.val.toAdd,v.property⟩
        invFun v := ⟨Multiplicative.ofAdd v.val,v.property⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Nat.card_congr e]
    exact cube_core_fixed_card g hg
  let C := (centralizer ({(k:G)} : Set G)).subgroupOf A
  have hC : C = F.comap q := by
    ext v
    constructor
    · intro hv
      have he : a v = v := by
        apply Subtype.ext
        change (k:G) * (v:G) * (k:G)⁻¹ = (v:G)
        have hv' : (v:G) ∈ centralizer ({(k:G)} : Set G) := hv
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hv').symm
      change t (q v) = q v
      exact (d.equivariant k v).symm.trans (congrArg q he)
    · intro hv
      change t (q v) = q v at hv
      have he := cubic_fixed_of_kernel_fixed q a ha3 hkerfix hkersq v
        ((d.equivariant k v).trans hv)
      have he' : (k:G) * (v:G) * (k:G)⁻¹ = (v:G) := congrArg Subtype.val he
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he').symm
  have hCindex : C.index = F.index := by rw [hC, index_comap_of_surjective F d.surjective]
  have hFindex : F.index ≤ 4 := by
    have hh := F.card_mul_index
    rw [hB] at hh
    nlinarith
  have hCcard : 8 ≤ Nat.card C := by
    have hh := C.card_mul_index
    rw [hCindex, hA] at hh
    nlinarith
  let E := A ⊓ centralizer ({(k:G)} : Set G)
  have hEcard : 8 ≤ Nat.card E := by
    have he : Nat.card C = Nat.card E := by
      simpa only [C, E, inf_subgroupOf_left] using
        Nat.card_congr (subgroupOfEquivOfLe (show E ≤ A from inf_le_left)).toEquiv
    rwa [he] at hCcard
  have hiA : i ∉ A := by
    intro hi
    have he : D = A := by rw [hDA, sup_eq_left.mpr (zpowers_le.mpr hi)]
    have hh : Nat.card D = 64 := hDcard
    rw [he, hA] at hh
    omega
  have hi2 : i ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := D) i hiD
  have hiord : orderOf i = 2 := orderOf_eq_prime hi2 (fun he => hiA (he ▸ A.one_mem))
  have hdis : Disjoint E (zpowers i) := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro v hv
    classical
    have hzv := (isOfFinOrder_of_finite i).mem_zpowers_iff_mem_range_orderOf.mp hv.2
    rw [hiord] at hzv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hzv
    have hj2 := Finset.mem_range.mp hj
    interval_cases j
    · simp
    · exact (hiA (by simpa using hv.1.1)).elim
  have hInorm : zpowers i ≤ normalizer (E : Set G) :=
    (((zpowers_le.mpr hiD).trans D.le_centralizer).trans
      (centralizer_le (show E ≤ D from inf_le_left.trans hAD))).trans
        (_root_.centralizer_le_normalizer _)
  have hcount := card_sup_eq_mul_of_normalizes_of_disjoint E (zpowers i) hInorm hdis
  rw [Nat.card_zpowers, hiord] at hcount
  have hjoin : E ⊔ zpowers i ≤ D ⊓ centralizer ({(k:G)} : Set G) := by
    apply sup_le
    · exact le_inf (inf_le_left.trans hAD) inf_le_right
    · exact le_inf (zpowers_le.mpr hiD) (zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hki).symm))
  have hb := card_le_of_le hjoin
  rw [hcount] at hb
  change 16 ≤ Nat.card (D ⊓ centralizer ({(k:G)} : Set G) : Subgroup G)
  omega

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
