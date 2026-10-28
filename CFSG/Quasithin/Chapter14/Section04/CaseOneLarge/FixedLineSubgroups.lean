module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.Perm.Centralizer
/-!
# Recognizing the surviving coefficient subgroup of the original double

The even part of the faithful coefficient image is the original component
centralizer and has trivial two-core. A proper even subgroup containing a
Sylow four-group normalizes it, so the only possible nontrivial even orders
are six and ten. In either case the unique odd Sylow is characteristic.
The order-ten case would normalize a five-cycle subgroup, excluded by the
original elementary actor. In the order-six case the cubic normalizer
centralizes the transposition on its two fixed points; index two makes the
whole image exactly that transposition centralizer. Otherwise the image is
all of S₅.

This identifies literal subgroups and supplies coefficient isomorphisms
agreeing pointwise with the original projective map. It uses no recognition
by group order. The finite certificate checks only the normalizer of one
standard cubic, then transports by permutation conjugacy. The whole-action
splitting remains in FixedLineCoefficient.

The source consumer is FixedLineRecognition. Recognition of the module
in these two coefficient cases and of unmarked exchanged constituents is
still required for the full marked catalogue.
Source: Aschbacher--Smith G.11.8, printed pp.368--369, and 14.4.2,
printed pp.1006--1007; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSubgroups
private abbrev Five := Equiv.Perm (Fin 5)
private abbrev Alt := alternatingGroup (Fin 5)
private theorem alt_card : Nat.card Alt = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem even_card_cases (C : Subgroup Alt) (hc : pCore 2 C = ⊥)
    (he : 2 ∣ Nat.card C) : C = ⊤ ∨ Nat.card C = 6 ∨ Nat.card C = 10 := by
  by_cases htop : C = ⊤
  · exact Or.inl htop
  apply Or.inr
  have hb : Nat.card C ≤ 12 := by
    let : IsSimpleGroup Alt := alternatingGroup.isSimpleGroup (by simp)
    have hi : 5 ≤ C.index := by
      by_contra hn
      apply htop
      apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
      have hb := Nat.factorial_le (show C.index ≤ 4 by omega)
      rw [alt_card]
      norm_num [Nat.factorial] at hb ⊢
      omega
    have hh := C.card_mul_index
    rw [alt_card] at hh
    nlinarith
  have hd : Nat.card C ∣ 60 := alt_card ▸ C.card_subgroup_dvd_card
  have hfour : ¬ 4 ∣ Nat.card C := by
    intro hfour
    let S : Sylow 2 C := Classical.choice inferInstance
    have hS : Nat.card S = 4 := by
      rw [S.card_eq_multiplicity]
      have hcases : Nat.card C = 4 ∨ Nat.card C = 12 := by
        generalize Nat.card C = n at *
        interval_cases n <;> omega
      rcases hcases with h | h <;> rw [h] <;> decide +kernel
    let P : Sylow 2 Alt := Sylow.ofCard ((S : Subgroup C).map C.subtype) (by
      rw [←Nat.card_congr ((S : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toEquiv,
        hS,alt_card]
      decide +kernel)
    have hPC : (P : Subgroup Alt) ≤ C := by
      rintro _ ⟨x,hx,rfl⟩
      exact x.property
    have hn := alternatingGroup.proper_sylow_overgroup_le_normalizer P C htop hPC
    let : (S : Subgroup C).Normal := by
      refine ⟨?_⟩
      intro x hx g
      have hh := (hn g.property x.val).mp (show x.val ∈ P from ⟨x,hx,rfl⟩)
      obtain ⟨y,hy,he⟩ := hh
      have hyx : y = g*x*g⁻¹ := Subtype.ext he
      exact hyx ▸ hy
    have hle : (S : Subgroup C) ≤ pCore 2 C := le_sSup ⟨inferInstance,S.isPGroup'⟩
    have hz : (S : Subgroup C) = ⊥ := bot_unique (hc ▸ hle)
    have h1 : Nat.card S = 1 := by rw [hz,card_bot]
    omega
  have htwo : Nat.card C ≠ 2 := by
    intro h2
    have hp : IsPGroup 2 C := IsPGroup.of_card (n := 1) (by simpa using h2)
    have ht : (⊤ : Subgroup C) ≤ pCore 2 C := le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩
    have hz : (⊤ : Subgroup C) = ⊥ := bot_unique (hc ▸ ht)
    have hh := congrArg (fun Q : Subgroup C => Nat.card Q) hz
    rw [card_top,card_bot,h2] at hh
    omega
  generalize Nat.card C = n at *
  interval_cases n <;> omega

private theorem even_index (B : Subgroup Five) (ho : ¬ B ≤ Alt) :
    Nat.card B = 2 * Nat.card (B ⊓ Alt : Subgroup Five) := by
  let f := Equiv.Perm.sign.comp B.subtype
  have hf : Function.Surjective f := by
    obtain ⟨b,hb,hbodd⟩ : ∃ b, b ∈ B ∧ b ∉ Alt := by
      by_contra! hh
      exact ho (fun b hb => hh b hb)
    have hs : Equiv.Perm.sign b = -1 := (Int.units_eq_one_or _).resolve_left
      (fun hh => hbodd (Equiv.Perm.mem_alternatingGroup.mpr hh))
    intro z
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1,f.map_one⟩
    · exact ⟨⟨b,hb⟩,hs⟩
  have hk : f.ker.map B.subtype = B ⊓ Alt := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property,Equiv.Perm.mem_alternatingGroup.mpr hb⟩
    · rintro ⟨hb,hs⟩
      exact ⟨⟨x,hb⟩,Equiv.Perm.mem_alternatingGroup.mp hs,rfl⟩
  have hh := f.ker.card_mul_index
  rw [index_ker,(MonoidHom.range_eq_top.mpr hf),card_top] at hh
  have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
  have hc : Nat.card f.ker = Nat.card (B ⊓ Alt : Subgroup Five) := by
    rw [←hk,card_map_of_injective B.subtype_injective]
  rw [htwo,hc] at hh
  omega

private theorem odd_normal_subgroup (C : Subgroup Five) (p : ℕ)
    (hp : p=3 ∨ p=5) (hc : Nat.card C = 2*p) :
    ∃ R : Subgroup Five, Nat.card R = p ∧
      normalizer (C : Set Five) ≤ normalizer (R : Set Five) := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  let P : Sylow p C := Classical.choice inferInstance
  have hP : Nat.card P = p := by
    rw [P.card_eq_multiplicity,hc]
    rcases hp with rfl | rfl <;> decide +kernel
  have hi : (P : Subgroup C).index = 2 := by
    have hh := (P : Subgroup C).card_mul_index
    rw [hP,hc] at hh
    rcases hp with rfl | rfl <;> omega
  let : (P : Subgroup C).Normal := normal_of_index_eq_two hi
  let : (P : Subgroup C).Characteristic := P.characteristic_of_normal inferInstance
  exact ⟨(P : Subgroup C).map C.subtype,
    (card_map_of_injective C.subtype_injective).trans hP,
    normalizer_le_normalizer_characteristic_image C (P : Subgroup C)⟩

private def standardCubic : Five := Equiv.swap 0 1 * Equiv.swap 1 2
private def standardSwap : Five := Equiv.swap 3 4

private theorem cubic_certificate : ∀ g : Five,
    (g*standardCubic*g⁻¹=standardCubic ∨ g*standardCubic*g⁻¹=standardCubic^2) →
      g*standardSwap=standardSwap*g := by
  decide +kernel

private theorem cubic_centralizing_swap (y : Five) (ho : orderOf y = 3) :
    ∃ t : Five, t.IsSwap ∧ ∀ g : Five,
      (g*y*g⁻¹=y ∨ g*y*g⁻¹=y^2) → g*t=t*g := by
  have hyc : y.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (ho ▸ (by decide : Nat.Prime 3)) (by rw [ho]; decide)
  have htype : y.cycleType = standardCubic.cycleType := by
    rw [hyc.cycleType,←hyc.orderOf,ho]
    decide +kernel
  obtain ⟨s,hs⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr htype)
  let e := MulAut.conj s
  have hey : e y = standardCubic := hs
  refine ⟨e.symm standardSwap,?_,?_⟩
  · change (s⁻¹ * Equiv.swap 3 4 * s).IsSwap
    rw [Equiv.mul_swap_eq_swap_mul]
    simp only [inv_mul_cancel_right]
    exact Equiv.Perm.swap_isSwap_iff.mpr (s.symm.injective.ne (by decide))
  · intro g hg
    apply e.injective
    simp only [map_mul,e.apply_symm_apply]
    apply cubic_certificate
    rcases hg with hg | hg
    · left
      have hh := congrArg e hg
      simpa only [map_mul,map_inv,hey] using hh
    · right
      have hh := congrArg e hg
      simpa only [map_mul,map_inv,map_pow,hey] using hh

private theorem cubic_normalizer (R : Subgroup Five) (hR : Nat.card R = 3) :
    ∃ t : Five, t.IsSwap ∧ normalizer (R : Set Five) ≤ centralizer ({t} : Set Five) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 (by rw [hR])
  have ho : orderOf (y : Five) = 3 := (orderOf_injective R.subtype R.subtype_injective y).trans hy
  have hn : (y : Five) ≠ 1 := by intro he; rw [he,orderOf_one] at ho; omega
  have hz : zpowers (y : Five) = R := eq_of_le_of_card_ge (zpowers_le.mpr y.property)
    (by rw [Nat.card_zpowers,ho,hR])
  obtain ⟨t,ht,hcomm⟩ := cubic_centralizing_swap y ho
  refine ⟨t,ht,?_⟩
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  apply hcomm
  have hcon : g*(y : Five)*g⁻¹ ∈ zpowers (y : Five) :=
    hz.symm ▸ (mem_normalizer_iff.mp hg y).mp y.property
  have hr : ∃ i : Fin 3, (y : Five)^i.val = g*y*g⁻¹ := by
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hcon)
    have hi3 : i < 3 := by simpa only [Finset.mem_range,ho] using hi
    exact ⟨⟨i,hi3⟩,he⟩
  obtain ⟨i,hi⟩ := hr
  fin_cases i
  · have hh : g*(y : Five)*g⁻¹ = 1 := hi.symm
    exact (hn ((MulAut.conj g).injective (hh.trans (map_one (MulAut.conj g)).symm))).elim
  · exact Or.inl (by simpa using hi.symm)
  · exact Or.inr hi.symm

/-- The surviving coefficient subgroup is the full S₅ or the literal
centralizer of a transposition. The latter conclusion retains its embedding. -/
private theorem coefficient_subgroup (B : Subgroup Five)
    (hc : pCore 2 (B ⊓ Alt : Subgroup Five) = ⊥)
    (ho : ¬ B ≤ Alt) (hfour : 4 ∣ Nat.card B)
    (hfive : ∀ P : Sylow 5 Five, ¬ B ≤ normalizer ((P : Subgroup Five) : Set Five)) :
    B = ⊤ ∨ ∃ t : Five, t.IsSwap ∧ B = centralizer ({t} : Set Five) := by
  let C := B ⊓ Alt
  let E := C.subgroupOf Alt
  have hCA : C ≤ Alt := inf_le_right
  have hEC : E ≃* C := subgroupOfEquivOfLe hCA
  have hcard := even_index B ho
  change Nat.card B = 2 * Nat.card C at hcard
  have hcore : pCore 2 E = ⊥ := by
    rw [←pCore_map_iso 2 hEC.symm,hc,Subgroup.map_bot]
  have heven : 2 ∣ Nat.card E := by
    rw [Nat.card_congr hEC.toEquiv]
    omega
  have hnormal : B ≤ normalizer (C : Set Five) :=
    le_normalizer_iff.mpr (by
      intro b hb x hx
      exact ⟨B.mul_mem (B.mul_mem hb hx.1) (B.inv_mem hb),
        (inferInstance : Alt.Normal).conj_mem x hx.2 b⟩)
  rcases even_card_cases E hcore heven with ht | hs | hf
  · left
    have hECcard : Nat.card C = 60 := by
      rw [←Nat.card_congr hEC.toEquiv,ht,card_top,alt_card]
    apply eq_top_of_card_eq
    rw [hcard,hECcard]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · right
    have hC : Nat.card C = 6 := by rwa [Nat.card_congr hEC.toEquiv] at hs
    obtain ⟨R,hR,hRN⟩ := odd_normal_subgroup C 3 (Or.inl rfl) (by simpa using hC)
    obtain ⟨t,ht,hN⟩ := cubic_normalizer R hR
    refine ⟨t,ht,eq_of_le_of_card_ge (hnormal.trans (hRN.trans hN)) ?_⟩
    rw [hcard,hC,Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp ht]
    norm_num [Nat.factorial]
  · have hC : Nat.card C = 10 := by rwa [Nat.card_congr hEC.toEquiv] at hf
    obtain ⟨R,hR,hRN⟩ := odd_normal_subgroup C 5 (Or.inr rfl) (by simpa using hC)
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let P : Sylow 5 Five := Sylow.ofCard R (by
      rw [hR,Nat.card_eq_fintype_card,Fintype.card_perm]
      decide +kernel)
    exact (hfive P (hnormal.trans hRN)).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSubgroups

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineSubgroups
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
  {H : Subgroup D} (a : Coordinates ρ H)

/-- Classify the actual coefficient image of the original doubled action. -/
theorem coefficientFive_image
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (hc : pCore 2 D = ⊥)
    (X : Subgroup D) [IsElementaryAbelian 2 X]
    (v : W) (hv : v ≠ 0)
    (hf : Representation.BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hY : Nat.card ((centralizer (H : Set D)).subgroupOf X) = 2) :
    a.coefficientFive.range = ⊤ ∨ ∃ t : Equiv.Perm (Fin 5),
      t.IsSwap ∧ a.coefficientFive.range = centralizer ({t} : Set (Equiv.Perm (Fin 5))) := by
  apply coefficient_subgroup _ (a.coefficientFive_even_twoCore B hnd hB hc)
  · intro he
    obtain ⟨x,hx⟩ := a.actor_field_nontrivial X v hv hf
    exact hx ((a.ambientFive_even_iff x).mp (he ⟨a.coefficient.rangeRestrict x,(a.ambientFive_apply x).symm⟩))
  · rw [←a.actor_five_card B hnd hB X v hv hf hY]
    apply card_dvd_of_le
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨a.coefficient.rangeRestrict x,(a.ambientFive_apply x).symm⟩
  · exact a.coefficientFive_not_le_fiveNormalizer B hnd hB X v hv hf hY

/-- The coefficient image recognition supplies actual isomorphisms whose
underlying permutations are the original coefficient map. -/
theorem coefficientFive_models
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (hc : pCore 2 D = ⊥)
    (X : Subgroup D) [IsElementaryAbelian 2 X]
    (v : W) (hv : v ≠ 0)
    (hf : Representation.BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hY : Nat.card ((centralizer (H : Set D)).subgroupOf X) = 2) :
    (∃ e : a.coefficient.range ≃* Equiv.Perm (Fin 5), ∀ b, e b = a.coefficientFive b) ∨
      (∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
        ∃ e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))),
          ∀ b, (e b).val = a.coefficientFive b) := by
  have hi := a.coefficientFive_injective B hnd hB
  rcases a.coefficientFive_image B hnd hB hc X v hv hf hY with he | ⟨t,ht,he⟩
  · exact Or.inl ⟨MulEquiv.ofBijective a.coefficientFive
      ⟨hi,MonoidHom.range_eq_top.mp he⟩,fun _ => rfl⟩
  · exact Or.inr ⟨t,ht,(MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr he),fun _ => rfl⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
