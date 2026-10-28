module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# Shared source geometry of the original central Hall actor

E.2.2 provides a cyclic group of order 2^f-1 in an odd Hall subgroup of
the actual H-star overlap, with f at least n(H)>1. Equality of Hall orders
therefore makes the prescribed B nontrivial. Odd order also makes B act
trivially on the pair of components, hence preserve the original moved
factor. Finally the Sylow-fixed subgroup of the elementary module lies
in Ω₁Z(T), so the centralizing-Z hypothesis fixes it pointwise.

These facts retain the literal source Hall subgroup. They do not assert
Borel placement, field-factor elimination, or any of the three row
calculations consumed in `HallGeometry.Source`.
Source: Aschbacher--Smith, 10.1.1--2 and the centralizing-Z branch of
10.2.3, printed pp.741--742 and 745, using E.2.2, pp.215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
include D c

/-- The Hall hypothesis gives odd order on the original carrier. -/
theorem hall_odd : Odd (Nat.card B) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  apply c.hall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
  rw [Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv]
  exact even_iff_two_dvd.mp he

/-- E.2.2 forces a nontrivial Mersenne divisor of this Hall subgroup's order. -/
theorem exists_mersenne_dvd_hall :
    ∃ f : ℕ, 1 < f ∧ 2 ^ f - 1 ∣ Nat.card B := by
  obtain ⟨hP,f,_hg,hf,d,he,_hp,_hx⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D c.hstar c.large
  have hh := d.hall
  rw [he] at hh
  have hcard := hh.card_eq c.hall
  rw [Nat.card_congr (subgroupOfEquivOfLe (he ▸ d.hall_le)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv] at hcard
  refine ⟨f,lt_of_lt_of_le c.large hf,?_⟩
  rw [← hcard, ← d.witness.card]
  exact card_dvd_of_le d.witness.cyclic_le

/-- In particular the source Hall group cannot be trivial. -/
theorem hall_card_ge_three : 3 ≤ Nat.card B := by
  obtain ⟨f,hf,hd⟩ := exists_mersenne_dvd_hall D c
  have hp : 4 ≤ 2 ^ f := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) (by omega)
  have hle := Nat.le_of_dvd (Nat.card_pos (α := B)) hd
  omega

theorem hall_ne_bot : B ≠ ⊥ := by
  intro he
  have hc := hall_card_ge_three D c
  rw [he, Subgroup.card_bot] at hc
  omega

/-- Triviality of the literal orbit-quotient action contradicts source generation. -/
theorem action_ne_one : action D B c.hall_le ≠ 1 := by
  intro he
  apply hall_ne_bot D c
  apply eq_bot_iff.mpr
  intro b hb
  have h1 : action D B c.hall_le (⟨b,hb⟩ : B) = action D B c.hall_le 1 := by
    rw [he]
    rfl
  have he1 := action_injective D B c.hall_le c.faithful h1
  exact mem_bot.mpr (congrArg Subtype.val he1)

/-- Odd order removes the component-exchange coordinate of the Hall action. -/
theorem hall_normalizes_component : B.map H.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let M := D.maximalLocal
  let C := B.map H.subtype
  let N := (normalizer (L : Set G)).subgroupOf M
  let A := C.subgroupOf M
  have hCM : C ≤ M := map_le_iff_le_comap.mpr c.hall_le
  have hi : N.index = 2 := normalizer_relIndex_eq_two_of_pair M L
    (L.map (MulAut.conj t).toMonoidHom)
    (source_nonnormal_maximal_pair D c.nonnormal ht htn) t
    (le_normalizer_componentOrbit L T ht)
    (fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he))
  let : N.Normal := normal_of_index_eq_two hi
  have hd : N.relIndex A ∣ 2 := hi ▸ N.relIndex_dvd_index_of_normal A
  have ho : Odd (Nat.card A) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv,
      card_map_of_injective H.subtype_injective]
    exact hall_odd D c
  have hle : A ≤ N := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes ho.coprime_two_right (N.relIndex_dvd_card A) hd)
  intro b hb
  exact hle (show (⟨b,hCM hb⟩ : M) ∈ A from hb)

/-- The same Hall group therefore preserves the original moved factor. -/
theorem hall_normalizes_moved :
    B.map H.subtype ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (map_le_iff_le_comap.mpr c.hall_le hb)),
    mem_normalizer_iff_map_conj_eq.mp (hall_normalizes_component D c hb)]


omit c in
/-- The original Sylow fixed subgroup of the full module lies in Z. -/
theorem module_fixed_le_omegaCenter (geometry : ModuleGeometry D) :
    D.fullModule ⊓ centralizer (T : Set G) ≤
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
  rw [geometry.full_eq_local]
  let := D.module_elementary
  intro v hv
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨D.module_le_sylow hv.1,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv.1, hv.2⟩

/-- The centralizing-Z source hypothesis fixes every original Sylow-fixed
module vector, before making any field or Cartan choice. -/
theorem hall_centralizes_module_fixed (geometry : ModuleGeometry D) :
    B.map H.subtype ≤ centralizer
      (D.fullModule ⊓ centralizer (T : Set G) : Set G) := by
  have hHZ : H ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact c.central)
  exact (map_subtype_le B).trans (hHZ.trans
    (centralizer_le (module_fixed_le_omegaCenter D geometry)))

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
