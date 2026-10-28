module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation

/-!
# The literal quotient in the root-four five-local branch

For an order-five subgroup E, the kernel E ∩ C_G(E) is all of E and is
central in C_G(E). The order-25 Sylow subgroup containing E lies in C_G(E),
so the literal quotient C_G(E)/E has order divisible by five.

The marked 47.1 model also places E in the A₅ component of C_G(t), and
therefore the selected cubic subgroup D.X centralizes E. The root four-group
lies in C_G(E) but is not normal there: otherwise 25 would divide its
normalizer's order 720. These are source inputs to quotient recognition,
not assumptions of that recognition's intended application.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent

variable {G : Type*} [Group G] [Finite G]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The source kernel E, expressed without a premature abelianness assumption. -/
def kernel (E : Subgroup G) : Subgroup (centralizer (E : Set G)) :=
  E.subgroupOf (centralizer (E : Set G))

/-- The kernel is normal in the centralizer, not in the ambient simple group. -/
instance kernel_normal (E : Subgroup G) : (kernel E).Normal :=
  normal_subgroupOf_of_le_normalizer (centralizer_le_normalizer (E : Set G))

omit [Finite G] in
/-- The quotient kernel is central in its literal domain. -/
theorem kernel_le_center (E : Subgroup G) : kernel E ≤ center (centralizer (E : Set G)) := by
  intro x hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact (y.property x hx).symm

/-- The literal centralizer quotient M/E from the source proof. -/
abbrev Quotient (E : Subgroup G) := centralizer (E : Set G) ⧸ kernel E

omit [Finite G] in
/-- An order-five subgroup is abelian and centralizes itself. -/
theorem five_le_centralizer (E : Subgroup G) (hE : Nat.card E = 5) :
    E ≤ centralizer (E : Set G) := by
  let : IsCyclic E := isCyclic_of_prime_card hE
  exact le_centralizer_iff_isMulCommutative.mpr inferInstance

omit [Finite G] in
/-- No subgroup is lost when E is restricted to its centralizer. -/
theorem kernel_card (E : Subgroup G) (hE : Nat.card E = 5) : Nat.card (kernel E) = 5 := by
  exact (Nat.card_congr (subgroupOfEquivOfLe (five_le_centralizer E hE)).toEquiv).trans hE

/-- An abelian Sylow five-subgroup containing E lies in C_G(E). -/
theorem twenty_five_dvd_centralizer_card (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : Nat.card E = 5) :
    25 ∣ Nat.card (centralizer (E : Set G)) := by
  have hp : IsPGroup 5 E := IsPGroup.of_card (n := 1) (by simpa using hE)
  obtain ⟨P, hEP⟩ := hp.exists_le_sylow
  have hd := card_dvd_of_le (sylow_le_centralizer hG P E hEP)
  rwa [sylow_card hG P] at hd

/-- One factor of five survives passage from C_G(E) to C_G(E)/E. -/
theorem five_dvd_quotient_card (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : Nat.card E = 5) : 5 ∣ Nat.card (Quotient E) := by
  have hd := twenty_five_dvd_centralizer_card hG E hE
  rw [card_eq_card_quotient_mul_card_subgroup (kernel E), kernel_card E hE] at hd
  exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 5)).mp hd

/-- The marked normalizer from 47.1 has order 720. -/
theorem root_normalizer_card {D : Seed G} (S : InvolutionGeometry.SelectedGeometry D) :
    Nat.card (normalizer (InvolutionGeometry.rootCore S.t : Set G)) = 720 := by
  rw [Nat.card_congr S.normalizerEquiv.toEquiv, Nat.card_prod,
    InvolutionGeometry.card_A5, nat_card_alternatingGroup]
  norm_num

/-- The five-centralizer cannot normalize the source root four-group. -/
theorem centralizer_not_le_root_normalizer {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : Nat.card E = 5) :
    ¬ centralizer (E : Set G) ≤ normalizer (InvolutionGeometry.rootCore S.t : Set G) := by
  intro h
  have hd := (twenty_five_dvd_centralizer_card hG E hE).trans (card_dvd_of_le h)
  rw [root_normalizer_card S] at hd
  norm_num at hd

/-- The original root four-group lies in the five-centralizer. -/
theorem rootCore_le_centralizer {D : Seed G} {t : G}
    (C : InvolutionGeometry.SecondCentralizer D t)
    (E : Subgroup G) (hEt : E ≤ involutionCentralizer t) :
    InvolutionGeometry.rootCore t ≤ centralizer (E : Set G) := by
  intro u hu x hx
  exact (C.centralizer_le_core_centralizer (hEt hx) u hu).symm

/-- Relative nonnormality inside C_G(E), as required by the source route. -/
theorem rootCore_not_normal {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) :
    ¬ ((InvolutionGeometry.rootCore S.t).subgroupOf (centralizer (E : Set G))).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (rootCore_le_centralizer S.model E hEt)]
  exact centralizer_not_le_root_normalizer S hG E hE

/-- The root involution regarded as an element of the literal five-centralizer. -/
def rootInCentralizer (E : Subgroup G) (t : G) (hEt : E ≤ involutionCentralizer t) :
    centralizer (E : Set G) :=
  ⟨t, fun _ hx => mem_centralizer_singleton_iff.mp (hEt hx)⟩

/-- The same root involution in the actual quotient by E. -/
def rootInQuotient (E : Subgroup G) (t : G) (hEt : E ≤ involutionCentralizer t) : Quotient E :=
  QuotientGroup.mk' (kernel E) (rootInCentralizer E t hEt)

omit [Finite G] in
/-- The involution survives the odd quotient kernel. -/
theorem rootInQuotient_order (E : Subgroup G) (hE : Nat.card E = 5)
    (t : G) (ht : orderOf t = 2) (hEt : E ≤ involutionCentralizer t) :
    orderOf (rootInQuotient E t hEt) = 2 := by
  apply orderOf_eq_prime
  · change (QuotientGroup.mk' (kernel E) (rootInCentralizer E t hEt)) ^ 2 = 1
    rw [← map_pow]
    have hs : rootInCentralizer E t hEt ^ 2 = 1 := by
      apply Subtype.ext
      exact ht ▸ pow_orderOf_eq_one t
    rw [hs, map_one]
  · intro he
    have hm : rootInCentralizer E t hEt ∈ kernel E := by
      rw [← QuotientGroup.ker_mk' (kernel E)]
      exact he
    have hd := orderOf_dvd_natCard (⟨t, hm⟩ : E)
    rw [← orderOf_coe, ht, hE] at hd
    norm_num at hd

/-- An order-five subgroup of E₄ × A₅ lies in the specified A₅ factor. -/
theorem five_le_fiveFactor {D : Seed G} {t : G}
    (C : InvolutionGeometry.SecondCentralizer D t)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer t) :
    E ≤ C.fiveFactor := by
  intro x hx
  let xE : E := ⟨x, hx⟩
  let xC : involutionCentralizer t := ⟨x, hEt hx⟩
  have hx5 : xC ^ 5 = 1 := by
    apply Subtype.ext
    have hh := pow_card_eq_one' (x := xE)
    rw [hE] at hh
    exact congrArg (fun y : E => (y : G)) hh
  have h5 : (C.equiv xC).1 ^ 5 = 1 := by
    simpa only [map_pow, map_one, Prod.pow_fst, Prod.fst_one] using
      congrArg (fun y => (C.equiv y).1) hx5
  have hs : ∀ a : InvolutionGeometry.E4, a ^ 2 = 1 := by decide +kernel
  have hfive (a : InvolutionGeometry.E4) : a ^ 5 = a := by
    rw [show 5 = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hs, one_mul]
  have h1 : (C.equiv xC).1 = 1 := by
    rwa [hfive] at h5
  refine ⟨C.equiv xC, ⟨h1, mem_top _⟩, ?_⟩
  simp [InvolutionGeometry.SecondCentralizer.embedding, xC]

/-- The chosen source cubic subgroup belongs to the five-centralizer. -/
theorem seed_le_centralizer {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) :
    D.X ≤ centralizer (E : Set G) := by
  have hEC : E ≤ InvolutionGeometry.rootComponent S.t := by
    rw [S.component_eq]
    exact five_le_fiveFactor S.model E hE hEt
  exact S.X_centralizes_component.trans (centralizer_le hEC)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
