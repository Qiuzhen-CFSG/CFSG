module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Transfer

/-!
# Involutions and transfer in the original single-block setup

The chosen torus normalizer complements R in T. A nonidentity element
of that two-group complement supplies an involution outside R. Given
original 2.4.21(2), generalized Thompson transfer therefore makes T/R
noncyclic. The original index-two row then yields R < S, and the split
extension S = RF supplies the marked field-complement involution.

The final consumer records precisely the centralizer quotient and fusion
containment established on printed pp.538–539. It constructs the original
tori and the marked involution, then applies transfer with the two earlier
source families explicit. Source: Aschbacher–Smith, combined manuscript
of 1 March 2004, Lemma 2.4.22 and the final single-block argument.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- The cyclic complement identifies the actual quotient S/R. -/
theorem CyclicTorusSetup.sylow_quotient_cyclic
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ} (c : CyclicTorusSetup d T n)
    [((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf
      ((d.S : Subgroup d.H).map d.H.subtype)).Normal] :
    IsCyclic (((d.S : Subgroup d.H).map d.H.subtype) ⧸
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf
        ((d.S : Subgroup d.H).map d.H.subtype))) := by
  let : IsCyclic ((((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G)).subgroupOf
      ((d.S : Subgroup d.H).map d.H.subtype)) : Subgroup ((d.S : Subgroup d.H).map d.H.subtype)) :=
    (subgroupOfEquivOfLe inf_le_left).isCyclic.mpr c.field_cyclic
  exact c.split_sylow.symm.QuotientMulEquiv.isCyclic.mpr inferInstance

/-- The literal data used by the final transfer on printed p.539.
The source constructs `kernel` as the centralizer in T of the marked Z. -/
structure TerminalTransferSetup (d : MinimalBlockSetup M) (T : Sylow 2 G) (s : T) where
  kernel : Subgroup T
  normal : kernel.Normal
  cyclic : letI := normal; IsCyclic (T ⧸ kernel)
  intersection : kernel ⊓ (((d.S : Subgroup d.H).map d.H.subtype).subgroupOf (T : Subgroup G)) =
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf (T : Subgroup G))
  fusion : ∀ t : T, IsConj (s : G) (t : G) → (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype

private theorem complement_has_involution
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (R C : Subgroup P) (hc : IsComplement' R C) (hne : C ≠ ⊥) :
    ∃ s : P, orderOf s = 2 ∧ s ∈ C ∧ s ∉ R := by
  obtain ⟨a, ha, ha1⟩ := C.bot_or_exists_ne_one.resolve_left hne
  let s := a ^ (orderOf a / 2)
  have hs : orderOf s = 2 := orderOf_pow_orderOf_div (orderOf_pos a).ne' (hP.dvd_orderOf ha1)
  refine ⟨s, hs, C.pow_mem ha _, ?_⟩
  intro hr
  have he : s = 1 := disjoint_def.mp hc.disjoint hr (C.pow_mem ha _)
  simp [he] at hs

/-- The actual torus splitting supplies an involution outside R before any
fixed-centralizer classification is used. -/
theorem CyclicTorusSetup.exists_involution_outside_core
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ} (c : CyclicTorusSetup d T n) :
    ∃ s : T, orderOf s = 2 ∧
      (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨x, hxT, hxS, hxB⟩ := c.outside
  have hne : (normalizer (c.hall : Set G)).subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hx : (⟨x, hxT⟩ : T) ∈ (normalizer (c.hall : Set G)).subgroupOf (T : Subgroup G) := hxB
    rw [he, mem_bot] at hx
    apply hxS
    rw [show x = 1 from congrArg Subtype.val hx]
    exact one_mem _
  obtain ⟨s,hs,_,hsR⟩ := complement_has_involution T.isPGroup' _ _ c.split_ambient hne
  exact ⟨s,hs,hsR⟩

/-- Original 2.4.22(1), with its exact earlier-source premise 2.4.21(2). -/
theorem CyclicTorusSetup.quotient_not_cyclic_of_fusion
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ} (c : CyclicTorusSetup d T n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let := c.normal_in_sylow
    ¬ IsCyclic (T ⧸ ((Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf (T : Subgroup G))) := by
  let := c.normal_in_sylow
  obtain ⟨s,hs,hsR⟩ := c.exists_involution_outside_core
  exact quotient_not_cyclic_of_involution_closed hG T _ hclosed s hs hsR

/-- Original 2.4.22(2), using the previously proved index-two statement. -/
theorem CyclicTorusSetup.core_lt_sylow_of_fusion
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ} (c : CyclicTorusSetup d T n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) <
      (d.S : Subgroup d.H).map d.H.subtype := by
  let := c.normal_in_sylow
  apply lt_of_le_of_ne (sSup_le fun _ hA ↦ hA.1)
  intro he
  change Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) =
    (d.S : Subgroup d.H).map d.H.subtype at he
  apply c.quotient_not_cyclic_of_fusion hG hclosed
  apply isCyclic_of_prime_card (p := 2)
  change (Stellmacher.elementaryAbelianMaxJ
    ((d.S : Subgroup d.H).map d.H.subtype)).relIndex (T : Subgroup G) = 2
  rw [he]
  exact hindex

/-- The marked field-complement involution chosen after 2.4.22. -/
theorem CyclicTorusSetup.exists_field_involution_of_fusion
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ} (c : CyclicTorusSetup d T n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    ∃ s : T, orderOf s = 2 ∧
      (s : G) ∈ ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G)) ∧
      (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have hlt := c.core_lt_sylow_of_fusion hG hindex hclosed
  have hne : (S ⊓ normalizer (c.hall : Set G)).subgroupOf S ≠ ⊥ := by
    intro he
    have htop := c.split_sylow.sup_eq_top
    change R.subgroupOf S ⊔ (S ⊓ normalizer (c.hall : Set G)).subgroupOf S = ⊤ at htop
    rw [he, sup_bot_eq] at htop
    have hSR : S ≤ R := by
      intro a ha
      have hh : (⟨a,ha⟩ : S) ∈ R.subgroupOf S := by rw [htop]; exact mem_top _
      exact hh
    exact hlt.not_ge hSR
  obtain ⟨s, hs, hsF, hsR⟩ := complement_has_involution
    (d.S.isPGroup'.map d.H.subtype) _ _ c.split_sylow hne
  refine ⟨⟨s,hST s.property⟩, ?_, hsF, hsR⟩
  exact (orderOf_coe (⟨(s:G),hST s.property⟩ : T)).symm.trans ((orderOf_coe s).trans hs)

/-- The actual final p.539 transfer from the independently supplied local geometry. -/
theorem TerminalTransferSetup.false_of_fusion
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {s : T}
    (c : TerminalTransferSetup d T s) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hs : orderOf s = 2)
    (hsR : (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) : False := by
  let := c.normal
  let := c.cyclic
  obtain ⟨r, hsr, hrC⟩ := cyclic_quotient_forces_involution_fusion hG T c.kernel s hs
  have hrR : (r : G) ∈ Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) := by
    have hr : r ∈ c.kernel ⊓ (((d.S : Subgroup d.H).map d.H.subtype).subgroupOf (T : Subgroup G)) :=
      ⟨hrC, c.fusion r hsr⟩
    rw [c.intersection] at hr
    exact hr
  have hord : orderOf r = 2 := by
    rw [← orderOf_coe]
    exact (SemiconjBy.orderOf_eq (hsr.choose : G) hsr.choose_spec).symm.trans ((orderOf_coe s).trans hs)
  exact hsR (hclosed r s hord hrR hsr.symm)

/-- The original single-block consumer with precisely the two remaining source
families explicit: 2.4.21(2), and the centralizer and nonfusion geometry on p.539. -/
theorem source_single_false_of_fusion_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hterminal : ∀ (c : CyclicTorusSetup d T n) (s : T), orderOf s = 2 →
      (s : G) ∈ ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G)) →
      (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      Nonempty (TerminalTransferSetup d T s)) : False := by
  obtain ⟨c⟩ := source_cyclic_torus_setup d hG T hST hsingle hL hM hTM hunique
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle hL').1
  obtain ⟨s, hs, hsF, hsR⟩ := c.exists_field_involution_of_fusion hG hST.le hindex hclosed
  obtain ⟨e⟩ := hterminal c s hs hsF hsR
  exact e.false_of_fusion hG hs hsR hclosed

end CFSG.Quasithin.Chapter2.LinearShadows.Single
