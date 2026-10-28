module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The pair calculation in the small §47.1 centralizer

From the earlier §46 frame, construct the literal subgroup B = X₁(EU).
The elementary subgroup EU has order sixteen, is normal in B, and has
index three. Hence every involution of B belongs to EU. The local census
then places its z-class involutions precisely in E minus the identity.

When B is the full centralizer of t, the source condition t ∈ ⟨ab⟩
forces ab = t, because a and b belong to EU. Conversely, each nonidentity
element e of E gives the pair (e, et). This supplies an actual equivalence
with E minus the identity and proves the count three. The subgroup order
and conjugacy transport apply this calculation to every order-48
representative in the other class.

The final theorem uses the shared §46 frame construction to discharge the
geometry input. Only the seed, local census, and order-48 assumption remain;
neither completed recognition nor the ambient group order is used.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 46.14 and 47.1,
printed pp.258–260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}
namespace LocalPairs
variable (F : LargeCentralizer.LocalFrame D t)

/-- The actual ambient subgroup X₁A₁, where A₁ = EU. -/
def B : Subgroup G := F.X1 ⊔ (F.E ⊔ F.U)

private theorem join_commute {a b : G} (ha : a ∈ F.E ⊔ F.U) (hb : b ∈ F.E ⊔ F.U) :
    Commute a b := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(F.E ⊔ F.U)) ⟨b, hb⟩)

private theorem join_pow {a : G} (ha : a ∈ F.E ⊔ F.U) : a ^ 2 = 1 := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  exact elemPow_eq_one_of_isElementaryAbelian a ha

/-- The cubic factor fixes the chosen four-group pointwise. -/
theorem X1_centralizes_U : F.X1 ≤ centralizer (F.U : Set G) := by
  intro x hx
  apply mem_centralizer_iff.mpr
  intro u hu
  have huc : u ∈ centralizer (F.X1 : Set G) := (F.U_eq ▸ hu).2
  exact (mem_centralizer_iff.mp huc x hx).symm

/-- The cubic factor preserves the elementary subgroup A₁ = EU. -/
theorem X1_normalizes_join : F.X1 ≤ normalizer ((F.E ⊔ F.U : Subgroup G) : Set G) := by
  apply le_trans (le_inf F.X1_normalizes
    ((X1_centralizes_U F).trans (Subgroup.centralizer_le_normalizer _)))
  exact normalizer_inf_normalizer_le_normalizer_sup _ _

theorem join_card : Nat.card (F.E ⊔ F.U : Subgroup G) = 16 := by
  have hn : F.U ≤ normalizer (F.E : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu
    exact mem_centralizer_iff.mpr fun e he =>
      (join_commute F (mem_sup_left he) (mem_sup_right hu)).eq
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn F.disjoint,
    F.E_card, F.U_card]

theorem B_card : Nat.card (B F) = 48 := by
  have hd : Disjoint (F.E ⊔ F.U) F.X1 := disjoint_of_coprime_natCard (by
    rw [join_card F, F.X1_card]
    decide)
  rw [B, sup_comm, card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (X1_normalizes_join F) hd, join_card F, F.X1_card]

theorem B_le_centralizer : B F ≤ involutionCentralizer t := by
  apply sup_le F.X1_le
  rw [← F.A_eq]
  exact map_subtype_le _

/-- The subgroup used in the small branch centralizes the entire four-group U. -/
theorem B_centralizes_U : B F ≤ centralizer (F.U : Set G) := by
  apply sup_le (X1_centralizes_U F)
  intro a ha
  exact mem_centralizer_iff.mpr fun u hu =>
    (join_commute F (mem_sup_right hu) ha).eq

include F in
/-- The chosen representative lies in the source set A₁ minus E. -/
theorem representative_mem (ht : OtherInvolution D t) :
    t ∈ F.E ⊔ F.U ∧ t ∉ F.E := by
  refine ⟨mem_sup_right F.t_mem, fun he => ?_⟩
  have htone := (Subgroup.disjoint_def.mp F.disjoint) he F.t_mem
  have ho := ht.1
  simp [htone] at ho

/-- Involutions vanish in the actual quotient B/A₁, which has order three. -/
theorem involution_mem_join {a : G} (ha : a ∈ B F) (ho : orderOf a = 2) :
    a ∈ F.E ⊔ F.U := by
  let N := (F.E ⊔ F.U).subgroupOf (B F)
  let : N.Normal := normal_subgroupOf_sup_of_le_normalizer (X1_normalizes_join F)
  have hN : Nat.card N = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show F.E ⊔ F.U ≤ B F from le_sup_right)).toEquiv).trans
      (join_card F)
  have hindex : N.index = 3 := by
    have hc := N.index_mul_card
    rw [hN, B_card F] at hc
    omega
  let aB : B F := ⟨a, ha⟩
  let q := QuotientGroup.mk' N
  have htwo : q aB ^ 2 = 1 := by
    rw [← map_pow]
    have ha2 : aB ^ 2 = 1 := Subtype.ext (by simpa [ho] using pow_orderOf_eq_one a)
    rw [ha2, map_one]
  have hthree : orderOf (q aB) ∣ 3 := by
    have hh := orderOf_dvd_natCard (q aB)
    change orderOf (q aB) ∣ N.index at hh
    rwa [hindex] at hh
  have hone : q aB = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
      (orderOf_dvd_of_pow_eq_one htwo) hthree)
  exact (QuotientGroup.eq_one_iff aB).mp hone

private theorem fusion_on_join (L : LocalCensus D) {a : G}
    (ha : a ∈ F.E ⊔ F.U) (ho : orderOf a = 2) : IsConj D.z a ↔ a ∈ F.E := by
  have haH : a ∈ involutionCentralizer D.z := by
    rw [← F.double_centralizer] at ha
    exact ha.2
  rw [L.core_fusion a haH ho]
  constructor
  · intro hc
    exact F.core_intersection ▸ (show a ∈ (F.E ⊔ F.U) ⊓ ambientCore D.z from ⟨ha, hc⟩)
  · intro he
    have : F.E ≤ ambientCore D.z := by
      rw [← F.core_intersection]
      exact inf_le_right
    exact this he

omit [Finite G] in
private theorem orderOf_of_isConj {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (MulAut.conj g).orderOf_eq a

/-- The literal source pairs in the small local centralizer. -/
theorem pair_iff (L : LocalCensus D) (ht : OtherInvolution D t)
    (hC : involutionCentralizer t = B F) (a b : G) :
    (IsConj D.z a ∧ IsConj t b ∧ t ∈ zpowers (a * b)) ↔
      a ∈ F.E ∧ a ≠ 1 ∧ b = a * t := by
  have htne : t ≠ 1 := by
    intro he
    simpa [he] using ht.1
  constructor
  · intro hp
    have hmem := sourcePairs_mem_centralizer ht ht.1 ⟨(a, b), hp⟩
    rw [hC] at hmem
    have hao : orderOf a = 2 := (orderOf_of_isConj hp.1).trans D.localType.involution
    have hbo : orderOf b = 2 := (orderOf_of_isConj hp.2.1).trans ht.1
    have haA := involution_mem_join F hmem.1 hao
    have hbA := involution_mem_join F hmem.2 hbo
    have hae : a ∈ F.E := (fusion_on_join F L haA hao).mp hp.1
    have hane : a ≠ 1 := by
      intro he
      simp [he] at hao
    have habne : a * b ≠ 1 := by
      intro he
      have hm := hp.2.2
      rw [he] at hm
      exact htne (by simpa using hm)
    have habo : orderOf (a * b) = 2 := orderOf_eq_prime
      (join_pow F ((F.E ⊔ F.U).mul_mem haA hbA)) habne
    have habt : a * b = t := congrArg Subtype.val
      (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨a * b, mem_zpowers _⟩ : zpowers (a * b)))
        (y := (⟨t, hp.2.2⟩ : zpowers (a * b)))
        ((orderOf_coe _).symm.trans habo) ((orderOf_coe _).symm.trans ht.1))
    refine ⟨hae, hane, ?_⟩
    have hh := congrArg (a * ·) habt
    simpa only [← mul_assoc, ← pow_two, join_pow F haA, one_mul] using hh
  · rintro ⟨ha, hane, rfl⟩
    have haA : a ∈ F.E ⊔ F.U := mem_sup_left ha
    have htA : t ∈ F.E ⊔ F.U := mem_sup_right F.t_mem
    have hbA := (F.E ⊔ F.U).mul_mem haA htA
    have htE : t ∉ F.E := fun he => htne ((Subgroup.disjoint_def.mp F.disjoint) he F.t_mem)
    have hbE : a * t ∉ F.E := by
      intro hh
      apply htE
      simpa only [inv_mul_cancel_left] using F.E.mul_mem (F.E.inv_mem ha) hh
    have hbne : a * t ≠ 1 := fun he => hbE (he ▸ F.E.one_mem)
    have hao : orderOf a = 2 := orderOf_eq_prime (join_pow F haA) hane
    have hbo : orderOf (a * t) = 2 := orderOf_eq_prime (join_pow F hbA) hbne
    refine ⟨(fusion_on_join F L haA hao).mpr ha,
      ht.isConj ⟨hbo, fun hc => hbE ((fusion_on_join F L hbA hbo).mp hc)⟩, ?_⟩
    simpa only [← mul_assoc, ← pow_two, join_pow F haA, one_mul] using mem_zpowers t

/-- The three choices in the source are the nonidentity elements of the actual E. -/
noncomputable def sourcePairsEquivNonidentity (L : LocalCensus D) (ht : OtherInvolution D t)
    (hC : involutionCentralizer t = B F) :
    SourcePairs D.z t t ≃ {e : F.E // e ≠ 1} where
  toFun p := ⟨⟨p.val.1, ((pair_iff F L ht hC _ _).mp p.property).1⟩,
    fun he => ((pair_iff F L ht hC _ _).mp p.property).2.1 (congrArg Subtype.val he)⟩
  invFun e := ⟨((e.val : G), (e.val : G) * t),
    (pair_iff F L ht hC _ _).mpr ⟨e.val.property,
      fun he => e.property (Subtype.ext he), rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl ((pair_iff F L ht hC _ _).mp p.property).2.2.symm
  right_inv e := rfl

theorem count_eq_three (L : LocalCensus D) (ht : OtherInvolution D t)
    (hC : involutionCentralizer t = B F) : sourceCount D.z t t = 3 := by
  classical
  let _ := Fintype.ofFinite F.E
  rw [sourceCount, Nat.card_congr (sourcePairsEquivNonidentity F L ht hC), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun e : F.E => e = 1), Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, F.E_card]

include F in
/-- Apply the local count at the source representative, then transport it to
an arbitrary other-class representative of centralizer order 48. -/
theorem count_eq_three_of_frame (L : LocalCensus D) (ht : OtherInvolution D t)
    {s : G} (hs : OtherInvolution D s)
    (hC : Nat.card (involutionCentralizer s) = 48) : sourceCount D.z s s = 3 := by
  have he := centralizer_eq_of_le_and_card48 hs ht hC (B F)
    (B_le_centralizer F) (B_card F)
  exact (sourceCount_at_other_eq hs ht).trans (count_eq_three F L ht he)

/-- The small-centralizer pair count in 47.1, with the actual §46 frame
constructed from the seed and local census. This discharges the pair-count
premise of the small-centralizer exclusion assembly. -/
theorem count_eq_three_of_card48 (L : LocalCensus D) (ht : OtherInvolution D t)
    (hC : Nat.card (involutionCentralizer t) = 48) : sourceCount D.z t t = 3 := by
  obtain ⟨u, hu, ⟨F⟩⟩ := LargeCentralizer.SourceFrame.exists_localFrame D L
  exact count_eq_three_of_frame F L hu ht hC

end LocalPairs
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
