module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Actions
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotients of the concrete Parker triality group

Normality of the four-group constructs `N/K`. Its image of `Q1` is canonically
isomorphic to `Q1/⟨k1⟩` and has order `2^25`. The commutator preimage theorem
identifies its centralizer in the image of `N1` with `⟨z1 K⟩`; restricting
this equality gives its center, which has order two.

These are the quotient and centralizer clauses of Aschbacher, *Sporadic Groups*,
14.4(2,5), pp. 61–62, with the bar convention introduced on p. 61.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
open scoped commutatorElement
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin
instance K_normal_instance : K.Normal := K_normal
abbrev NQuotient := N ⧸ K
def nQuotientMap : N →* NQuotient := QuotientGroup.mk' K
def N1Image : Subgroup NQuotient := N1.map nQuotientMap
def Q1Image : Subgroup NQuotient := Q1.map nQuotientMap
def z1Image : NQuotient := nQuotientMap z1N

theorem z1N_mem_Q1 : z1N ∈ Q1 := Subgroup.subset_closure (Or.inl ⟨loopPi,rfl⟩)
theorem z1Image_mem_Q1Image : z1Image ∈ Q1Image := ⟨z1N,z1N_mem_Q1,rfl⟩
theorem Q1Image_le_N1Image : Q1Image ≤ N1Image := Subgroup.map_mono Q1_le_N1

theorem nQuotientMap_eq_one (g : N) : nQuotientMap g = 1 ↔ g ∈ K :=
  QuotientGroup.eq_one_iff g

theorem nQuotientMap_commute (g q : N) :
    Commute (nQuotientMap g) (nQuotientMap q) ↔ ⁅g,q⁆ ∈ K := by
  rw [← nQuotientMap_eq_one, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  rfl

theorem nQuotientMap_mem_zpowers (g : N) :
    nQuotientMap g ∈ Subgroup.zpowers z1Image ↔ g ∈ K ⊔ Subgroup.zpowers z1N := by
  change g ∈ (Subgroup.zpowers (nQuotientMap z1N)).comap nQuotientMap ↔ _
  rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq]
  rw [show nQuotientMap.ker = K from QuotientGroup.ker_mk' K, sup_comm]

theorem Q1Image_centralizer :
    N1Image ⊓ Subgroup.centralizer (Q1Image : Set NQuotient) =
      Subgroup.zpowers z1Image := by
  ext x
  constructor
  · rintro ⟨⟨g,hg,rfl⟩,hc⟩
    apply (nQuotientMap_mem_zpowers g).mpr
    apply (centralizer_preimage g hg).mp
    intro q hq
    apply (nQuotientMap_commute g q).mp
    exact (hc _ (show nQuotientMap q ∈ Q1Image from ⟨q,hq,rfl⟩)).symm
  · intro hx
    have hzN : z1Image ∈ N1Image :=
      Q1Image_le_N1Image z1Image_mem_Q1Image
    refine ⟨Subgroup.zpowers_le.mpr hzN hx, ?_⟩
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective K x
    intro q hq
    obtain ⟨q,hq,rfl⟩ := hq
    have h := (centralizer_preimage g ?_).mpr ((nQuotientMap_mem_zpowers g).mp hx) q hq
    · exact ((nQuotientMap_commute g q).mpr h).symm
    · exact sup_le K_le_N1 (Subgroup.zpowers_le.mpr (Q1_le_N1 z1N_mem_Q1))
        ((nQuotientMap_mem_zpowers g).mp hx)

def q1ImageMap : Q1 →* Q1Image :=
  (nQuotientMap.comp Q1.subtype).codRestrict Q1Image
    (fun q => ⟨q.val,q.prop,rfl⟩)
theorem q1ImageMap_surjective : Function.Surjective q1ImageMap := by
  rintro ⟨x,g,hg,rfl⟩
  exact ⟨⟨g,hg⟩,rfl⟩
theorem q1ImageMap_ker : q1ImageMap.ker = K1.subgroupOf Q1 := by
  ext q
  change (q1ImageMap q = 1) ↔ q.val ∈ K1
  rw [Subtype.ext_iff]
  change nQuotientMap q.val = 1 ↔ _
  rw [nQuotientMap_eq_one, ← Q1_inf_K_eq_K1]
  exact ⟨fun h => ⟨q.prop,h⟩, fun h => h.2⟩
instance K1_normal_in_Q1 : (K1.subgroupOf Q1).Normal :=
  q1ImageMap_ker ▸ q1ImageMap.normal_ker
abbrev Q1Quotient := Q1 ⧸ K1.subgroupOf Q1
def q1QuotientEquivImage : Q1Quotient ≃* Q1Image :=
  (QuotientGroup.quotientMulEquivOfEq q1ImageMap_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q1ImageMap q1ImageMap_surjective)
theorem Q1Quotient_card : Nat.card Q1Quotient = 2 ^ 25 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (K1.subgroupOf Q1)
  have hk : Nat.card (K1.subgroupOf Q1) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe K1_le_Q1).toEquiv).trans K1_card
  rw [Q1_card,hk] at h
  change Nat.card (Q1 ⧸ K1.subgroupOf Q1) = _
  omega
theorem Q1Image_card : Nat.card Q1Image = 2 ^ 25 :=
  (Nat.card_congr q1QuotientEquivImage.toEquiv).symm.trans Q1Quotient_card

def q1ImageCenterGenerator : Q1Image := ⟨z1Image,z1Image_mem_Q1Image⟩
theorem Q1Image_center : Subgroup.center Q1Image =
    Subgroup.zpowers q1ImageCenterGenerator := by
  ext x
  have hc : x ∈ Subgroup.center Q1Image ↔
      x.val ∈ Subgroup.centralizer (Q1Image : Set NQuotient) := by
    rw [Subgroup.mem_center_iff]
    constructor
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y,hy⟩)
    · intro h y
      exact Subtype.ext (h y.val y.prop)
  rw [hc]
  have hi := Q1Image_le_N1Image x.prop
  have hc' : x.val ∈ Subgroup.centralizer (Q1Image : Set NQuotient) ↔
      x.val ∈ N1Image ⊓ Subgroup.centralizer (Q1Image : Set NQuotient) :=
    ⟨fun h => ⟨hi,h⟩,fun h => h.2⟩
  rw [hc',Q1Image_centralizer]
  change x.val ∈ Subgroup.zpowers (Q1Image.subtype q1ImageCenterGenerator) ↔ _
  rw [← MonoidHom.map_zpowers]
  constructor
  · rintro ⟨y,hy,he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem z1N_not_mem_K : z1N ∉ K := by
  intro h
  rcases (mem_K_iff _).mp h with he | he | he | he
  · exact z1_fixedPointFree_on_A (Or.inl ⟨loopOne,rfl⟩)
      (congrArg (fun g : N => g.val (axis2 loopOne)) he)
  · have hh := congrArg (fun g : N => g.val (axis1 loopOne)) he
    change z1 (axis1 loopOne) = k1.val (axis1 loopOne) at hh
    have hh' : loopOne = parkerSign 1 loopOne := by
      simpa [axis1,k1_apply] using hh
    exact parkerSign_one_ne loopOne hh'.symm
  · exact k2_not_mem_Q1 (he ▸ z1N_mem_Q1)
  · exact k3_not_mem_Q1 (he ▸ z1N_mem_Q1)

theorem z1Image_ne_one : z1Image ≠ 1 := by
  intro h
  exact z1N_not_mem_K ((nQuotientMap_eq_one z1N).mp h)

theorem q1ImageCenterGenerator_sq : q1ImageCenterGenerator ^ 2 = 1 := by
  apply Subtype.ext
  change nQuotientMap z1N ^ 2 = 1
  rw [← map_pow,z1N_sq,map_one]

theorem q1ImageCenterGenerator_ne_one : q1ImageCenterGenerator ≠ 1 := by
  intro h
  exact z1Image_ne_one (congrArg Subtype.val h)

theorem Q1Image_center_card : Nat.card (Subgroup.center Q1Image) = 2 := by
  rw [Q1Image_center,Nat.card_zpowers]
  exact orderOf_eq_prime q1ImageCenterGenerator_sq q1ImageCenterGenerator_ne_one
end Sporadic.Monster.Construction.TrialitySpin
