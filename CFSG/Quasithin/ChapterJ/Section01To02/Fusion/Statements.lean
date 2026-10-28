module

public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import Theory.GroupTheory.SemidihedralStandardModel
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Exact targets for the local fusion lemmas

These predicates specify J.2.4–6 and J.2.8; they are not proofs of those
lemmas. Modulo-Z statements use the actual map H → H/Z, and the cubic
centralizer quotient uses the actual subgroup B of C_H(B). Fusion and
transitivity retain their conjugating elements in the specified subgroups.

`CentralProductData` is the intermediate decomposition HC = C_Q(B)U with
intersection Z. Its construction belongs to the commutator branch. It is
not part of Ru1/Ru2 and must be supplied before applying the conditional
omega/Frattini theorem in `Fusion.CentralProduct`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.434–435 and 437–438 (PDF pp.445–446 and 448–449).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

instance centerKernelNormal (d : TypeRuSetup G) : (d.Z.subgroupOf d.H).Normal where
  conj_mem a ha h := by
    change (a : G) ∈ d.Z at ha
    change (h : G) * (a : G) * (h : G)⁻¹ ∈ d.Z
    have he : (a : G) * (h : G) = (h : G) * (a : G) := h.property a ha
    simpa only [← he, mul_assoc, mul_inv_cancel, mul_one] using ha

def centerQuotientMap (d : TypeRuSetup G) : d.H →* d.H ⧸ d.Z.subgroupOf d.H :=
  QuotientGroup.mk' _

def modZ (d : TypeRuSetup G) (A : Subgroup G) :
    Subgroup (d.H ⧸ d.Z.subgroupOf d.H) :=
  (A.subgroupOf d.H).map (centerQuotientMap d)

def BSubgroup (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Subgroup G :=
  (B : Subgroup d.L₁).map d.L₁.subtype

def HB (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Subgroup G :=
  d.Q ⊓ centralizer (BSubgroup d B : Set G)

def CB (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Subgroup G :=
  d.H ⊓ centralizer (BSubgroup d B : Set G)

instance cubicKernelNormal (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    ((BSubgroup d B).subgroupOf (CB d B)).Normal where
  conj_mem a ha h := by
    change (a : G) ∈ BSubgroup d B at ha
    change (h : G) * (a : G) * (h : G)⁻¹ ∈ BSubgroup d B
    have he : (a : G) * (h : G) = (h : G) * (a : G) := h.property.2 a ha
    simpa only [← he, mul_assoc, mul_inv_cancel, mul_one] using ha

def involutionsOutside (A D : Subgroup G) : Set G :=
  {x | x ∈ A ∧ x ∉ D ∧ orderOf x = 2}

def TransitiveOn (H : Subgroup G) (X : Set G) : Prop :=
  ∀ ⦃x y : G⦄, x ∈ X → y ∈ X → ∃ h : H, (h : G) * x * (h : G)⁻¹ = y

def SourceJ24 (d : TypeRuSetup G) : Prop :=
  ∀ h : G, ∀ hh : h ∈ d.HC, h ∉ d.U →
    ⁅zpowers (centerQuotientMap d ⟨h, hh.1⟩), modZ d d.Q⁆ = modZ d d.U ∧
    ⁅zpowers h, d.Q⁆ = d.U ∧
    d.Q ⊓ centralizer ({h} : Set G) = zpowers h ⊔ d.U

def SourceJ25 (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Prop :=
  BSubgroup d B ≤ CB d B ∧
  Nonempty (HB d B ≃* QuaternionGroup 2) ∧
  Nonempty ((CB d B ⧸ (BSubgroup d B).subgroupOf (CB d B)) ≃*
    Semidihedral.StandardModel 4 (by decide))

def ElementaryFusion (d : TypeRuSetup G) (z : G) : Prop :=
  omegaOneAmbient d.HC = d.U ∧
  (frattini d.HC).map d.HC.subtype = d.Z ∧
  ∀ u ∈ d.U, u ≠ 1 → IsConj u z

def SourceJ26 (d : TypeRuSetup G) (z : G) : Prop :=
  (TransitiveOn d.H (involutionsOutside d.H d.K) ∧
    Nat.card (involutionsOutside d.H d.K) = 640 ∧
    ∀ i ∈ involutionsOutside d.H d.K, IsConj i z) ∧
  (∀ i ∈ involutionsOutside d.L d.S, IsConj i z) ∧
  (∀ i ∈ d.Q, orderOf i = 2 → IsConj i z) ∧
  ElementaryFusion d z

def SourceJ28 (d : TypeRuSetup G) (z : G) : Prop :=
  (TransitiveOn d.H (involutionsOutside d.Q d.U) ∧
    Nat.card (involutionsOutside d.Q d.U) = 240 ∧
    ∀ i ∈ involutionsOutside d.Q d.U, IsConj i z) ∧
  (∀ i ∈ d.S ⊓ d.Q, orderOf i = 2 →
    ∃ l : d.L, (l : G) * i * (l : G)⁻¹ ∈ d.U) ∧
  (∀ u ∈ d.U, u ∉ d.V → ∀ i ∈ d.S ⊓ centralizer ({u} : Set G),
    orderOf i = 2 → IsConj i z)

structure CentralProductData (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Prop where
  quaternion : Nonempty (HB d B ≃* QuaternionGroup 2)
  product_eq : d.HC = HB d B ⊔ d.U
  intersection_eq : HB d B ⊓ d.U = d.Z

end CFSG.Quasithin.ChapterJ.Fusion
