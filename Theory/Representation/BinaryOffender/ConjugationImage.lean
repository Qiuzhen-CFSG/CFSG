module

public import Theory.Representation.BinaryOffender.CubicInversionContainment
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Mathlib.Algebra.Module.ZMod

/-!
# Commutator images under an actual conjugation quotient

For a normalized subgroup U and a surjective map from U to an elementary
abelian group, the image of [P,X] is exactly the span of the action differences
on the image of P. The conjugation formula and both literal quotient maps are
retained. Normality is relative to X; U need not be normal in the ambient group.

The upper inclusion uses the inverse image of the linear commutator span.
For the reverse inclusion, each action difference is the image of the actual
commutator x*p*x⁻¹*p⁻¹. This bridge is used to convert the native cubic-point
calculation in Aschbacher–Smith 14.4.12, printed p.1012, into a quotient image
of order four before applying the extraspecial central-kernel lift.
-/

@[expose] public section
noncomputable section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace Representation.BinaryOffender
variable {G D Q : Type*} [Group G] [Group D] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

def quotientImage (U : Subgroup G) (q : U →* Q) (P : Subgroup G) :
    Submodule (ZMod 2) (Additive Q) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup ((P.subgroupOf U).map q))

theorem quotientImage_commutator
    (ρ : Representation (ZMod 2) D (Additive Q)) (U P X : Subgroup G)
    (hn : X ≤ normalizer (U : Set G)) (hPU : P ≤ U)
    (f : X →* D) (q : U →* Q) (hq : Function.Surjective q)
    (hact : ∀ (x : X) (u : U), ρ (f x) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩)) :
    quotientImage U q (⁅P, X⁆) =
      subspaceCommutator ρ (quotientImage U q P) f.range := by
  let M := subspaceCommutator ρ (quotientImage U q P) f.range
  let B := Subgroup.toAddSubgroup.symm M.toAddSubgroup
  let E := (B.comap q).map U.subtype
  have hEU : E.subgroupOf U = B.comap q :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  have hM : ⁅P, X⁆ ≤ E := by
    apply commutator_le_of_conjugation_image ρ U P X E hn hPU f q hact
      (quotientImage U q P) M
    · intro u hu
      change q u ∈ (P.subgroupOf U).map q
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    · rw [hEU, Subgroup.map_comap_eq_self_of_surjective hq]
    · rw [hEU]
      exact B.ker_le_comap q
    · exact le_rfl
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu, hqv⟩ := hv
    have he : u ∈ E.subgroupOf U := hM hu
    rw [hEU] at he
    change q u ∈ B at he
    change Additive.ofMul (q u) ∈ M at he
    rw [hqv] at he
    exact he
  · apply Submodule.span_le.mpr
    rintro v ⟨_, ⟨x, rfl⟩, w, hw, rfl⟩
    obtain ⟨p, hp, hqp⟩ := hw
    have hw : w = Additive.ofMul (q p) := congrArg Additive.ofMul hqp.symm
    subst w
    rw [hact]
    let c : U := ⟨(x : G) * p * (x : G)⁻¹,
      le_normalizer_iff.mp hn x x.property p p.property⟩
    change q c / q p ∈ ((⁅P, X⁆).subgroupOf U).map q
    rw [div_eq_mul_inv]
    refine Subgroup.mem_map.mpr ⟨c * p⁻¹, ?_, ?_⟩
    · change ⁅(x : G), (p : G)⁆ ∈ ⁅P, X⁆
      rw [commutator_comm]
      exact commutator_mem_commutator x.property hp
    · change q (c * p⁻¹) = q c * (q p)⁻¹
      simp only [map_mul, map_inv]

end Representation.BinaryOffender

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation.BinaryOffender
variable {G D Q : Type*} [Group G] [Group D] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

/-- The multiplicative subgroup of a binary subspace in the actual quotient. -/
def binarySubgroup (A : Submodule (ZMod 2) (Additive Q)) : Subgroup Q :=
  Subgroup.toAddSubgroup.symm A.toAddSubgroup

/-- The binary subspace of a subgroup of the actual quotient. -/
def binarySpace (A : Subgroup Q) : Submodule (ZMod 2) (Additive Q) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup A)

theorem binarySubgroup_card (A : Submodule (ZMod 2) (Additive Q)) :
    Nat.card (binarySubgroup A) = Nat.card A := by
  exact Nat.card_congr
    { toFun := fun q => ⟨Additive.ofMul q.val, q.property⟩
      invFun := fun q => ⟨q.val.toMul, q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Exact commutator image for the prescribed quotient conjugation action.
The point image and every conjugation map are retained literally. -/
theorem commutator_image_eq
    (ρ : Representation (ZMod 2) D (Additive Q)) (U P X : Subgroup G)
    (hn : X ≤ normalizer (U : Set G)) (hPU : P ≤ U)
    (f : X →* D) (q : U →* Q)
    (hact : ∀ (x : X) (u : U), ρ (f x) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩))
    (Pbar : Submodule (ZMod 2) (Additive Q))
    (hP : binarySubgroup Pbar = (P.subgroupOf U).map q) :
    (⁅P, X⁆.subgroupOf U).map q =
      binarySubgroup (Representation.BinaryOffender.subspaceCommutator ρ Pbar f.range) := by
  let L := Representation.BinaryOffender.subspaceCommutator ρ Pbar f.range
  have hMU : ⁅P, X⁆ ≤ U := (commutator_mono hPU le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hn)
  apply le_antisymm
  · let E : Subgroup G := ((binarySubgroup L).comap q).map U.subtype
    have hcomm : ⁅P, X⁆ ≤ E := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro x hx p hp
      let xX : X := ⟨x, hx⟩
      let pU : U := ⟨p, hPU hp⟩
      let c : U := ⟨x * p * x⁻¹, le_normalizer_iff.mp hn x hx p (hPU hp)⟩
      have hpbar : Additive.ofMul (q pU) ∈ Pbar := by
        change q pU ∈ binarySubgroup Pbar
        rw [hP]
        exact mem_map_of_mem q hp
      have hd : ρ (f xX) (Additive.ofMul (q pU)) - Additive.ofMul (q pU) ∈ L :=
        Submodule.subset_span ⟨f xX, ⟨xX, rfl⟩, _, hpbar, rfl⟩
      refine mem_map.mpr ⟨c * pU⁻¹, ?_, rfl⟩
      change Additive.ofMul (q (c * pU⁻¹)) ∈ L
      rw [map_mul, map_inv]
      change Additive.ofMul (q c) + -Additive.ofMul (q pU) ∈ L
      rw [hact] at hd
      simpa only [sub_eq_add_neg] using hd
    rintro a ⟨u, hu, rfl⟩
    obtain ⟨v, hv, he⟩ := hcomm hu
    have hev : v = u := Subtype.ext he
    exact hev ▸ hv
  · change binarySubgroup L ≤ (⁅P, X⁆.subgroupOf U).map q
    suffices h : L ≤ binarySpace ((⁅P, X⁆.subgroupOf U).map q) from h
    apply Submodule.span_le.mpr
    rintro v ⟨_, ⟨x, rfl⟩, w, hw, rfl⟩
    have hwm : w.toMul ∈ (P.subgroupOf U).map q := by
      rw [← hP]
      exact hw
    obtain ⟨p, hp, he⟩ := hwm
    have hew : Additive.ofMul (q p) = w := congrArg Additive.ofMul he
    let c : U := ⟨(x : G) * p * (x : G)⁻¹,
      le_normalizer_iff.mp hn x x.property p p.property⟩
    change (ρ (f x) w - w).toMul ∈ (⁅P, X⁆.subgroupOf U).map q
    refine mem_map.mpr ⟨c * p⁻¹, ?_, ?_⟩
    · change ⁅(x : G), (p : G)⁆ ∈ ⁅P, X⁆
      rw [commutator_comm]
      exact commutator_mem_commutator x.property hp
    · apply Additive.toMul.injective
      change Additive.ofMul (q (c * p⁻¹)) = ρ (f x) w - w
      rw [map_mul, map_inv]
      simp only [sub_eq_add_neg]
      change Additive.ofMul (q c) + -Additive.ofMul (q p) = _
      rw [← hact x p, hew]

end Representation.BinaryOffender

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryOffender
open Representation.BinaryOffender
variable {G D Q V : Type*} [Group G] [Group D] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)] [AddCommGroup V] [Module (ZMod 2) V]

/-- Equivariant constituent coordinates compute an ambient commutator image
without identifying the constituent with the whole quotient. -/
theorem commutator_image_eq_of_embedding
    (ρ : Representation (ZMod 2) D (Additive Q)) (σ : Representation (ZMod 2) G V)
    {K : Type*} [Group K] (U P X : Subgroup K)
    (hn : X ≤ normalizer (U : Set K)) (hPU : P ≤ U)
    (f : X →* D) (q : U →* Q)
    (hact : ∀ (x : X) (u : U), ρ (f x) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(x : K) * u * (x : K)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩))
    (e : V →ₗ[ZMod 2] Additive Q) (k : X →* G)
    (he : ∀ x v, ρ (f x) (e v) = e (σ (k x) v))
    (Pbar : Submodule (ZMod 2) V)
    (hP : binarySubgroup (Pbar.map e) = (P.subgroupOf U).map q) :
    (⁅P, X⁆.subgroupOf U).map q =
      binarySubgroup ((subspaceCommutator σ Pbar k.range).map e) := by
  let τ := ρ.comp f
  have ht : ∀ (x : X) (u : U), τ x (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(x : K) * u * (x : K)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩) := hact
  have hm := commutator_image_eq τ U P X hn hPU (MonoidHom.id X) q ht (Pbar.map e) hP
  rw [MonoidHom.range_eq_top.mpr (Function.surjective_id)] at hm
  rw [subspaceCommutator_map_embedding τ σ k e he ⊤ Pbar,
    ← MonoidHom.range_eq_map] at hm
  exact hm

end Representation.BinaryOffender
