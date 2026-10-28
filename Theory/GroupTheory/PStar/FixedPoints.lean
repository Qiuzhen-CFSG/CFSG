module

public import Theory.GroupTheory.PStar.CentralKernel
public import Theory.GroupTheory.PStar.FixedPoints.QuotientOfExtension
public import Theory.GroupTheory.PStar.Extension
public import Theory.GroupAction.FixedPointHom

/-!
# Two-star balance, action refinement and fixed-core quotient transport

The simultaneous induction in BalanceOfExtension proves GLS 5.10--5.11
from the universal 5.3 criterion. The accepted unconditional extension
theorem discharges that sole premise here. For arbitrary invariant normal
quotients, apply balance in the inverse image of the quotient fixed subgroup
and then surjective radical functoriality.

For an equivariant central surjection, conjugation by a lift of a fixed point
preserves the source fixed subgroup. Its image is therefore normal in the
target fixed subgroup, giving the forward radical containment.

For the reverse containment, take the full inverse image D of the embedded
target fixed two-star core. The central extension theorem makes O²(D)
two-star. The proved action decomposition 5.5 then gives enough fixed lifts
to cover the target core, because every action commutator maps to one.
The central-kernel radical transfer completes the equality. No surjectivity
of the full fixed-subgroup map is asserted, and D need not be normal in G.

Source: GLS II, Chapter B, 5.14, central-kernel clause underlying 5.19(ii),
using 5.3's proved central case and 5.5 (`refs/KGroup/GLS2/ChapterB.tex`).
All public conclusions in this module are unconditional: no S₂ or
classification hypothesis, balance premise, or extension premise remains.
-/

public section
open Subgroup Theory.GroupTheory

namespace FixedPoints
variable {A G H : Type*} [Group A] [Group G] [Group H]
    [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- A central kernel makes the image of the fixed subgroup normal. -/
theorem mapHom_range_normal_of_central_kernel
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    (mapHom f he).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ y
  obtain ⟨z, hz⟩ := hf (y : H)
  have hd (a : A) : (a • z) * z⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, hz, y.property a, mul_inv_cancel]
  have hcj (a : A) : (a • z) * (x : G) * (a • z)⁻¹ = z * (x : G) * z⁻¹ := by
    have hh := mem_center_iff.mp (hc (hd a)) (z * (x : G) * z⁻¹)
    have hh' : ((a • z) * z⁻¹) * (z * (x : G) * z⁻¹) *
        ((a • z) * z⁻¹)⁻¹ = z * (x : G) * z⁻¹ := by
      rw [← hh, mul_inv_cancel_right]
    convert hh' using 1
    group
  have hx : z * (x : G) * z⁻¹ ∈ fixedPointSubgroup A G := by
    intro a
    rw [smul_mul', smul_mul', smul_inv', x.property a]
    exact hcj a
  refine ⟨⟨z * (x : G) * z⁻¹, hx⟩, Subtype.ext ?_⟩
  change f (z * (x : G) * z⁻¹) = (y : H) * f (x : G) * (y : H)⁻¹
  rw [map_mul, map_mul, map_inv, hz]
end FixedPoints

namespace FixedPoints
variable {A G H : Type*} [Group A] [Group G] [Group H] [Finite G]
    [MulDistribMulAction A G]

/-- When the quotient is two-star and the actor acts trivially on it, fixed
points cover the quotient of a central extension. -/
theorem fixed_restriction_surjective_of_central_kernel
    (hA : IsPGroup 2 A) (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hH : IsPStar 2 H)
    (he : ∀ (a : A) (x : G), f (a • x) = f x) :
    Function.Surjective (f.comp (fixedPointSubgroup A G).subtype) := by
  let R := pResidual 2 G
  let : IsInvariant A G R := isInvariant_of_characteristic R
  let g := f.comp R.subtype
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    exact (map_pResidual_of_surjective 2 f hf).trans hH.1
  have hR := Theory.GroupTheory.isPStar_pResidual_of_surjective_central_kernel f hf hc hH
  have hgen := IsPStar.commutator_sup_fixed_of_centralizerResidual
    (fun Y _ _ hY N _ P => hY.isPStar_pResidual_centralizer N P) hA hR
  have hd : commutatorAction A R ≤ g.ker := by
    rw [commutatorAction_eq_closure]
    apply (closure_le _).mpr
    rintro _ ⟨a, x, rfl⟩
    change f ((x : G)⁻¹ * (a • (x : G))) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hsur : Function.Surjective (g.comp (fixedPointSubgroup A R).subtype) := by
    apply MonoidHom.range_eq_top.mp
    have hh := congrArg (Subgroup.map g) hgen
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hd, bot_sup_eq,
      map_top_of_surjective g hg] at hh
    simpa only [MonoidHom.range_comp, range_subtype] using hh
  intro y
  obtain ⟨x, hx⟩ := hsur y
  have hfix : (((x : fixedPointSubgroup A R) : R) : G) ∈ fixedPointSubgroup A G := by
    intro a
    exact congrArg Subtype.val (x.property a)
  exact ⟨⟨((x : R) : G), hfix⟩, hx⟩
end FixedPoints

namespace FixedPoints
variable {A G H : Type*} [Group A] [Group G] [Group H] [Finite G] [Finite H]
    [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- Equivariant central surjections preserve the core of the full fixed subgroup. -/
theorem map_twoStarCore_of_central_kernel
    (hA : IsPGroup 2 A) (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    (pStarCore 2 (fixedPointSubgroup A G)).map (mapHom f he) =
      pStarCore 2 (fixedPointSubgroup A H) := by
  let m := mapHom f he
  let : m.range.Normal := mapHom_range_normal_of_central_kernel f hf hc he
  apply le_antisymm (map_twoStarCore_le_of_normal_range m)
  have hcm : m.ker ≤ center (fixedPointSubgroup A G) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (congrArg Subtype.val hx)) (y : G))
  apply twoStarCore_le_map_of_central_kernel m hcm
  let B := (pStarCore 2 (fixedPointSubgroup A H)).map (fixedPointSubgroup A H).subtype
  have hBfix : B ≤ fixedPointSubgroup A H := map_subtype_le _
  have hBstar : IsPStar 2 B := isPStar_twoStarCore.of_equiv
    ((pStarCore 2 (fixedPointSubgroup A H)).equivMapOfInjective
      (fixedPointSubgroup A H).subtype (fixedPointSubgroup A H).subtype_injective)
  let D := B.comap f
  have hdfix (x : D) (a : A) : f (a • (x : G)) = f (x : G) := by
    rw [he]
    exact hBfix x.property a
  let : IsInvariant A G D := ⟨fun a x => by
    constructor
    · intro hx
      change f (a • x) ∈ B
      rw [hdfix ⟨x, hx⟩ a]
      exact hx
    · intro hx
      have hh := hdfix ⟨a • x, hx⟩ a⁻¹
      change f x ∈ B
      have hhx : f (a⁻¹ • (a • x)) ∈ B := hh.symm ▸ hx
      simpa only [inv_smul_smul] using hhx⟩
  let g := f.subgroupComap B
  have hgc : g.ker ≤ center D := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (congrArg Subtype.val hx)) (y : G))
  have hg : Function.Surjective (g.comp (fixedPointSubgroup A D).subtype) :=
    fixed_restriction_surjective_of_central_kernel hA g
      (f.subgroupComap_surjective_of_surjective B hf) hgc hBstar
      (fun a x => Subtype.ext (hdfix x a))
  intro y hy
  obtain ⟨x, hx⟩ := hg ⟨(y : H), mem_map.mpr ⟨y, hy, rfl⟩⟩
  have hxfix : (((x : fixedPointSubgroup A D) : D) : G) ∈ fixedPointSubgroup A G :=
    fun a => congrArg Subtype.val (x.property a)
  exact ⟨⟨((x : D) : G), hxfix⟩, Subtype.ext (congrArg (fun b : B => (b : H)) hx)⟩
end FixedPoints

namespace FixedPoints
variable {A G : Type*} [Group A] [Group G] [Finite G] [MulDistribMulAction A G]

/-- The central-kernel fixed-core equality for the literal quotient action and map. -/
theorem map_twoStarCore_quotient_of_central
    (hA : IsPGroup 2 A) (N : Subgroup G) [N.Normal]
    (hN : IsInvariant A G N) (hc : N ≤ center G) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    (pStarCore 2 (fixedPointSubgroup A G)).map (quotientMap N hN) =
      pStarCore 2 (fixedPointSubgroup A (G ⧸ N)) := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  exact map_twoStarCore_of_central_kernel hA (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by simpa only [QuotientGroup.ker_mk'] using hc)
    (fun _ _ => rfl)
end FixedPoints

universe u v w

private theorem fixedCoreExtensionCriterion : SylowBoundExtensionCriterion.{u} (p := 2) := by
  intro Y _ _ N _ P hquot hres hgen
  exact isPStar_pResidual_of_extension N P hquot hres hgen

namespace Subgroup
variable {G : Type u} [Group G] [Finite G]

/-- GLS II 5.11 for an actual internal two-subgroup, with the literal subtype map. -/
theorem map_twoStarCore_centralizer_le (P : Subgroup G) (hP : IsPGroup 2 P) :
    (pStarCore 2 (centralizer (P : Set G))).map (centralizer (P : Set G)).subtype ≤
      pStarCore 2 G :=
  map_twoStarCore_centralizer_le_of_extension fixedCoreExtensionCriterion P hP
end Subgroup

namespace Theory.GroupTheory.PStarAction
variable {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
  [MulDistribMulAction A G]

/-- Unconditional two-star balance for the original action, GLS II 5.11. -/
theorem map_twoStarCore_fixedPoint_le (hA : IsPGroup 2 A) :
    (pStarCore 2 (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype ≤
      pStarCore 2 G :=
  map_twoStarCore_fixedPoint_le_of_extension fixedCoreExtensionCriterion hA
end Theory.GroupTheory.PStarAction

namespace Theory.GroupTheory
variable {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
  [MulDistribMulAction A G]

/-- GLS II 5.10: a two-star group is generated by its action commutator
and the embedded two-star core of its full fixed subgroup. -/
theorem IsPStar.commutator_sup_twoStarCore_fixed (hG : IsPStar 2 G) (hA : IsPGroup 2 A) :
    commutatorAction A G ⊔ (pStarCore 2 (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype = ⊤ :=
  PStarAction.commutator_sup_twoStarCore_fixed_of_extension fixedCoreExtensionCriterion hG hA
end Theory.GroupTheory

namespace FixedPoints
variable {G : Type u} {H : Type w} {A : Type v} [Group G] [Group H] [Group A]
    [Finite G] [Finite A] [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- An equivariant surjection carries the fixed-subgroup two-star core
into the two-star core of the quotient fixed subgroup. -/
theorem map_twoStarCore_of_surjective (hA : IsPGroup 2 A)
    (f : G →* H) (hf : Function.Surjective f)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    (pStarCore 2 (fixedPointSubgroup A G)).map (mapHom f he) ≤
      pStarCore 2 (fixedPointSubgroup A H) :=
  map_twoStarCore_of_surjective_of_extension fixedCoreExtensionCriterion hA f hf he

/-- The arbitrary-kernel image containment in GLS II 5.14, retaining the
literal quotient action and `FixedPoints.quotientMap`. -/
theorem map_twoStarCore_quotient_le (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    (pStarCore 2 (fixedPointSubgroup A G)).map (quotientMap N hN) ≤
      pStarCore 2 (fixedPointSubgroup A (G ⧸ N)) := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  exact map_twoStarCore_quotient_le_of_extension fixedCoreExtensionCriterion hA N hN
end FixedPoints
