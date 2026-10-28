module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions
public import Theory.GroupTheory.QuaternionSemidihedralExtension
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.CubicBound

/-!
# Semidihedral recognition and quaternion fusion in J.2.5–6

For a constructed involution i in C_H(B) outside K, the actual six-dimensional
module forces movement on C_Q(B)/Z. Transporting through its quaternion
isomorphism produces a rotation a of order eight, with a⁴=z and i a i⁻¹=a³.
The square a² lies in C_Q(B) and conjugates i to iz.

The odd subgroup B cannot kill z, so these relations persist with exact
rotation order in the literal quotient C_H(B)/B. Its proved order bound
then identifies it with Semidihedral.StandardModel 4. The independent
lifting argument supplies i before this recognition is applied.

Source: Aschbacher–Smith J.2.5–6, printed pp.434–435 of `refs/quasithin.pdf`.
-/

public section
noncomputable section

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

private theorem quaternion_involution (x : QuaternionGroup 2) (hx : x ^ 2 = 1)
    (hx1 : x ≠ 1) : x = QuaternionGroup.a 2 := by
  revert x
  decide +kernel

/-- Construct a semidihedral rotation and a conjugator in the literal C_Q(B). -/
theorem quaternion_rotation (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (cp : CentralProductData d.toTypeRuSetup B)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1)
    (i : CB d.toTypeRuSetup B) (hiK : (i : G) ∉ d.toTypeRuSetup.K)
    (hi : orderOf (i : G) = 2) :
    ∃ a : CB d.toTypeRuSetup B,
      orderOf (a : G) = 8 ∧ (i : G) * a * (i : G)⁻¹ = (a : G) ^ 3 ∧
      (a : G) ^ 4 = z ∧
      ∃ q : HB d.toTypeRuSetup B, (q : G) * i * (q : G)⁻¹ = (i : G) * z := by
  let D := d.toTypeRuSetup
  obtain ⟨e⟩ := cp.quaternion
  let f : QuaternionGroup 2 →* G := (HB D B).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hzHB : z ∈ HB D B := by
    have hZHB : D.Z ≤ HB D B := cp.intersection_eq ▸ inf_le_left
    exact hZHB hz
  have hz2 : z ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := (⟨z, hz⟩ : D.Z))
    rw [d.card_Z] at he
    exact congrArg Subtype.val he
  have hez : e ⟨z, hzHB⟩ = QuaternionGroup.a 2 :=
    quaternion_involution _ (by
      rw [← map_pow]
      have he : (⟨z, hzHB⟩ : HB D B) ^ 2 = 1 := Subtype.ext hz2
      rw [he, map_one])
      (fun h => hz1 (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))))
  have hfz : f (QuaternionGroup.a 2) = z := by
    rw [← hez]
    exact congrArg Subtype.val (e.symm_apply_apply _)
  obtain ⟨q, hq, hmoved⟩ := (outerActionData_of_centralProduct d B cp).quaternion_moved i hiK hi
  have hq' : (i : G) * q * (i : G)⁻¹ ∈ HB D B := by
    refine ⟨(mem_normalizer_iff.mp (D.ru2.six.normalized i.property.1) q).mp hq.1, ?_⟩
    exact (centralizer _).mul_mem ((centralizer _).mul_mem i.property.2 hq.2)
      ((centralizer _).inv_mem i.property.2)
  let u := e ⟨q, hq⟩
  let v := e ⟨(i : G) * q * (i : G)⁻¹, hq'⟩
  have hfu : f u = q := congrArg Subtype.val (e.symm_apply_apply _)
  have hfv : f v = (i : G) * q * (i : G)⁻¹ := congrArg Subtype.val (e.symm_apply_apply _)
  have horder : orderOf v = orderOf u := by
    rw [← orderOf_injective f hf v, ← orderOf_injective f hf u, hfv, hfu]
    exact (MulAut.conj (i : G)).orderOf_eq q
  have hmove : f (v * u⁻¹) ∉ D.Z := by
    simpa only [map_mul, map_inv, hfv, hfu] using hmoved
  have hne : v * u⁻¹ ≠ 1 := by
    intro he
    exact hmove (by rw [he, map_one]; exact D.Z.one_mem)
  have hnz : v * u⁻¹ ≠ QuaternionGroup.a 2 := by
    intro he
    exact hmove (by rw [he, hfz]; exact hz)
  obtain ⟨ha8, hrel, hfour, -, hfusion⟩ :=
    Semidihedral.quaternion_twisted_generators f hf (i : G)
      (hi ▸ pow_orderOf_eq_one (i : G)) v u horder hne hnz (by rw [hfu, hfv])
  have hHB_CB : HB D B ≤ CB D B := inf_le_inf D.ru2.six.section_le le_rfl
  refine ⟨⟨f u * i, (CB D B).mul_mem (hHB_CB (e.symm u).property) i.property⟩,
    ha8, hrel, hfour.trans hfz, e.symm (u * v), ?_⟩
  change f (u * v) * i * (f (u * v))⁻¹ = (i : G) * z
  rwa [hfz] at hfusion
end CFSG.Quasithin.ChapterJ.Fusion.Outer

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- J.2.5 after the independent lifting argument has constructed its involution. -/
theorem sourceJ25_of_centralizing_involution (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1)
    (i : CB d.toTypeRuSetup B) (hiK : (i : G) ∉ d.toTypeRuSetup.K)
    (hi : orderOf (i : G) = 2) : SourceJ25 d.toTypeRuSetup B := by
  let D := d.toTypeRuSetup
  let C := CB D B
  let A := BSubgroup D B
  obtain ⟨a, ha, hab, haz, -⟩ := quaternion_rotation d B cp hz hz1 i hiK hi
  let π : C →* C ⧸ A.subgroupOf C := QuotientGroup.mk' _
  have hzA : z ∉ A := by
    intro hzA
    have hd : Disjoint A D.Q := (B.isPGroup'.map D.L₁.subtype).disjoint_of_coprime
      (isPGroup_pCoreIn 2 D.H) (by decide)
    exact hz1 (hd.le_bot ⟨hzA, D.ru2.six.kernel_le (D.ru2.natural.kernel_le hz)⟩)
  have ha4 : (π a) ^ 4 ≠ 1 := by
    intro he
    have hmem : a ^ 4 ∈ A.subgroupOf C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (a ^ 4) = 1
      rwa [map_pow]
    exact hzA (haz ▸ hmem)
  have ha8 : orderOf (π a) = 8 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 2) ha4
    change (π a) ^ 8 = 1
    rw [← map_pow]
    have he : a ^ 8 = 1 := Subtype.ext (ha ▸ pow_orderOf_eq_one (a : G))
    rw [he, map_one]
  have hi2 : (π i) ^ 2 = 1 := by
    rw [← map_pow]
    have he : i ^ 2 = 1 := Subtype.ext (hi ▸ pow_orderOf_eq_one (i : G))
    rw [he, map_one]
  have hrel : π i * π a * (π i)⁻¹ = (π a) ^ 3 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    exact congrArg π (Subtype.ext hab)
  exact ⟨cubic_le_CB d B, cp.quaternion,
    Semidihedral.equiv_of_small_twisted_generators (π a) (π i) ha8 hi2 hrel
      (cubic_quotient_card_le d B cp)⟩

end CFSG.Quasithin.ChapterJ.Fusion.Outer
