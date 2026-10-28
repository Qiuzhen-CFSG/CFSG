module

public import Theory.Representation.BinaryConjugationSection.QuotientSection
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.BinaryOffender.Basic

/-!
# Exact coprime fixed counts in a literal binary conjugation section

Coprime lifting makes the original coordinate map onto the fixed subspace
when restricted to the original relative centralizer. Its kernel is the
relative centralizer in the original denominator. The first isomorphism
count therefore retains the entire numerator and denominator.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- Fixed vectors lift to the actual relative centralizer, and its order
includes the full fixed part of the specified kernel. -/
theorem coprime_fixed_card (d : BinaryConjugationSection H U Z ρ)
    (A : Subgroup G) (hAH : A ≤ H) (hsolv : Group.IsSolvable U)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card U)) :
    Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (fixedSpace ρ (A.subgroupOf H)) *
        Nat.card (Z ⊓ centralizer (A : Set G) : Subgroup G) := by
  classical
  let C := U ⊓ centralizer (A : Set G)
  let F := fixedSpace ρ (A.subgroupOf H)
  have hfixed (c : C) : (d.coordinates ⟨c,c.property.1⟩).toAdd ∈ F := by
    intro a
    change ρ (a : H) (d.coordinates ⟨c,c.property.1⟩).toAdd = _
    rw [←d.equivariant (a : H) ⟨c,c.property.1⟩]
    congr 2
    apply Subtype.ext
    change (a:G)*(c:G)*(a:G)⁻¹=(c:G)
    rw [mem_centralizer_iff.mp c.property.2 a a.property,mul_inv_cancel_right]
  let f : C →* Multiplicative F := {
    toFun := fun c => Multiplicative.ofAdd ⟨(d.coordinates ⟨c,c.property.1⟩).toAdd,hfixed c⟩
    map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one d.coordinates)
    map_mul' := by intro c e; apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_mul d.coordinates ⟨c,c.property.1⟩ ⟨e,e.property.1⟩) }
  let native := conjMulDistribMulActionOfLeNormalizer A U (hAH.trans d.normalized)
  let _ : MulDistribMulAction A U := native
  let _ : SMul A U := native.toSMul
  let _ : MulAction A U := native.toMulAction
  have hequiv (a : A) (u : U) :
      (d.coordinates (a • u)).toAdd = ρ (inclusion hAH a) (d.coordinates u).toAdd :=
    d.equivariant (inclusion hAH a) u
  have hInv : IsInvariant A U d.coordinates.ker := by
    constructor
    intro a u
    change d.coordinates u=1 ↔ d.coordinates (a • u)=1
    constructor
    · intro hu
      apply Multiplicative.toAdd.injective
      rw [hequiv a u,hu]
      exact map_zero _
    · intro hu
      have hh := congrArg Multiplicative.toAdd hu
      rw [hequiv a u] at hh
      apply Multiplicative.toAdd.injective
      exact (ρ.apply_bijective (inclusion hAH a)).injective (hh.trans (map_zero _).symm)
  let _ : MulDistribMulAction A (U ⧸ d.coordinates.ker) := quotientMulDistribMulAction d.coordinates.ker hInv
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd w.toAdd.val)
    have hq : QuotientGroup.mk' d.coordinates.ker u ∈
        FixedPoints.subgroup A (U ⧸ d.coordinates.ker) := by
      intro a
      change QuotientGroup.mk' d.coordinates.ker (a • u)=QuotientGroup.mk' d.coordinates.ker u
      apply QuotientGroup.eq_iff_div_mem.mpr
      change d.coordinates ((a • u)/u)=1
      rw [map_div,div_eq_one]
      apply Multiplicative.toAdd.injective
      rw [hequiv a u,hu]
      exact w.toAdd.property ⟨inclusion hAH a,a.property⟩
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop d.coordinates.ker hInv] at hq
    obtain ⟨v,hv,he⟩ := hq
    have hvC : (v:G) ∈ C := by
      refine ⟨v.property,mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have hh := congrArg Subtype.val (hv ⟨a,ha⟩)
      change a*(v:G)*a⁻¹=(v:G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hc : d.coordinates v=d.coordinates u := by
      have hh := QuotientGroup.eq_iff_div_mem.mp he
      change d.coordinates (v/u)=1 at hh
      rwa [map_div,div_eq_one] at hh
    refine ⟨⟨v,hvC⟩,?_⟩
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hc.trans hu)
  let e : f.ker ≃ (Z ⊓ centralizer (A : Set G) : Subgroup G) := {
    toFun := fun x => ⟨x.val.val,(d.coordinates_eq_one_iff _).mp
      (Multiplicative.toAdd.injective (congrArg (fun y : Multiplicative F => y.toAdd.val) x.property)),x.val.property.2⟩
    invFun := fun z => ⟨⟨z,d.kernel_le z.property.1,z.property.2⟩,by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd ((d.coordinates_eq_one_iff _).mpr z.property.1)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcount := f.ker.index_mul_card
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,card_top,Nat.card_congr e] at hcount
  exact hcount.symm

end Representation.BinaryConjugationSection
