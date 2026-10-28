module
public import Theory.Representation.SL3.DualInvariantLines

/-!
# Detecting the center of a doubled-dual extension

A covector stabilizer with no fixed point on the central kernel forces every
dual diagonal to have elementary full preimage. The image of a larger center
would be a whole invariant dual line. The complementary elementary line then
generates the group with its center, making it abelian. Thus a nonabelian
extension has exactly the specified central kernel.

The application in LinearThreeMS.NonbinarySource.SecondCenterExhaustion
uses both natural and doubled-natural central kernels at one SL₃ marking.
Source: Aschbacher–Smith C.1.34–35, pp.136–138; the dual stabilizer argument
in C.1.35(2).
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL3ParabolicNatural
variable {F A P : Type*} [Field F] [Group A] [Group P]

/-- Stabilizer fixed points force elementary full preimages of every dual
line, retaining an arbitrary central kernel representation. -/
theorem dual_lines_elementary_of_fixed_zero
    {W : Type*} [AddCommGroup W] [Module F W] [CharP F 2]
    (α : A →* SL(3,F)) (hα : Function.Surjective α) (act : A →* MulAut P)
    (p : P →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hc : p.ker ≤ center P) (ρ : Representation F SL(3,F) W)
    (u : p.ker ≃* Multiplicative W)
    (hp : ∀ a x, (p (act a x)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p x).toAdd)
    (hu : ∀ (a : A) (x y : p.ker), (y : P) = act a (x : P) →
      (u y).toAdd = ρ (α a) (u x).toAdd)
    (hfix : ∀ f : Module.Dual F (Fin 3 → F), f ≠ 0 → ∀ w : W,
      (∀ g : SL(3,F), (specialLinearNatural 3).dual g f=f → ρ g w=w) → w=0)
    (a b : F) : IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p) := by
  have hexp (z : p.ker) : (z:P)^2=1 := by
    have he : u (z^2)=1 := by
      rw [map_pow,pow_two]
      apply Multiplicative.toAdd.injective
      change (u z).toAdd+(u z).toAdd=0
      rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]
    exact congrArg Subtype.val (u.map_eq_one_iff.mp he)
  have hs (q : P) (f : Module.Dual F (Fin 3 → F))
      (hq : (p q).toAdd=(a • f,b • f)) : q^2=1 := by
    have hq2 : q^2∈p.ker := by
      change p (q^2)=1
      rw [map_pow,pow_two]
      apply Multiplicative.toAdd.injective
      change (p q).toAdd+(p q).toAdd=0
      rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]
    by_cases hf : f=0
    · apply hexp ⟨q,?_⟩
      apply Multiplicative.toAdd.injective
      change (p q).toAdd=0
      simp [hq,hf]
    let z : p.ker := ⟨q^2,hq2⟩
    have hz : (u z).toAdd=0 := by
      apply hfix f hf
      intro g hg
      obtain ⟨k,rfl⟩ := hα g
      have hd : (act k q)/q∈p.ker := by
        apply p.div_mem_ker_iff.mpr
        apply Multiplicative.toAdd.injective
        rw [hp,hq]
        change ((specialLinearNatural 3).dual (α k) (a • f),
          (specialLinearNatural 3).dual (α k) (b • f))=(a • f,b • f)
        rw [map_smul,map_smul,hg]
      have hcomm : Commute ((act k q)/q) q := (mem_center_iff.mp (hc hd) q).symm
      have hsq : act k (q^2)=q^2 := by
        rw [map_pow]
        calc (act k q)^2=(((act k q)/q)*q)^2 := by rw [div_mul_cancel]
             _=((act k q)/q)^2*q^2 := hcomm.mul_pow 2
             _=q^2 := by rw [hexp ⟨_,hd⟩,one_mul]
      exact (hu k z z hsq.symm).symm
    exact congrArg Subtype.val (u.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz))
  let B := (dualDiagonal a b).range.comap p
  have hsB (x : B) : x^2=1 := by
    obtain ⟨f,hf⟩ := x.property
    exact Subtype.ext (hs x f.toAdd (congrArg Multiplicative.toAdd hf).symm)
  have hinv (x : B) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hsB x)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsB }
  intro x y
  calc x*y=(x*y)⁻¹ := (hinv _).symm
       _=y*x := by rw [_root_.mul_inv_rev,hinv,hinv]

/-- A nonabelian central extension of doubled duals with elementary diagonal
preimages has precisely the specified kernel as its center. -/
theorem center_eq_kernel_of_elementary_dual_lines
    (α : A →* SL(3,F)) (hα : Function.Surjective α) (act : A →* MulAut P)
    (p : P →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (_hp : Function.Surjective p) (hc : p.ker ≤ center P)
    (he : ∀ a x, (p (act a x)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p x).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (hna : ¬ IsMulCommutative P) : center P = p.ker := by
  let D := (center P).map p
  have hab (B : Subgroup P) [IsMulCommutative B]
      (hB : ∀ x : P, ∃ z ∈ center P, x / z ∈ B) : IsMulCommutative P := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨zx,hzx,hx⟩ := hB x
    obtain ⟨zy,hzy,hy⟩ := hB y
    have hxy : Commute (x/zx) (y/zy) :=
      congrArg Subtype.val (mul_comm' (⟨x/zx,hx⟩ : B) ⟨y/zy,hy⟩)
    have h1 : Commute ((x/zx)*zx) (y/zy) :=
      hxy.mul_left (mem_center_iff.mp hzx (y/zy)).symm
    have h2 := h1.mul_right (show Commute ((x/zx)*zx) zy from
      mem_center_iff.mp hzy _)
    simpa only [div_mul_cancel] using h2.eq
  have hproper : D ≠ ⊤ := by
    intro ht
    apply hna
    apply center_eq_top_iff.mp
    apply top_unique
    intro x _
    obtain ⟨z,hz,hzx⟩ := show p x ∈ D from ht ▸ mem_top _
    have hd : x/z ∈ center P := hc (p.div_mem_ker_iff.mpr hzx.symm)
    simpa only [div_mul_cancel] using (center P).mul_mem hd hz
  have hD : D = ⊥ := by
    by_contra hn
    obtain ⟨a,ha⟩ := invariant_dual_subgroup_eq_line D hn hproper (by
      intro g v hv
      obtain ⟨k,rfl⟩ := hα g
      obtain ⟨x,hx,rfl⟩ := hv
      refine ⟨act k x,(centerCongr (act k) ⟨x,hx⟩).property,?_⟩
      exact Multiplicative.toAdd.injective (he k x))
    apply hna
    cases a with
    | none =>
      let B := (dualDiagonal (1:F) 0).range.comap p
      let : IsMulCommutative B := (hel 1 0).toIsMulCommutative
      apply hab B
      intro x
      have hv : Multiplicative.ofAdd (0,(p x).toAdd.2) ∈ D := by
        rw [ha,mem_dualLine_none]
        rfl
      obtain ⟨z,hz,hzv⟩ := hv
      refine ⟨z,hz,Multiplicative.ofAdd ((p x).toAdd.1),?_⟩
      apply Multiplicative.toAdd.injective
      rw [map_div,hzv]
      change ((1:F) • (p x).toAdd.1,(0:F) • (p x).toAdd.1) = (p x).toAdd-(0,(p x).toAdd.2)
      exact Prod.ext (by simp) (by simp)
    | some a =>
      let B := (dualDiagonal (0:F) 1).range.comap p
      let : IsMulCommutative B := (hel 0 1).toIsMulCommutative
      apply hab B
      intro x
      have hv : Multiplicative.ofAdd ((p x).toAdd.1,a • (p x).toAdd.1) ∈ D := by
        rw [ha,mem_dualLine_some]
        rfl
      obtain ⟨z,hz,hzv⟩ := hv
      refine ⟨z,hz,Multiplicative.ofAdd ((p x).toAdd.2-a • (p x).toAdd.1),?_⟩
      apply Multiplicative.toAdd.injective
      rw [map_div,hzv]
      change (0 • _,1 • _) = (p x).toAdd-((p x).toAdd.1,a • (p x).toAdd.1)
      exact Prod.ext (by simp) (by simp)
  apply le_antisymm _ hc
  intro x hx
  have hh : p x ∈ D := mem_map_of_mem p hx
  rwa [hD,mem_bot] at hh
/-- Elementary complementary dual lines generate every abelian extension. -/
theorem elementary_of_abelian_dual_lines
    (p : P →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hp : Function.Surjective p)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (hab : IsMulCommutative P) : IsElementaryAbelian 2 P := by
  let := hab
  have hexp (a b : F) (x : P) (hx : p x∈(dualDiagonal a b).range) : x^2=1 := by
    let : IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p) := hel a b
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := (dualDiagonal a b).range.comap p) x hx
  refine { toIsMulCommutative := hab
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨y,hy⟩ := hp (Multiplicative.ofAdd (0,(p x).toAdd.2))
  have hy2 : y^2=1 := hexp 0 1 y ⟨Multiplicative.ofAdd ((p x).toAdd.2),by
    rw [hy]
    apply Multiplicative.toAdd.injective
    change ((0:F) • (p x).toAdd.2,(1:F) • (p x).toAdd.2)=(0,(p x).toAdd.2)
    simp⟩
  have hx2 : (x/y)^2=1 := hexp 1 0 (x/y) ⟨Multiplicative.ofAdd ((p x).toAdd.1),by
    rw [map_div,hy]
    apply Multiplicative.toAdd.injective
    change ((1:F) • (p x).toAdd.1,(0:F) • (p x).toAdd.1)=(p x).toAdd-(0,(p x).toAdd.2)
    exact Prod.ext (by simp) (by simp)⟩
  calc x^2=((x/y)*y)^2 := by rw [div_mul_cancel]
       _=(x/y)^2*y^2 := (show Commute (x/y) y from mul_comm' _ _).mul_pow 2
       _=1 := by rw [hx2,hy2,mul_one]
end Representation.SL3ParabolicNatural

