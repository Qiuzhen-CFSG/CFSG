module

public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupAction.Defs
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Fixed residuals for an arbitrary acting group

For an equivariant surjection with central p-group kernel, every actor's
displacement on the inverse image of the fixed subgroup is a homomorphism
to the kernel. These homomorphisms kill the p-residual simultaneously.
Consequently the residual of the full fixed subgroup maps onto the
residual of the quotient fixed subgroup, even when fixed points do not lift.

Source: GLS II, Chapter B, Lemma 4.2(ii), as used in Lemma 5.3.
-/

public section
open Subgroup
namespace FixedPoints
variable {A G H : Type*} [Group A] [Group G] [Group H]
  [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- The homomorphism on fixed subgroups induced by an equivariant map. -/
@[expose] def subgroupMap (f : G →* H)
    (heq : ∀ a : A, ∀ x : G, f (a • x) = a • f x) :
    subgroup A G →* subgroup A H :=
  (f.comp (subgroup A G).subtype).codRestrict (subgroup A H) (fun x a => by
    change a • f x = f x
    rw [← heq, x.property a])

/-- Central p-kernels preserve the residual of the full fixed subgroup.
The actor need not be finite or a p-group. -/
theorem map_fixedResidual_of_central_pgroup_ker [Finite G]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker)
    (heq : ∀ a : A, ∀ x : G, f (a • x) = a • f x) :
    (pResidual p (subgroup A G)).map (subgroupMap f heq) =
      pResidual p (subgroup A H) := by
  let D := (subgroup A H).comap f
  have hdmem (a : A) (x : D) : a • (x : G) * (x : G)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, x.property a, mul_inv_cancel]
  let d (a : A) : D →* f.ker := {
    toFun x := ⟨a • (x : G) * (x : G)⁻¹, hdmem a x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change a • ((x : G) * y) * ((x : G) * y)⁻¹ =
        (a • (x : G) * (x : G)⁻¹) * (a • (y : G) * (y : G)⁻¹)
      have hy := mem_center_iff.mp (hc (hdmem a y)) (x : G)⁻¹
      rw [smul_mul', mul_inv_rev]
      calc
        _ = a • (x : G) * ((a • (y : G) * (y : G)⁻¹) * (x : G)⁻¹) := by group
        _ = a • (x : G) * ((x : G)⁻¹ * (a • (y : G) * (y : G)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hrfix (x : pResidual p D) : ((x : D) : G) ∈ subgroup A G := by
    intro a
    have hd : (d a).comp (pResidual p D).subtype = 1 :=
      (isPPerfect_pResidual p).hom_eq_one_of_isPGroup hp _
    have h := congrArg (fun k : pResidual p D →* f.ker => (k x : G)) hd
    exact mul_inv_eq_one.mp h
  let r : pResidual p D →* subgroup A G :=
    (D.subtype.comp (pResidual p D).subtype).codRestrict (subgroup A G) hrfix
  have hr (x : pResidual p D) : r x ∈ pResidual p (subgroup A G) := by
    apply map_pResidual_le p r
    exact mem_map.mpr ⟨x, by
      rw [(pResidual_eq_top_iff p _).mpr (isPPerfect_pResidual p)]; trivial, rfl⟩
  let q : D →* subgroup A H := f.subgroupComap (subgroup A H)
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  apply le_antisymm (map_pResidual_le p _) ?_
  intro y hy
  rw [← map_pResidual_of_surjective p q hq] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact mem_map.mpr ⟨r ⟨x, hx⟩, hr ⟨x, hx⟩, hxy⟩

/-- The same equality with both fixed residuals embedded in their ambient groups. -/
theorem map_embedded_fixedResidual_of_central_pgroup_ker [Finite G]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker)
    (heq : ∀ a : A, ∀ x : G, f (a • x) = a • f x) :
    ((pResidual p (subgroup A G)).map (subgroup A G).subtype).map f =
      (pResidual p (subgroup A H)).map (subgroup A H).subtype := by
  rw [← map_fixedResidual_of_central_pgroup_ker p f hf hc hp heq, map_map, map_map]
  rfl

end FixedPoints

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The centralizer version of fixed-residual lifting, with the actual
subgroup images and ambient embeddings. -/
theorem map_embedded_centralizer_pResidual_of_central_pgroup_ker [Finite G]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker) (Q : Subgroup G) :
    ((pResidual p (centralizer (Q : Set G))).map
      (centralizer (Q : Set G)).subtype).map f =
      (pResidual p (centralizer (Q.map f : Set H))).map
        (centralizer (Q.map f : Set H)).subtype := by
  let actionG : MulDistribMulAction Q G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp Q.subtype)
  let actionH : MulDistribMulAction Q H :=
    MulDistribMulAction.compHom H (MulAut.conj.comp (f.comp Q.subtype))
  let : MulAction Q G := actionG.toMulAction
  let : SMul Q G := actionG.toSMul
  let : MulAction Q H := actionH.toMulAction
  let : SMul Q H := actionH.toSMul
  have heq (a : Q) (x : G) : f (a • x) = a • f x := by
    change f ((a : G) * x * (a : G)⁻¹) = f a * f x * (f a)⁻¹
    simp only [map_mul, map_inv]
  have hfixG : @FixedPoints.subgroup Q G _ _ actionG = centralizer (Q : Set G) := by
    ext x
    change (∀ a : Q, (a : G) * x * (a : G)⁻¹ = x) ↔ ∀ a ∈ Q, a * x = x * a
    simp only [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.property⟩
  have hfixH : @FixedPoints.subgroup Q H _ _ actionH = centralizer (Q.map f : Set H) := by
    ext x
    change (∀ a : Q, f a * x * (f a)⁻¹ = x) ↔ ∀ a ∈ Q.map f, a * x = x * a
    simp only [mul_inv_eq_iff_eq_mul]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      exact h ⟨a, ha⟩
    · intro h a
      exact h _ (mem_map_of_mem f a.property)
  have h := @FixedPoints.map_embedded_fixedResidual_of_central_pgroup_ker
    Q G H _ _ _ actionG actionH _ p _ f hf hc hp heq
  rw [hfixG, hfixH] at h
  exact h

end Subgroup
