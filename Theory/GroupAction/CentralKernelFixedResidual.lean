module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom

/-!
# Fixed residuals under a central prime-power quotient

An equivariant surjection with central p-group kernel maps the p-residual
of its fixed subgroup onto the fixed-subgroup p-residual in the quotient.
On the inverse image of the quotient fixed subgroup, the displacement
x ↦ a(x)x⁻¹ is a homomorphism into the kernel. It vanishes on the
p-residual, which therefore consists of genuine fixed points upstairs.
Surjectivity then follows from preservation of residuals under finite
surjections. No splitting or coprimality of the automorphism order is used.

This supplies the projection step for the four-cover calculations in
Aschbacher--Smith 15.3.38, printed p.1137 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- Restrict a compatible homomorphism to the actual fixed subgroups. -/
@[expose] def fixedSubgroupMap (a : MulAut G) (b : MulAut H) (f : G →* H)
    (heq : ∀ x, f (a x) = b (f x)) : a.fixedSubgroup →* b.fixedSubgroup :=
  (f.comp a.fixedSubgroup.subtype).codRestrict b.fixedSubgroup (fun x => by
    rw [mem_fixedSubgroup]
    change b (f x) = f x
    rw [← heq, (mem_fixedSubgroup _ _).mp x.property])

/-- A central p-group quotient preserves the fixed-subgroup p-residual. -/
theorem map_fixedResidual_of_central_pgroup_ker [Finite G] (p : ℕ) [Fact p.Prime]
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (hp : IsPGroup p f.ker) (heq : ∀ x, f (a x) = b (f x)) :
    (pResidual p a.fixedSubgroup).map (fixedSubgroupMap a b f heq) =
      pResidual p b.fixedSubgroup := by
  let P := b.fixedSubgroup.comap f
  have hdmem (x : P) : a x * (x : G)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq]
    have hx : b (f x) = f x := (mem_fixedSubgroup _ _).mp x.property
    rw [hx, mul_inv_cancel]
  let d : P →* f.ker := {
    toFun x := ⟨a x * (x : G)⁻¹, hdmem x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change a ((x : G) * y) * ((x : G) * y)⁻¹ =
        (a x * (x : G)⁻¹) * (a y * (y : G)⁻¹)
      have hy := mem_center_iff.mp (hc (hdmem y)) (x : G)⁻¹
      rw [map_mul, mul_inv_rev]
      calc
        _ = a x * ((a y * (y : G)⁻¹) * (x : G)⁻¹) := by group
        _ = a x * ((x : G)⁻¹ * (a y * (y : G)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hd : d.comp (pResidual p P).subtype = 1 :=
    (isPPerfect_pResidual p).hom_eq_one_of_isPGroup hp _
  have hrfix (x : pResidual p P) : ((x : P) : G) ∈ a.fixedSubgroup := by
    have h := congrArg (fun k : pResidual p P →* f.ker => (k x : G)) hd
    change a ((x : P) : G) * ((x : P) : G)⁻¹ = 1 at h
    exact (mem_fixedSubgroup _ _).mpr (mul_inv_eq_one.mp h)
  let r : pResidual p P →* a.fixedSubgroup :=
    (P.subtype.comp (pResidual p P).subtype).codRestrict a.fixedSubgroup hrfix
  have hr (x : pResidual p P) : r x ∈ pResidual p a.fixedSubgroup := by
    apply map_pResidual_le p r
    exact mem_map.mpr ⟨x, by
      rw [(pResidual_eq_top_iff p _).mpr (isPPerfect_pResidual p)]; trivial, rfl⟩
  let q : P →* b.fixedSubgroup :=
    (f.comp P.subtype).codRestrict b.fixedSubgroup (fun x => x.property)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ b.fixedSubgroup; rw [hx]; exact y.property⟩,
      Subtype.ext hx⟩
  apply le_antisymm (map_pResidual_le p _) ?_
  intro y hy
  rw [← map_pResidual_of_surjective p q hq] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact mem_map.mpr ⟨r ⟨x, hx⟩, hr ⟨x, hx⟩, hxy⟩
/-- The canonical map between the intrinsic fixed-subgroup residuals. -/
@[expose] def fixedResidualMap (p : ℕ) (a : MulAut G) (b : MulAut H)
    (f : G →* H) (heq : ∀ x, f (a x) = b (f x)) :
    pResidual p a.fixedSubgroup →* pResidual p b.fixedSubgroup :=
  ((fixedSubgroupMap a b f heq).comp (pResidual p a.fixedSubgroup).subtype).codRestrict
    (pResidual p b.fixedSubgroup) (fun x =>
      map_pResidual_le p (fixedSubgroupMap a b f heq)
        (mem_map.mpr ⟨x.val, x.property, rfl⟩))

/-- The residual projection uses the original homomorphism on ambient elements. -/
@[simp] theorem fixedResidualMap_apply (p : ℕ) (a : MulAut G) (b : MulAut H)
    (f : G →* H) (heq : ∀ x, f (a x) = b (f x))
    (x : pResidual p a.fixedSubgroup) :
    (((fixedResidualMap p a b f heq x : pResidual p b.fixedSubgroup) :
      b.fixedSubgroup) : H) = f ((x : a.fixedSubgroup) : G) := rfl

/-- The canonical residual projection is onto for a central p-group kernel. -/
theorem fixedResidualMap_surjective [Finite G] (p : ℕ) [Fact p.Prime]
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (hp : IsPGroup p f.ker) (heq : ∀ x, f (a x) = b (f x)) :
    Function.Surjective (fixedResidualMap p a b f heq) := by
  intro y
  have hy := (map_fixedResidual_of_central_pgroup_ker p a b f hf hc hp heq).ge y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The equality also retains the embeddings in the two ambient groups. -/
theorem map_embedded_fixedResidual_of_central_pgroup_ker [Finite G]
    (p : ℕ) [Fact p.Prime] (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (hp : IsPGroup p f.ker) (heq : ∀ x, f (a x) = b (f x)) :
    ((pResidual p a.fixedSubgroup).map a.fixedSubgroup.subtype).map f =
      (pResidual p b.fixedSubgroup).map b.fixedSubgroup.subtype := by
  rw [← map_fixedResidual_of_central_pgroup_ker p a b f hf hc hp heq,
    map_map, map_map]
  rfl

/-- Centrality of the kernel is inherited by the residual projection. -/
theorem fixedResidualMap_ker_le_center (p : ℕ) (a : MulAut G) (b : MulAut H)
    (f : G →* H) (heq : ∀ x, f (a x) = b (f x))
    (hc : f.ker ≤ center G) :
    (fixedResidualMap p a b f heq).ker ≤ center (pResidual p a.fixedSubgroup) := by
  intro x hx
  have hx' : f ((x : a.fixedSubgroup) : G) = 1 :=
    congrArg (fun z : pResidual p b.fixedSubgroup => ((z : b.fixedSubgroup) : H)) hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  apply Subtype.ext
  exact mem_center_iff.mp (hc hx') ((y : a.fixedSubgroup) : G)

/-- The kernel of the residual projection embeds in the original kernel. -/
theorem fixedResidualMap_ker_isPGroup (p : ℕ) (a : MulAut G) (b : MulAut H)
    (f : G →* H) (heq : ∀ x, f (a x) = b (f x))
    (hp : IsPGroup p f.ker) : IsPGroup p (fixedResidualMap p a b f heq).ker := by
  let r := fixedResidualMap p a b f heq
  let j : r.ker →* f.ker := {
    toFun x := ⟨((x.val : a.fixedSubgroup) : G),
      congrArg (fun z : pResidual p b.fixedSubgroup => ((z : b.fixedSubgroup) : H))
        x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply hp.of_injective j
  intro x y h
  have hval : ((x.val : a.fixedSubgroup) : G) = ((y.val : a.fixedSubgroup) : G) :=
    congrArg (fun z : f.ker => (z : G)) h
  exact Subtype.ext (Subtype.ext (Subtype.ext hval))

end MulAut

