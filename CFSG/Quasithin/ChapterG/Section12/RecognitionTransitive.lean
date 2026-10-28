module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionOrbits
public import Theory.LinearAlgebra.AlternatingPlane
/-!
# Transitive recognition above binary degree four

Fix two good centers with pairing one. If the first point radical acts
faithfully on its perpendicular hyperplane, its two regular outside orbits
give coordinates on the perpendicular complement of the chosen plane.
The binary coordinate satisfies the quadratic addition law with polar form
B, and is invariant under the pointwise plane stabilizer.

When every nonzero vector is good, each complement vector is a transvection
center. In dimension at least six one can choose an independent perpendicular
vector and realize a transvection fixing the chosen plane. Invariance forces
the coordinate of every center to vanish, making the complement isotropic.
Its dimension d-2 contradicts the isotropic dimension bound. Thus the point
radical has a nontrivial hyperplane kernel, and the already proved G.12.5
identifies the whole group with the full symplectic group.

This is a direct local proof of the transitive branch used in G.12.1 and
G.12.9 (Aschbacher--Smith, printed pp.370--373). It retains the literal point
radicals and requires no classification of abstract group-family labels.
-/

public noncomputable section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section12
namespace TransitiveRecognition
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {D : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
  {u v : V} {hB : B.IsAlt}

include hB in
private theorem swap (x y : V) : B x y=B y x := by
  rw [← hB.neg_eq x y]
  exact (show ∀ a : ZMod 2,-a=a from by decide) _ |>.symm

private theorem double (x : V) : x+x=0 := by
  have hh : (2 : ZMod 2) • x=0 := by rw [show (2 : ZMod 2)=0 from by decide,zero_smul]
  simpa only [two_smul] using hh

private abbrev C (B : LinearMap.BilinForm (ZMod 2) V) (u v : V) :=
  (B u).ker ⊓ (B v).ker

private theorem C_left (x : C B u v) : B u x=0 := x.property.1
private theorem C_right (x : C B u v) : B v x=0 := x.property.2

include hB in
private theorem complement_dimension [FiniteDimensional (ZMod 2) V] (hnd : B.Nondegenerate) (huv : B u v=1) :
    finrank (ZMod 2) (C B u v)+2=finrank (ZMod 2) V := by
  have hp := B.span_pair_nondegenerate_of_pairing_ne_zero hB u v (huv ▸ one_ne_zero)
  have hc : C B u v=B.orthogonal (Submodule.span (ZMod 2) {u,v}) := by
    ext x
    constructor
    · rintro ⟨hu,hv⟩ y hy
      change B u x=0 at hu
      change B v x=0 at hv
      obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hy
      simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,hu,hv,
        smul_zero,add_zero]
    · intro hx
      exact ⟨hx u (Submodule.subset_span (by simp)),hx v (Submodule.subset_span (by simp))⟩
  rw [hc,B.finrank_orthogonal hnd,hp.1]
  have hh := Submodule.finrank_le (Submodule.span (ZMod 2) {u,v})
  rw [hp.1] at hh
  omega

private def project (huv : B u v=1) : V →ₗ[ZMod 2] C B u v :=
  (LinearMap.id - (B v).smulRight u - (B u).smulRight v).codRestrict _ (by
    intro x
    have hvu : B v u=1 := (swap (hB := hB) v u).trans huv
    change B u (x-B v x • u-B u x • v)=0 ∧ B v (x-B v x • u-B u x • v)=0
    constructor <;>
      simp [map_sub,map_smul,hB u,hB v,huv,hvu])

private theorem project_apply (huv : B u v=1) (x : V) :
    (project (hB := hB) huv x : V)=x-B v x • u-B u x • v := rfl

private theorem project_u (huv : B u v=1) : project (hB := hB) huv u=0 := by
  apply Subtype.ext
  rw [project_apply,swap (hB := hB) v u,huv,hB u,one_smul,zero_smul,sub_self,sub_zero]
  rfl
private theorem project_v (huv : B u v=1) : project (hB := hB) huv v=0 := by
  apply Subtype.ext
  rw [project_apply,huv,hB v,one_smul,zero_smul,sub_zero,sub_self]
  rfl
private theorem project_mem (huv : B u v=1) (x : C B u v) :
    project (hB := hB) huv x=x := by
  apply Subtype.ext
  simp only [project_apply,C_left,C_right,zero_smul,sub_zero]

private theorem radical_action (hD : D≤formStabilizer B) (huv : B u v=1)
    (a : pointRadical D B v) {x : V} (hx : B v x=0) :
    a.val x=x+B (a.val u-u) x • v := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (a.property.2.2.2 x hx)
  have hax : a.val x=x+c • v := by rw [hc]; abel
  have hpair : B (a.val u) v=1 := by
    have hh := hD a.property.1 u v
    rw [a.property.2.1] at hh
    exact hh.trans huv
  have he := hD a.property.1 u x
  rw [hax,map_add,map_smul,smul_eq_mul,hpair,mul_one] at he
  have hc' : B (a.val u-u) x=c := by
    rw [map_sub,LinearMap.sub_apply]
    have hh : c+c=0 := double c
    linear_combination he - hh
  rw [hc',hax]

private theorem radical_conjugate (hD : D≤formStabilizer B)
    {g : V ≃ₗ[ZMod 2] V} (hg : g∈D) (hgv : g v=v)
    (a : pointRadical D B v) : g*a.val*g⁻¹∈pointRadical D B v := by
  have hgi : g.symm v=v := (congrArg g.symm hgv).symm.trans (g.symm_apply_apply v)
  apply (mem_pointRadical_iff hD).mpr
  refine ⟨D.mul_mem (D.mul_mem hg a.property.1) (D.inv_mem hg),?_,?_⟩
  · change g (a.val (g.symm v))=v
    rw [hgi,a.property.2.1,hgv]
  · intro x hx
    have hi : B v (g.symm x)=0 := by
      have hh := hD hg v (g.symm x)
      rw [hgv,g.apply_symm_apply] at hh
      exact hh.symm.trans hx
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (a.property.2.2.2 (g.symm x) hi)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    have hh := congrArg g hc
    simpa only [map_sub,map_smul,g.apply_symm_apply,hgv,LinearEquiv.mul_apply,
      LinearEquiv.coe_inv] using hh

variable [FiniteDimensional (ZMod 2) V]
variable (hv : GoodVector D B hB v) (hnd : B.Nondegenerate) (hD : D≤formStabilizer B)
  (hf : ∀ a∈pointRadical D B v,(∀ w,B v w=0 → a w=w) → a=1)
  (huv : B u v=1)

private def coordinates (x : C B u v) : pointRadical D B v × ZMod 2 :=
  Classical.choose (hv.radical_pair_exists_unique hnd hD hf
    ((swap (hB := hB) v u).trans huv)
    (by rw [map_add,x.property.2,add_zero]; exact (swap (hB := hB) v u).trans huv :
      B v (u+x.val)=1))

private theorem coordinates_eq (x : C B u v) :
    (coordinates hv hnd hD hf huv x).1.val
      (u+(coordinates hv hnd hD hf huv x).2 • v)=u+x.val :=
  (Classical.choose_spec (hv.radical_pair_exists_unique hnd hD hf
    ((swap (hB := hB) v u).trans huv)
    (by rw [map_add,x.property.2,add_zero]; exact (swap (hB := hB) v u).trans huv :
      B v (u+x.val)=1))).1

private theorem coordinates_action (x : C B u v) :
    (coordinates hv hnd hD hf huv x).1.val u=
      u+x.val+(coordinates hv hnd hD hf huv x).2 • v := by
  have hh := coordinates_eq hv hnd hD hf huv x
  rw [map_add,map_smul,(coordinates hv hnd hD hf huv x).1.property.2.1] at hh
  calc
    _ = ((coordinates hv hnd hD hf huv x).1.val u+
        (coordinates hv hnd hD hf huv x).2 • v)+
        (coordinates hv hnd hD hf huv x).2 • v := by rw [add_assoc,double,add_zero]
    _ = _ := congrArg (·+(coordinates hv hnd hD hf huv x).2 • v) hh

private theorem coordinates_unique (x : C B u v) (a : pointRadical D B v) (c : ZMod 2)
    (ha : a.val u=u+x.val+c • v) :
    (coordinates hv hnd hD hf huv x).2=c := by
  have hh : a.val (u+c • v)=u+x.val := by
    rw [map_add,map_smul,a.property.2.1,ha,add_assoc,double,add_zero]
  exact (hv.radical_pair_unique hD hf ((swap (hB := hB) v u).trans huv)
    ((coordinates_eq hv hnd hD hf huv x).trans hh.symm)).2

private theorem coordinate_add (x y : C B u v) :
    (coordinates hv hnd hD hf huv (x+y)).2=
      (coordinates hv hnd hD hf huv x).2+(coordinates hv hnd hD hf huv y).2+B x y := by
  let a := (coordinates hv hnd hD hf huv x).1
  let b := (coordinates hv hnd hD hf huv y).1
  apply coordinates_unique hv hnd hD hf huv (x+y) (a*b)
  change a.val (b.val u)=_
  rw [coordinates_action hv hnd hD hf huv y,map_add,map_add,map_smul,a.property.2.1,
    radical_action hD huv a y.property.2,coordinates_action hv hnd hD hf huv x]
  have hxy : B (u+x.val+(coordinates hv hnd hD hf huv x).2 • v-u) y=B x y := by
    simp only [map_sub,map_add,map_smul,LinearMap.sub_apply,LinearMap.add_apply,
      LinearMap.smul_apply,C_left y,C_right y,smul_zero,zero_add,add_zero,sub_zero]
  rw [hxy]
  simp only [Submodule.coe_add,add_smul]
  abel


private theorem coordinate_invariant (x y : C B u v)
    {g : V ≃ₗ[ZMod 2] V} (hg : g∈D) (hgu : g u=u) (hgv : g v=v)
    (hxy : g x=y) :
    (coordinates hv hnd hD hf huv y).2=(coordinates hv hnd hD hf huv x).2 := by
  let a := (coordinates hv hnd hD hf huv x).1
  let b : pointRadical D B v := ⟨g*a.val*g⁻¹,radical_conjugate hD hg hgv a⟩
  apply coordinates_unique hv hnd hD hf huv y b
  have hgi : g.symm u=u := (congrArg g.symm hgu).symm.trans (g.symm_apply_apply u)
  change g (a.val (g.symm u))=_
  rw [hgi,coordinates_action hv hnd hD hf huv x,map_add,map_add,map_smul,hgu,hgv,hxy]

include hnd huv hB in
private theorem perpendicular_witness (hd : 6≤finrank (ZMod 2) V)
    (z : C B u v) (hz : z≠0) :
    ∃ w : C B u v, B z w=0 ∧ w∉Submodule.span (ZMod 2) {z} := by
  let f : Module.Dual (ZMod 2) (C B u v) := (B z).comp (C B u v).subtype
  have hc := complement_dimension (hB := hB) hnd huv
  have hf := f.finrank_range_add_finrank_ker
  have hr := f.range.finrank_le
  rw [Module.finrank_self] at hr
  have hn : ¬f.ker≤Submodule.span (ZMod 2) {z} := by
    intro hl
    have hh := Submodule.finrank_mono hl
    rw [finrank_span_singleton hz] at hh
    omega
  obtain ⟨w,hw,hn⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨w,hw,hn⟩

private theorem coordinate_zero_of_good
    (hd : 6≤finrank (ZMod 2) V) (z : C B u v)
    (hz : GoodVector D B hB z.val) :
    (coordinates hv hnd hD hf huv z).2=0 := by
  obtain ⟨w,hzw,hwn⟩ := perpendicular_witness (hB := hB) hnd huv hd z
    (fun he => hz.nonzero (congrArg Subtype.val he))
  obtain ⟨φ,hφw,hφ⟩ := (Submodule.span (ZMod 2) {z}).exists_le_ker_of_notMem hwn
  have hφz : φ z=0 := hφ (Submodule.mem_span_singleton_self z)
  have hφw1 : φ w=1 := (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _ |>.resolve_left hφw
  let ψ : Module.Dual (ZMod 2) (B z.val).ker :=
    (φ.comp (project (hB := hB) huv)).comp (B z.val).ker.subtype
  have hψ : ψ ⟨z.val,hB z.val⟩=0 := by
    change φ (project (hB := hB) huv z.val)=0
    rw [project_mem,hφz]
  obtain ⟨a,ha⟩ := hz.full ψ hψ
  have hzu : B z.val u=0 := (swap (hB := hB) z.val u).trans (C_left z)
  have hzv : B z.val v=0 := (swap (hB := hB) z.val v).trans (C_right z)
  have hau : a.val u=u := by
    have hh := ha ⟨u,hzu⟩
    change a.val u=u+φ (project (hB := hB) huv u) • z.val at hh
    simpa only [project_u,map_zero,zero_smul,add_zero] using hh
  have hav : a.val v=v := by
    have hh := ha ⟨v,hzv⟩
    change a.val v=v+φ (project (hB := hB) huv v) • z.val at hh
    simpa only [project_v,map_zero,zero_smul,add_zero] using hh
  have haw : a.val w=w.val+z.val := by
    have hh := ha ⟨w.val,hzw⟩
    change a.val w=w.val+φ (project (hB := hB) huv w.val) • z.val at hh
    simpa only [project_mem,hφw1,one_smul] using hh
  have he := coordinate_invariant hv hnd hD hf huv w (w+z) a.property.1 hau hav haw
  have hadd := coordinate_add hv hnd hD hf huv w z
  have hwz : B w z=0 := (swap (hB := hB) w z).trans hzw
  rw [hwz,add_zero,he] at hadd
  exact (add_eq_left.mp hadd.symm)

include hv hnd hD hf huv in
/-- A faithful point radical is incompatible with all vectors being good
in dimension at least six. Its complement coordinates have quadratic polar
form B, but the other good point radicals force every quadratic value zero. -/
private theorem not_all_good_of_faithful (hd : 6≤finrank (ZMod 2) V)
    (hall : ∀ z : V,z≠0 → GoodVector D B hB z) : False := by
  have hzero (z : C B u v) : (coordinates hv hnd hD hf huv z).2=0 := by
    by_cases hz : z=0
    · subst z
      apply coordinates_unique hv hnd hD hf huv 0 1 0
      simp
    · exact coordinate_zero_of_good hv hnd hD hf huv hd z
        (hall z (fun he => hz (Subtype.ext he)))
  have hiso : ∀ x∈C B u v,∀ y∈C B u v,B x y=0 := by
    intro x hx y hy
    have hh := coordinate_add hv hnd hD hf huv ⟨x,hx⟩ ⟨y,hy⟩
    rw [hzero,hzero,hzero,zero_add,zero_add] at hh
    exact hh.symm
  have hh := B.twice_finrank_le_of_isotropic hnd (C B u v) hiso
  have hc := complement_dimension (hB := hB) hnd huv
  omega

end TransitiveRecognition

/-- In degree at least six, transitivity on nonzero vectors and the full
point-radical transvection action force the full symplectic group. -/
theorem ClassificationHypotheses.eq_formStabilizer_of_transitive_ge_six
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {D : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    {u v : V} (h : ClassificationHypotheses D B u v)
    (hd : 6≤finrank (ZMod 2) V)
    (ht : ∀ x : V,x≠0 → ∃ a∈D,a v=x) : D=formStabilizer B := by
  by_contra hn
  have hf : ∀ a∈pointRadical D B v,(∀ w,B v w=0 → a w=w) → a=1 := by
    intro a ha hh
    by_contra hne
    exact hn (h.eq_formStabilizer_of_radical_kernel ⟨a,ha,hne,hh⟩)
  have hall (x : V) (hx : x≠0) : GoodVector D B h.alternating x := by
    obtain ⟨a,ha,rfl⟩ := ht x hx
    exact h.good_v.conjugate h.preserves ha
  have huv : B u v=1 := (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _ |>.resolve_left h.pairing
  exact TransitiveRecognition.not_all_good_of_faithful h.good_v h.nondegenerate h.preserves
    hf huv hd hall
end CFSG.Quasithin.ChapterG.Section12
