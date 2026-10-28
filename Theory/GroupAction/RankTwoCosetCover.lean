module

public import Theory.GroupAction.RankTwoCosetGeometry

/-!
# Coverings of rank-two coset graphs

A surjective homomorphism inducing isomorphisms on both vertex groups and
mapping their intersection onto the target intersection induces a covering of
the coset graphs. Neighbors at a standard vertex have representatives in its
vertex group. Intersection preservation and injectivity on that group give
unique local lifts; translation gives the result at every vertex.

The graph, action, stabilizers, two coset orbits, connectedness under generation,
and inverse bridge from right cosets are the existing `RankTwoCosetGeometry`
constructions. No finiteness or triviality of the ambient kernel is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition F.3.1 and Lemma F.3.3(2), printed pp.269–270.
-/

@[expose] public section
namespace Subgroup.CosetGeometry.RankTwo
variable {A B : Type*} [Group A] [Group B]
variable (F : Bool → Subgroup A) (E : Bool → Subgroup B)

def mkVertex (i : Bool) (a : A) : Vertex F := ⟨i, (a : A ⧸ F i)⟩

@[simp] theorem mkVertex_eq (i : Bool) (a b : A) :
    mkVertex F i a = mkVertex F i b ↔ a⁻¹ * b ∈ F i := by
  simp only [mkVertex, CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and, QuotientGroup.eq]

@[simp] theorem smul_mkVertex (i : Bool) (a b : A) :
    a • mkVertex F i b = mkVertex F i (a * b) := by
  exact congrArg (CosetGeometry.Vertex.mk i) (MulAction.Quotient.smul_mk (F i) a b)

theorem neighbor_base_rep (i : Bool) {v : Vertex F} (hv : (graph F).Adj (base F i) v) :
    ∃ a ∈ F i, mkVertex F (!i) a = v := by
  obtain ⟨a, ha, hq⟩ := (incident_base_iff F i v).mp hv.2
  refine ⟨a, ha, ?_⟩
  rcases v with ⟨j, q⟩
  have hj : j = !i := by
    have ht := hv.1
    cases i <;> cases j <;> simp_all
  subst j
  exact congrArg (CosetGeometry.Vertex.mk (!i)) hq

structure CoverData (f : A →* B) : Prop where
  surjective : Function.Surjective f
  map_eq : ∀ i, (F i).map f = E i
  injective : ∀ i, Function.Injective (fun a : F i => f a)
  map_inf : (F false ⊓ F true).map f = E false ⊓ E true

namespace CoverData
variable {F E} {f : A →* B} (c : CoverData F E f)
include c

def coset (i : Bool) : A ⧸ F i → B ⧸ E i :=
  Quotient.map f (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul, ← c.map_eq i]
    exact mem_map.mpr ⟨_, QuotientGroup.leftRel_apply.mp hab, rfl⟩)

def vertex (v : Vertex F) : Vertex E := ⟨v.type, c.coset v.type v.coset⟩

@[simp] theorem vertex_mk (i : Bool) (a : A) :
    c.vertex (mkVertex F i a) = mkVertex E i (f a) := rfl

@[simp] theorem vertex_base (i : Bool) : c.vertex (base F i) = base E i := by
  change mkVertex E i (f 1) = mkVertex E i 1
  rw [map_one]

@[simp] theorem vertex_smul (a : A) (v : Vertex F) :
    c.vertex (a • v) = f a • c.vertex v := by
  rcases v with ⟨i, q⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  change c.vertex (a • mkVertex F i b) = f a • c.vertex (mkVertex F i b)
  rw [smul_mkVertex, vertex_mk, vertex_mk, smul_mkVertex, map_mul]

def hom : graph F →g graph E where
  toFun := c.vertex
  map_rel' := by
    intro v w h
    refine ⟨h.1, ?_⟩
    obtain ⟨a, hv, hw⟩ := h.2
    exact ⟨f a, congrArg (c.coset v.type) hv, congrArg (c.coset w.type) hw⟩

theorem vertex_surjective : Function.Surjective c.vertex := by
  rintro ⟨i, q⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, rfl⟩ := c.surjective b
  exact ⟨mkVertex F i a, rfl⟩

theorem map_inf_pair (i : Bool) : (F i ⊓ F (!i)).map f = E i ⊓ E (!i) := by
  cases i
  · exact c.map_inf
  · simpa only [Bool.not_true, inf_comm] using c.map_inf

theorem mem_of_mem_image (i : Bool) {a : A} (ha : a ∈ F i)
    (hf : f a ∈ E (!i)) : a ∈ F (!i) := by
  have hfa : f a ∈ (F i ⊓ F (!i)).map f := by
    rw [c.map_inf_pair]
    exact ⟨by rw [← c.map_eq i]; exact mem_map.mpr ⟨a, ha, rfl⟩, hf⟩
  obtain ⟨b, hb, hba⟩ := mem_map.mp hfa
  have he : (⟨b, hb.1⟩ : F i) = ⟨a, ha⟩ := c.injective i hba
  have h : b = a := congrArg Subtype.val he
  exact h ▸ hb.2

theorem neighbor_base_injective (i : Bool) :
    Function.Injective (c.hom.mapNeighborSet (base F i)) := by
  intro v w he
  obtain ⟨a, ha, hva⟩ := neighbor_base_rep F i v.property
  obtain ⟨b, hb, hwb⟩ := neighbor_base_rep F i w.property
  apply Subtype.ext
  have hm : c.vertex (mkVertex F (!i) a) = c.vertex (mkVertex F (!i) b) := by
    rw [hva, hwb]
    exact congrArg Subtype.val he
  rw [vertex_mk, vertex_mk, mkVertex_eq] at hm
  have hab := c.mem_of_mem_image i ((F i).mul_mem ((F i).inv_mem ha) hb)
    (by simpa only [map_mul, map_inv] using hm)
  exact hva.symm.trans ((mkVertex_eq F (!i) a b).mpr hab) |>.trans hwb

theorem neighbor_base_surjective (i : Bool) :
    Function.Surjective (c.hom.mapNeighborSet (base F i)) := by
  intro w
  have hw : (graph E).Adj (base E i) w.val := by
    have hw := w.property
    change (graph E).Adj (c.vertex (base F i)) w.val at hw
    rwa [vertex_base] at hw
  obtain ⟨b, hb, hwb⟩ := neighbor_base_rep E i hw
  rw [← c.map_eq i] at hb
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
  have hadj : (graph F).Adj (base F i) (mkVertex F (!i) a) := by
    refine ⟨by change i ≠ !i; cases i <;> decide, ?_⟩
    apply (incident_base_iff F i _).mpr
    exact ⟨a, ha, rfl⟩
  refine ⟨⟨mkVertex F (!i) a, hadj⟩, Subtype.ext ?_⟩
  exact hwb

theorem neighbor_bijective (v : Vertex F) : Function.Bijective (c.hom.mapNeighborSet v) := by
  obtain ⟨g, hv⟩ := exists_smul_base F v
  let i := v.type
  have hv' : g • base F i = v := hv
  have undo {w : Vertex F} (hw : (graph F).Adj v w) :
      (graph F).Adj (base F i) (g⁻¹ • w) := by
    have h := (translationGraphIso F g⁻¹).toHom.map_adj hw
    change (graph F).Adj (g⁻¹ • v) (g⁻¹ • w) at h
    simpa only [← hv', inv_smul_smul] using h
  constructor
  · intro w z he
    have he' : c.hom.mapNeighborSet (base F i) ⟨g⁻¹ • w.val, undo w.property⟩ =
        c.hom.mapNeighborSet (base F i) ⟨g⁻¹ • z.val, undo z.property⟩ := by
      apply Subtype.ext
      change c.vertex (g⁻¹ • w.val) = c.vertex (g⁻¹ • z.val)
      rw [vertex_smul, vertex_smul]
      exact congrArg (f g⁻¹ • ·) (congrArg Subtype.val he)
    have he'' := congrArg Subtype.val (c.neighbor_base_injective i he')
    exact Subtype.ext ((MulAction.injective g⁻¹) he'')
  · intro w
    have hw : (graph E).Adj (c.hom (base F i)) ((f g)⁻¹ • w.val) := by
      have h := (translationGraphIso E (f g)⁻¹).toHom.map_adj w.property
      change (graph E).Adj ((f g)⁻¹ • c.vertex v) ((f g)⁻¹ • w.val) at h
      change (graph E).Adj (c.vertex (base F i)) ((f g)⁻¹ • w.val)
      simpa only [← hv', vertex_smul, inv_smul_smul] using h
    obtain ⟨z, hz⟩ := c.neighbor_base_surjective i ⟨(f g)⁻¹ • w.val, hw⟩
    have hzadj : (graph F).Adj v (g • z.val) := by
      have h := (translationGraphIso F g).toHom.map_adj z.property
      change (graph F).Adj (g • base F i) (g • z.val) at h
      rwa [hv'] at h
    refine ⟨⟨g • z.val, hzadj⟩, Subtype.ext ?_⟩
    change c.vertex (g • z.val) = w.val
    rw [vertex_smul]
    have he : c.vertex z.val = (f g)⁻¹ • w.val := congrArg Subtype.val hz
    rw [he, smul_inv_smul]

omit c in
/-- The stabilizer of a represented left coset has its literal conjugate criterion. -/
theorem mem_stabilizer_mk (i : Bool) (a x : A) :
    x ∈ stabilizer F (mkVertex F i a) ↔ a⁻¹ * x * a ∈ F i := by
  change x • mkVertex F i a = mkVertex F i a ↔ _
  rw [smul_mkVertex, mkVertex_eq]
  have h : (x * a)⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by simp [mul_assoc]
  rw [h, inv_mem_iff]

/-- The homomorphism restricted to the actual vertex stabilizers. -/
def stabilizerHom (v : Vertex F) : stabilizer F v →* stabilizer E (c.vertex v) where
  toFun a := ⟨f a, by
    change f (a : A) • c.vertex v = c.vertex v
    rw [← vertex_smul, a.property]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f (a : A) (b : A))

theorem stabilizerHom_bijective (v : Vertex F) : Function.Bijective (c.stabilizerHom v) := by
  rcases v with ⟨i, q⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  change Function.Bijective (c.stabilizerHom (mkVertex F i a))
  constructor
  · intro x y he
    have hx : a⁻¹ * (x : A) * a ∈ F i := (mem_stabilizer_mk i a x).mp x.property
    have hy : a⁻¹ * (y : A) * a ∈ F i := (mem_stabilizer_mk i a y).mp y.property
    have he' : f (x : A) = f (y : A) := congrArg Subtype.val he
    have he'' := c.injective i (a₁ := ⟨_, hx⟩) (a₂ := ⟨_, hy⟩)
      (by change f (a⁻¹ * (x : A) * a) = f (a⁻¹ * (y : A) * a); simp only [map_mul, he'])
    apply Subtype.ext
    have h : a⁻¹ * (x : A) * a = a⁻¹ * (y : A) * a := congrArg Subtype.val he''
    exact mul_left_cancel (mul_right_cancel h)
  · intro y
    have hy : (f a)⁻¹ * (y : B) * f a ∈ E i := by
      apply (mem_stabilizer_mk (F := E) i (f a) y).mp
      exact y.property
    rw [← c.map_eq i] at hy
    obtain ⟨x, hx, hxy⟩ := mem_map.mp hy
    have hx' : a * x * a⁻¹ ∈ stabilizer F (mkVertex F i a) := by
      rw [mem_stabilizer_mk]
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hx
    refine ⟨⟨a * x * a⁻¹, hx'⟩, Subtype.ext ?_⟩
    change f (a * x * a⁻¹) = (y : B)
    simp only [map_mul, map_inv, hxy, mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one]

noncomputable def stabilizerEquiv (v : Vertex F) :
    stabilizer F v ≃* stabilizer E (c.vertex v) :=
  MulEquiv.ofBijective (c.stabilizerHom v) (c.stabilizerHom_bijective v)

end CoverData
end Subgroup.CosetGeometry.RankTwo
