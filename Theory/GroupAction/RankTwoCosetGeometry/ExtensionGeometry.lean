module
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity
/-!
# Coset geometry of an extension with common inner representatives

Suppose a homomorphism has the prescribed preimages of both parabolics, and
every target element has a representative in its image modulo both parabolics
simultaneously. It induces a type-preserving graph isomorphism: preimages
prove injectivity, and common representatives prove surjectivity and reflect
incidence. The map intertwines the actual actions. Equivariant graph
isomorphisms then carry rooted nonbacktracking-path transitivity to the
larger acting group, without requiring surjectivity on groups.

Source: the extension geometry in Aschbacher–Smith F.4.3–5, pp.274–275.
-/

@[expose] public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo.ExtensionGeometry
variable {A B : Type*} [Group A] [Group B]
variable (P : Bool → Subgroup A) (Q : Bool → Subgroup B) (f : A →* B)
variable (hpre : ∀ i, (Q i).comap f = P i)
variable (hrep : ∀ b : B, ∃ a : A, (f a)⁻¹ * b ∈ Q false ⊓ Q true)

def coset (i : Bool) : A ⧸ P i → B ⧸ Q i :=
  Quotient.map f (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [←map_inv, ←map_mul]
    change a⁻¹ * b ∈ (Q i).comap f
    rw [hpre]
    exact QuotientGroup.leftRel_apply.mp hab)

theorem coset_injective (i : Bool) : Function.Injective (coset P Q f hpre i) := by
  intro x y he
  obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective y
  apply QuotientGroup.eq.mpr
  rw [←hpre]
  change f (a⁻¹ * b) ∈ Q i
  rw [map_mul, map_inv]
  exact QuotientGroup.eq.mp he

include hrep in
theorem representative (b : B) : ∃ a : A, ∀ i, (f a : B ⧸ Q i) = (b : B ⧸ Q i) := by
  obtain ⟨a,ha⟩ := hrep b
  refine ⟨a,fun i => QuotientGroup.eq.mpr ?_⟩
  cases i
  · exact ha.1
  · exact ha.2

def vertex (v : Vertex P) : Vertex Q := ⟨v.type, coset P Q f hpre v.type v.coset⟩

@[simp] theorem vertex_mk (i : Bool) (a : A) :
    vertex P Q f hpre (mkVertex P i a) = mkVertex Q i (f a) := rfl

@[simp] theorem vertex_base (i : Bool) :
    vertex P Q f hpre (base P i) = base Q i := by
  change mkVertex Q i (f 1) = mkVertex Q i 1
  rw [map_one]

@[simp] theorem vertex_smul (a : A) (v : Vertex P) :
    vertex P Q f hpre (a • v) = f a • vertex P Q f hpre v := by
  rcases v with ⟨i,q⟩
  obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective q
  change vertex P Q f hpre (a • mkVertex P i b) = f a • vertex P Q f hpre (mkVertex P i b)
  rw [smul_mkVertex, vertex_mk, vertex_mk, smul_mkVertex, map_mul]

include hrep in
theorem vertex_bijective : Function.Bijective (vertex P Q f hpre) := by
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    have ht := congrArg (fun v : Vertex Q => v.type) he
    change i = j at ht
    subst j
    have hc : coset P Q f hpre i x = coset P Q f hpre i y := by
      simpa only [vertex, CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and] using he
    exact congrArg (CosetGeometry.Vertex.mk i) (coset_injective P Q f hpre i hc)
  · rintro ⟨i,q⟩
    obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a,ha⟩ := representative Q f hrep b
    exact ⟨mkVertex P i a, congrArg (CosetGeometry.Vertex.mk i) (ha i)⟩

def graphIso : graph P ≃g graph Q where
  toEquiv := Equiv.ofBijective (vertex P Q f hpre) (vertex_bijective P Q f hpre hrep)
  map_rel_iff' := by
    intro v w
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨b,hv,hw⟩
      obtain ⟨a,ha⟩ := representative Q f hrep b
      exact ⟨a,coset_injective P Q f hpre v.type ((ha v.type).trans hv),
        coset_injective P Q f hpre w.type ((ha w.type).trans hw)⟩
    · rintro ⟨a,hv,hw⟩
      exact ⟨f a,congrArg (coset P Q f hpre v.type) hv,
        congrArg (coset P Q f hpre w.type) hw⟩
end Subgroup.CosetGeometry.RankTwo.ExtensionGeometry

namespace SimpleGraph.PathTransitivePolygon.RootPathTransitive
variable {V W A B : Type*} [Group A] [Group B] [MulAction A V] [MulAction B W]
variable {Γ : SimpleGraph V} {Δ : SimpleGraph W}
theorem map_graphIso (e : Γ ≃g Δ) (f : A →* B)
    (he : ∀ a v, e (a • v) = f a • e v)
    {v : V} {n : ℕ} (ht : RootPathTransitive Γ A v n) :
    RootPathTransitive Δ B (e v) n := by
  intro p q hp hq
  let ep := BasedWalk.coveringEquiv e.toHom (fun v => (e.mapNeighborSet v).bijective) n v
  let p' := ep.symm p
  let q' := ep.symm q
  have hpm : p'.map e.toHom = p := (BasedWalk.coveringEquiv_apply _ _ _).symm.trans (ep.apply_symm_apply p)
  have hqm : q'.map e.toHom = q := (BasedWalk.coveringEquiv_apply _ _ _).symm.trans (ep.apply_symm_apply q)
  have hp' : p'.Nonbacktracking := (BasedWalk.nonbacktracking_map_iff e.toHom
    (fun v => (e.mapNeighborSet v).injective) p').mp (hpm.symm ▸ hp)
  have hq' : q'.Nonbacktracking := (BasedWalk.nonbacktracking_map_iff e.toHom
    (fun v => (e.mapNeighborSet v).injective) q').mp (hqm.symm ▸ hq)
  obtain ⟨a,hav,ha⟩ := ht p' q' hp' hq'
  refine ⟨f a, (he a v).symm.trans (congrArg e hav), ?_⟩
  have hl := congrArg (List.map e) ha
  rw [List.map_map] at hl
  rw [←hpm,←hqm,BasedWalk.vertices_map,BasedWalk.vertices_map,List.map_map]
  exact (List.map_congr_left (fun x _ => (he a x).symm)).trans hl
end SimpleGraph.PathTransitivePolygon.RootPathTransitive
