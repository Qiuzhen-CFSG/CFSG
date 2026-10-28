module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates

/-!
# Positive-root relations sufficient to split the symplectic Sylow subgroup

The ordered product x₆(b)x₀(k)x₄(w)x₂(v) has multiplication law
(b,k,w,v)(c,l,t,a) = (b+c,k+l+c²v,w+t+cv,v+a) in characteristic two.
Additivity, the five commuting pairs, and the x₂–x₆ crossing relation
therefore define a homomorphism from the actual matrix unipotent subgroup.
The four projection equations make this homomorphism a section.

Coordinates are taken from `CentralRootGeometry.element`; its second
coordinate is k+bw, so the construction uses its proved bijection and
multiplication law. Thus no identification with an abstract presentation is
assumed. The separate construction in `FieldFour.Relations` supplies compatible
lifted roots over every finite characteristic-two field of order greater than
two, including the field of order four.

Source: the type-C₂ root calculation underlying Aschbacher–Smith I.1.3,
printed p.407, and its cited multiplier source GLS98 §6.1.
-/

public section

open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary

variable {F E : Type*} [Field F] [Group E]

/-- Four additive root sections with the five commuting pairs and the
remaining C₂ crossing relation, in the existing matrix-root numbering.
`FieldFour.Relations` constructs these data in surjective central extensions. -/
structure PositiveRootLifts (f : E →* Sp F) where
  x6 : Multiplicative F →* E
  x0 : Multiplicative F →* E
  x4 : Multiplicative F →* E
  x2 : Multiplicative F →* E
  project6 : f.comp x6 = RootSubgroup.parameter 6
  project0 : f.comp x0 = RootSubgroup.parameter 0
  project4 : f.comp x4 = RootSubgroup.parameter 4
  project2 : f.comp x2 = RootSubgroup.parameter 2
  commute60 : ∀ b k : F, Commute (x6 (.ofAdd b)) (x0 (.ofAdd k))
  commute64 : ∀ b w : F, Commute (x6 (.ofAdd b)) (x4 (.ofAdd w))
  commute04 : ∀ k w : F, Commute (x0 (.ofAdd k)) (x4 (.ofAdd w))
  commute02 : ∀ k v : F, Commute (x0 (.ofAdd k)) (x2 (.ofAdd v))
  commute42 : ∀ w v : F, Commute (x4 (.ofAdd w)) (x2 (.ofAdd v))
  crossing : ∀ v c : F,
    x2 (.ofAdd v) * x6 (.ofAdd c) =
      x6 (.ofAdd c) * x0 (.ofAdd (c^2*v)) * x4 (.ofAdd (c*v)) * x2 (.ofAdd v)

namespace PositiveRootLifts
variable {f : E →* Sp F} (L : PositiveRootLifts f)

private def product (b k w v : F) : E :=
  L.x6 (.ofAdd b) * L.x0 (.ofAdd k) * L.x4 (.ofAdd w) * L.x2 (.ofAdd v)

private theorem add_left (x : Multiplicative F →* E) (s t : F) (z : E) :
    x (.ofAdd s) * (x (.ofAdd t) * z) = x (.ofAdd (s+t)) * z := by
  rw [← mul_assoc, ← map_mul]
  rfl

private theorem product_mul (b k w v c l t a : F) :
    L.product b k w v * L.product c l t a =
      L.product (b+c) (k+l+c^2*v) (w+t+c*v) (v+a) := by
  simp only [product, mul_assoc]
  rw [← mul_assoc (L.x2 (.ofAdd v)) (L.x6 (.ofAdd c)), L.crossing]
  simp only [mul_assoc]
  rw [(L.commute64 c w).symm.left_comm, (L.commute60 c k).symm.left_comm]
  rw [(L.commute02 l v).symm.left_comm, (L.commute42 t v).symm.left_comm]
  rw [(L.commute04 (c^2*v) w).symm.left_comm]
  rw [(L.commute04 l (c*v)).symm.left_comm, (L.commute04 l w).symm.left_comm]
  rw [add_left, add_left, add_left, add_left, add_left, ← map_mul]
  change L.x6 (.ofAdd (b+c)) * (L.x0 (.ofAdd (k+c^2*v+l)) *
    (L.x4 (.ofAdd (w+c*v+t)) * L.x2 (.ofAdd (v+a)))) = _
  simp only [add_assoc, add_left_comm, add_comm]

include L in
/-- The full set of positive-root relations constructs a homomorphic section
of the concrete unipotent subgroup. This proves the local presentation
sufficiency; it does not assert the existence of the lifted-root data. -/
theorem exists_unipotent_section [Finite F] [CharP F 2] :
    ∃ s : unipotent (F := F) →* E, f.comp s = (unipotent (F := F)).subtype := by
  let e : (F × F × F × F) ≃ unipotent (F := F) := Equiv.ofBijective
    (fun p => CentralRootGeometry.element p.1 p.2.1 p.2.2.1 p.2.2.2)
    ⟨CentralRootGeometry.element_injective, CentralRootGeometry.element_surjective⟩
  let j : unipotent (F := F) → E := fun g =>
    let p := e.symm g
    L.product p.1 (p.2.1 + p.1*p.2.2.1) p.2.2.1 p.2.2.2
  have hj (b u w v : F) : j (CentralRootGeometry.element b u w v) =
      L.product b (u+b*w) w v := by
    change L.product (e.symm (e (b,u,w,v))).1
      ((e.symm (e (b,u,w,v))).2.1 + (e.symm (e (b,u,w,v))).1 *
        (e.symm (e (b,u,w,v))).2.2.1)
      (e.symm (e (b,u,w,v))).2.2.1 (e.symm (e (b,u,w,v))).2.2.2 = _
    rw [e.symm_apply_apply]
  have hjone : j 1 = 1 := by
    rw [← CentralRootGeometry.element_zero, hj]
    simp [product]
  have hjmul (x y : unipotent (F := F)) : j (x*y) = j x*j y := by
    obtain ⟨⟨b,u,w,v⟩, rfl⟩ := CentralRootGeometry.element_surjective x
    obtain ⟨⟨c,z,t,a⟩, rfl⟩ := CentralRootGeometry.element_surjective y
    rw [CentralRootGeometry.element_mul, hj, hj, hj, L.product_mul]
    congr 1 <;> ring_nf
    simp [CharTwo.two_eq_zero]
  refine ⟨{toFun := j, map_one' := hjone, map_mul' := hjmul}, ?_⟩
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨b,u,w,v⟩, rfl⟩ := CentralRootGeometry.element_surjective g
  change f (j (CentralRootGeometry.element b u w v)) = _
  rw [hj]
  simp only [product, map_mul]
  simp only [← MonoidHom.comp_apply, L.project6, L.project0, L.project4, L.project2]
  rfl

end PositiveRootLifts

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary

end
