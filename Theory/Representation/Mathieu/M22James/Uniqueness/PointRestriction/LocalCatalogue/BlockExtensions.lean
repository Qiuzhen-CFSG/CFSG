module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.Models

/-!
# Block coordinates for extensions of the two binary SL₃(4) candidates

An extension in chosen vector-space coordinates acts by
`(x,y) ↦ (A(g)x + c(g)y, B(g)y)`. The displayed multiplication identity
on c is exactly what makes this a representation. The central quadratic
relation becomes a single explicit off-diagonal equation. Changing the
linear section gives an actual intertwining equivalence when the two
blocks differ by a coboundary.

These are coordinates for the extension calculation in the local
catalogue, not an enumeration or classification of extensions. That
calculation must supply a finite list of explicit blocks and prove its
coverage. Source context: James (1973), Lemma 8.3; Aschbacher–Smith
H.12.1, printed pp.393–394.
-/

@[expose] public noncomputable section
namespace Representation.SL3FourLocalCatalogue

/-- Off-diagonal blocks satisfying the multiplication law for a module extension. -/
structure BlockCocycle (a b : Constituent) where
  value : SL → W →ₗ[ZMod 2] W
  one : value 1 = 0
  mul (g h : SL) : value (g * h) =
    (constituent a g).comp (value h) + (value g).comp (constituent b h)

namespace BlockCocycle
variable {a b : Constituent}

/-- The genuine representation specified by its two diagonal actions and cross block. -/
def representation (c : BlockCocycle a b) : Representation (ZMod 2) SL (W × W) where
  toFun g := ((constituent a g).coprod (c.value g)).prod
    ((constituent b g).comp (LinearMap.snd (ZMod 2) W W))
  map_one' := by
    apply LinearMap.ext
    intro v
    change ((constituent a 1) v.1 + c.value 1 v.2, (constituent b 1) v.2) = v
    simp only [map_one, c.one, LinearMap.zero_apply, Module.End.one_apply, add_zero]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change (constituent a (g * h)) v.1 + c.value (g * h) v.2 =
        (constituent a g) ((constituent a h) v.1 + c.value h v.2) +
          c.value g ((constituent b h) v.2)
      simp only [map_mul, c.mul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.comp_apply, map_add, add_assoc]
    · exact LinearMap.congr_fun ((constituent b).map_mul g h) v.2

lemma representation_apply (c : BlockCocycle a b) (g : SL) (v : W × W) :
    c.representation g v = ((constituent a g) v.1 + c.value g v.2,
      (constituent b g) v.2) := rfl

lemma representation_faithful (c : BlockCocycle a b) : Function.Injective c.representation := by
  intro g h he
  apply constituent_faithful a
  apply LinearMap.ext
  intro v
  have hv := congrArg Prod.fst (LinearMap.congr_fun he (v, 0))
  simpa only [representation_apply, map_zero, add_zero] using hv

/-- The off-diagonal equation forced by the central polynomial on the whole module. -/
def IsCentral (c : BlockCocycle a b) : Prop :=
  (constituent a z).comp (c.value z) + (c.value z).comp (constituent b z) + c.value z = 0

lemma centralQuadratic_iff (c : BlockCocycle a b) :
    CentralQuadratic c.representation ↔ c.IsCentral := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have hv := congrArg Prod.fst (centralQuadratic_apply _ h (0, v))
    change (constituent a z) ((constituent a z) 0 + c.value z v) +
      c.value z ((constituent b z) v) + ((constituent a z) 0 + c.value z v) + 0 = 0 at hv
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      map_zero, zero_add, add_zero] using hv
  · intro h
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change (constituent a z) ((constituent a z) v.1 + c.value z v.2) +
        c.value z ((constituent b z) v.2) +
        ((constituent a z) v.1 + c.value z v.2) + v.1 = 0
      have ha := centralQuadratic_apply _ (constituent_centralQuadratic a) v.1
      have hc := LinearMap.congr_fun h v.2
      change (constituent a z) (c.value z v.2) +
        c.value z ((constituent b z) v.2) + c.value z v.2 = 0 at hc
      rw [map_add]
      calc
        _ = ((constituent a z) ((constituent a z) v.1) + (constituent a z) v.1 + v.1) +
          ((constituent a z) (c.value z v.2) +
            c.value z ((constituent b z) v.2) + c.value z v.2) := by abel
        _ = 0 := by rw [ha, hc, add_zero]
    · exact centralQuadratic_apply _ (constituent_centralQuadratic b) v.2

/-- The zero off-diagonal block, giving the split extension. -/
def zero (a b : Constituent) : BlockCocycle a b where
  value _ := 0
  one := rfl
  mul _ _ := by simp

lemma zero_representation (a b : Constituent) : (zero a b).representation = splitRepresentation a b := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change ((constituent a g) v.1 + 0, (constituent b g) v.2) =
    ((constituent a g) v.1, (constituent b g) v.2)
  rw [add_zero]

/-- A change of linear section in an extension, on its actual carrier. -/
def changeSection (f : W →ₗ[ZMod 2] W) : (W × W) ≃ₗ[ZMod 2] (W × W) where
  toFun v := (v.1 + f v.2, v.2)
  invFun v := (v.1 - f v.2, v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by
    apply Prod.ext
    · change (v.1 + w.1) + f (v.2 + w.2) = (v.1 + f v.2) + (w.1 + f w.2)
      rw [map_add]
      abel
    · rfl
  map_smul' r v := by
    apply Prod.ext
    · change r • v.1 + f (r • v.2) = r • (v.1 + f v.2)
      rw [map_smul, smul_add]
    · rfl

/-- A coboundary comparison gives an actual representation equivalence. -/
def equivOfCoboundary (c d : BlockCocycle a b) (f : W →ₗ[ZMod 2] W)
    (h : ∀ g, c.value g + f.comp (constituent b g) =
      (constituent a g).comp f + d.value g) : c.representation.Equiv d.representation := by
  refine .mk (changeSection f) ?_
  intro g
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · change ((constituent a g) v.1 + c.value g v.2) + f ((constituent b g) v.2) =
      (constituent a g) (v.1 + f v.2) + d.value g v.2
    have hv := LinearMap.congr_fun (h g) v.2
    change c.value g v.2 + f ((constituent b g) v.2) =
      (constituent a g) (f v.2) + d.value g v.2 at hv
    rw [map_add, add_assoc, hv, ← add_assoc]
  · rfl

end BlockCocycle
end Representation.SL3FourLocalCatalogue
