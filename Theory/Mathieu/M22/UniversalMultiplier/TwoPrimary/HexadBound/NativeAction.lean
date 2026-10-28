module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadBound.Reduction
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The marked action on the lifted hexad radical

The full preimage of the native E₁₆ maps onto the literal natural four-space.
The specified lifted A₆ section acts by conjugation, and the native coordinate
formula identifies that action over the original projection. Its kernel is
precisely the original central kernel restricted to the radical.

The section is injective and complementary to the full radical. Multiplication
therefore gives a marked semidirect-product equivalence, with no perfectness or
prescribed order assumption on the covering group. These are the shared native
inputs of the pairing and abelian-module branches of the relative bound.

Source: Aschbacher–Smith I.1.3(4), printed p.407, and I.2.2(6), printed p.412.
-/

@[expose] public section

open Subgroup
namespace Sporadic.Mathieu.M22UniversalMultiplier.HexadBound
noncomputable section
universe u
variable {D : Type u} [Group D]

/-- The native quotient to the naturally marked four-dimensional module. -/
def naturalProjection (q : D →* m22HexadStabilizer) :
    radical q →* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  (m22HexadNaturalCoordinates m22Hexad123_mem).toMonoidHom.comp
    (q.subgroupComap (m22SetAction m22Hexad123).ker)

theorem naturalProjection_surjective (q : D →* m22HexadStabilizer)
    (hq : Function.Surjective q) : Function.Surjective (naturalProjection q) :=
  (m22HexadNaturalCoordinates m22Hexad123_mem).surjective.comp
    (q.subgroupComap_surjective_of_surjective _ hq)

theorem naturalProjection_ker (q : D →* m22HexadStabilizer) :
    (naturalProjection q).ker = q.ker.subgroupOf (radical q) := by
  ext x
  change m22HexadNaturalCoordinates m22Hexad123_mem
    (q.subgroupComap (m22SetAction m22Hexad123).ker x) = 1 ↔ q x = 1
  exact (map_eq_one_iff _ (m22HexadNaturalCoordinates m22Hexad123_mem).injective).trans
    Subtype.ext_iff

/-- Conjugation by the specified lifted A₆ section on the full radical. -/
def actor (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D) :
    alternatingGroup (Fin 6) →* MulAut (radical q) :=
  MulAut.conjNormal.comp s

/-- The original section marking gives exactly the natural module action. -/
theorem naturalProjection_equivariant (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D)
    (hs : q.comp s = m22HexadSection m22Hexad123_mem)
    (a : alternatingGroup (Fin 6)) (r : radical q) :
    (naturalProjection q (actor q s a r)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) a.val
        (naturalProjection q r).toAdd := by
  let t := q.subgroupComap (m22SetAction m22Hexad123).ker
  have he : t (actor q s a r) = MulAut.conjNormal
      (m22HexadSection m22Hexad123_mem a) (t r) := by
    apply Subtype.ext
    change q (s a * r * (s a)⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rw [show q (s a) = m22HexadSection m22Hexad123_mem a from DFunLike.congr_fun hs a]
    rfl
  change (m22HexadNaturalCoordinates m22Hexad123_mem (t (actor q s a r))).toAdd = _
  rw [he]
  exact m22HexadNaturalCoordinates_section m22Hexad123_mem a (t r)

theorem actor_fixes_kernel (q : D →* m22HexadStabilizer)
    (hc : q.ker ≤ center D) (s : alternatingGroup (Fin 6) →* D)
    (r : radical q) (hr : r ∈ (naturalProjection q).ker) (a : alternatingGroup (Fin 6)) :
    actor q s a r = r := by
  rw [naturalProjection_ker] at hr
  apply Subtype.ext
  change s a * (r : D) * (s a)⁻¹ = (r : D)
  have he : s a * (r : D) = (r : D) * s a := mem_center_iff.mp (hc hr) (s a)
  rw [he, mul_inv_cancel_right]

theorem section_injective (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D)
    (hs : q.comp s = m22HexadSection m22Hexad123_mem) : Function.Injective s := by
  intro a b hab
  apply m22HexadSection_injective m22Hexad123_mem
  rw [← hs]
  exact congrArg q hab

/-- The lifted section is complementary to the full preimage of E₁₆. -/
theorem section_isComplement (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D)
    (hs : q.comp s = m22HexadSection m22Hexad123_mem) :
    (radical q).IsComplement' s.range := by
  let Q : D →* alternatingGroup (Fin 6) := (m22HexadSixMap m22Hexad123_mem).comp q
  have hQs (a : alternatingGroup (Fin 6)) :
      Q (s a) = m22HexadMarking m22Hexad123_mem a := by
    change m22HexadSixMap m22Hexad123_mem (q (s a)) = _
    exact (congrArg (m22HexadSixMap m22Hexad123_mem) (DFunLike.congr_fun hs a)).trans
      (m22HexadSixMap_section m22Hexad123_mem a)
  have hQker : Q.ker = radical q := by
    exact congrArg (fun H => H.comap q) (m22HexadSixMap_ker m22Hexad123_mem)
  have hd : Disjoint (radical q) s.range := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hx, a, rfl⟩
    have he : Q (s a) = 1 := by
      change s a ∈ Q.ker
      rwa [hQker]
    rw [hQs, map_eq_one_iff _ (m22HexadMarking m22Hexad123_mem).injective] at he
    rw [he, map_one]
    exact one_mem _
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro x
  let a := (m22HexadMarking m22Hexad123_mem).symm (Q x)
  have hr : x * (s a)⁻¹ ∈ radical q := by
    rw [← hQker]
    change Q (x * (s a)⁻¹) = 1
    rw [map_mul, map_inv, hQs, MulEquiv.apply_symm_apply, mul_inv_cancel]
  exact ⟨(⟨x * (s a)⁻¹, hr⟩, ⟨s a, a, rfl⟩), inv_mul_cancel_right x (s a)⟩

/-- Multiplication of the full radical and the lifted A₆ section. -/
def splitHom (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D) :
    radical q ⋊[actor q s] alternatingGroup (Fin 6) →* D :=
  SemidirectProduct.lift (radical q).subtype s (fun _ => rfl)

/-- The section hypothesis constructs an actual split extension of D. -/
theorem splitHom_bijective (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D)
    (hs : q.comp s = m22HexadSection m22Hexad123_mem) :
    Function.Bijective (splitHom q s) := by
  have hc := section_isComplement q s hs
  constructor
  · intro x y h
    have he : (x.left, (⟨s x.right, x.right, rfl⟩ : s.range)) =
        (y.left, (⟨s y.right, y.right, rfl⟩ : s.range)) := hc.1 h
    apply SemidirectProduct.ext (congrArg Prod.fst he)
    exact section_injective q s hs
      (congrArg (fun z : radical q × s.range => (z.2 : D)) he)
  · intro d
    obtain ⟨⟨r, a⟩, he⟩ := hc.2 d
    obtain ⟨b, hb⟩ := a.property
    refine ⟨⟨r, b⟩, ?_⟩
    change (r : D) * s b = d
    rw [hb]
    exact he

/-- Marked semidirect coordinates for the original central extension. -/
def splitEquiv (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D)
    (hs : q.comp s = m22HexadSection m22Hexad123_mem) :
    radical q ⋊[actor q s] alternatingGroup (Fin 6) ≃* D :=
  MulEquiv.ofBijective (splitHom q s) (splitHom_bijective q s hs)

@[simp] theorem splitEquiv_apply (q : D →* m22HexadStabilizer)
    (s : alternatingGroup (Fin 6) →* D)
    (hs : q.comp s = m22HexadSection m22Hexad123_mem)
    (x : radical q ⋊[actor q s] alternatingGroup (Fin 6)) :
    splitEquiv q s hs x = (x.left : D) * s x.right := rfl

end
end Sporadic.Mathieu.M22UniversalMultiplier.HexadBound
