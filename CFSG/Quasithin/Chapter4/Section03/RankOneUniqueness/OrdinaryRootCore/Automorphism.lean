module
public import Theory.Representation.SL2OrthogonalCover.OuterSemilinear
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Geometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.OrthogonalCover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Full-cover automorphisms fixing the ordinary Sylow-fixed plane

An automorphism of the plane local group induces the literal SL₂ quotient
actor and a binary linear actor on its full orthogonal-cover radical. If it
fixes the intersection with the point radical, it fixes the plane with last
coordinate zero. Semilinearity then forces the field automorphism to be the
identity. Preserving the singular vectors (0,0,1) and (1,1,1) determines the
remaining column, giving an actual upper-unipotent actor. Its plane Levi lift
belongs to the point radical, as checked in the original matrix coordinates.

This supplies the centralizer calculation in Aschbacher--Smith 4.3.6 (**),
printed p.615, using the full cover rather than just its natural quotient.
-/

public section
open Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCoreMatrix
open Representation Representation.SL2OrthogonalCover
open Representation.OneCohomology.CentralCoverOriginalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A normalizing binary actor of the full orthogonal cover which fixes the
Sylow-fixed plane pointwise acts as an actual upper unipotent matrix. -/
theorem cover_actor_fixing_plane (hF : 2 < Nat.card F)
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u))
    (hfix : ∀ u : Space F, u 2 = 0 → E u = u) :
    ∃ t : F, ∀ u, E u = action (upper t) u := by
  obtain ⟨e, he, hover⟩ := intertwiner_descends a E hE
  obtain ⟨σ, hσ⟩ := normalizer_semilinear
    (specialLinearNatural 2 (k := F)) (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf) a e he
  have hsemi := intertwiner_semilinear_of_projection hF a e E hE hover σ hσ
  have hs (c : F) : σ c = c := by
    have hh := hsemi c ![1,0,0]
    rw [hfix _ (by simp), hfix _ (by simp)] at hh
    have hv := congrFun hh 0
    simpa using hv.symm
  have hlin (c : F) (u : Space F) : E (c • u) = c • E u := by rw [hsemi, hs]
  let x : Space F := E ![0,0,1]
  have hcoord (u : Space F) : E u = ![u 0 + u 2*x 0, u 1 + u 2*x 1, u 2*x 2] := by
    have hu : u = ![u 0,u 1,0] + u 2 • ![0,0,1] := by ext i; fin_cases i <;> simp
    rw [hu, map_add, hfix _ (by simp), hlin]
    ext i
    fin_cases i <;> simp [x]
  have hsing := FullFixed.normalizer_preserves_singular hF a e E he hE hover
  have hx : x 0 ^ 2 + x 1*x 2 = 0 := by
    have hh := (hsing ![0,0,1]).mpr (by simp [form_apply])
    simpa only [form_apply] using hh
  have hmix : (1+x 0)^2 + (1+x 1)*x 2 = 0 := by
    have hh := (hsing ![1,1,1]).mpr (by simp [form_apply, CharTwo.add_self_eq_zero])
    rw [hcoord] at hh
    simpa [form_apply] using hh
  have hx2 : x 2 = 1 := by
    have hh : (1+x 0)^2 + (1+x 1)*x 2 = 1+x 2+(x 0^2+x 1*x 2) := by
      ring_nf
      simp [CharTwo.two_eq_zero]
    rw [hh, hx, add_zero] at hmix
    exact (CharTwo.add_eq_zero.mp hmix).symm
  have hx0 : x 0 = root (x 1) := by
    apply CharTwo.sq_injective
    change x 0 ^ 2 = root (x 1) ^ 2
    rw [sq_root]
    simpa only [hx2, mul_one, CharTwo.add_eq_zero] using hx
  refine ⟨x 1, fun u => ?_⟩
  rw [hcoord, action_upper, hx2, hx0, mul_one]
  ext i
  fin_cases i <;> simp [mul_comm]

open Subgroup Theory.SpecificGroups.SymplecticFour
open Plane.OrthogonalCover

omit [Finite F] [Algebra (ZMod 2) F] in
theorem levi_upper_mem_point_radical (t : F) :
    (Plane.levi (upper t)).val ∈ (pointRadical (F := F)).map pointLocal.subtype := by
  refine ⟨pointRadicalElement 0 t 0, pointRadicalElement_mem _ _ _, ?_⟩
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, Plane.levi, Plane.leviSp,
      upper, CharTwo.neg_eq]

theorem fixed_plane_mem_point_radical (q : Plane.radical (F := F))
    (hq : (radicalLinearCoordinates (Additive.ofMul q)) 2 = 0) :
    q.val.val ∈ (pointRadical (F := F)).map pointLocal.subtype := by
  let B := (Plane.radicalEquiv q).toAdd
  have hB : B.val 1 1 = 0 := by
    have hh := congrArg (fun x : F => x^2) hq
    change (root (B.val 1 1))^2 = 0^2 at hh
    simpa only [sq_root, zero_pow (by decide : 2 ≠ 0)] using hh
  have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  refine ⟨pointRadicalElement (B.val 0 1) 0 (B.val 0 0), pointRadicalElement_mem _ _ _, ?_⟩
  have he : q.val = Plane.shear B := congrArg Subtype.val (Plane.radicalEquiv.symm_apply_apply q).symm
  change (pointRadicalElement _ _ _).val = q.val.val
  rw [he]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, Plane.shear, Plane.shearSp, hs, hB]

theorem plane_automorphism_fixing_point_radical {n : ℕ}
    (hcard : Nat.card F = 2^n) (hn : 1 < n)
    (α : MulAut (planeLocal (F := F)))
    (hfix : ∀ q : Plane.radical (F := F),
      q.val.val ∈ (pointRadical (F := F)).map pointLocal.subtype → α q.val = q.val) :
    ∃ t : F, ∀ q : Plane.radical (F := F),
      α q.val = Plane.levi (upper t) * q.val * (Plane.levi (upper t))⁻¹ := by
  have hrad : (Plane.radical (F := F)).map α.toMonoidHom = Plane.radical := by
    rw [← planeLocal_core_eq hcard hn]
    exact pCore_map_iso 2 α
  let r : MulAut (Plane.radical (F := F)) :=
    (α.subgroupMap Plane.radical).trans (MulEquiv.subgroupCongr hrad)
  have hr (q : Plane.radical (F := F)) : (r q).val = α q.val := rfl
  let R : Additive (Plane.radical (F := F)) ≃ₗ[ZMod 2] Additive (Plane.radical (F := F)) :=
    r.toAdditive.toLinearEquiv (fun c x => ZMod.map_smul r.toAdditive.toAddMonoidHom c x)
  let C : Additive (Plane.radical (F := F)) ≃ₗ[ZMod 2] Space F := radicalLinearCoordinates
  let E : Space F ≃ₗ[ZMod 2] Space F := C.symm.trans (R.trans C)
  have hEcoord (q : Plane.radical (F := F)) :
      E (C (Additive.ofMul q)) = C (Additive.ofMul (r q)) := by
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hEcoorda (q : Additive (Plane.radical (F := F))) :
      E (C q) = C (Additive.ofMul (r q.toMul)) := by
    simpa only [ofMul_toMul] using hEcoord q.toMul
  let e := planeLocalCoreQuotientEquiv hcard hn
  let aq := (pCore 2 (planeLocal (F := F))).quotientAut α
  let a : MulAut (SL F) := e.symm.trans (aq.trans e)
  have ha (g : planeLocal (F := F)) : a (Plane.quotientMap g) = Plane.quotientMap (α g) := by
    have heq : e.symm (Plane.quotientMap g) = QuotientGroup.mk g :=
      e.symm_apply_eq.mpr (planeLocalCoreQuotientEquiv_mk hcard hn g).symm
    change e (aq (e.symm (Plane.quotientMap g))) = _
    rw [heq]
    exact (congrArg e (quotientAut_apply_mk _ α g)).trans
      (planeLocalCoreQuotientEquiv_mk hcard hn (α g))
  have hc (g : planeLocal (F := F)) (q : Plane.radical (F := F)) :
      r (Plane.conjugate g q) = Plane.conjugate (α g) (r q) := by
    apply Subtype.ext
    change α (g * q.val * g⁻¹) = α g * α q.val * (α g)⁻¹
    simp only [map_mul, map_inv]
  have hE (g : SL F) (u : Space F) : E (action g u) = action (a g) (E u) := by
    obtain ⟨g, rfl⟩ := Plane.quotientMap_surjective g
    obtain ⟨q, rfl⟩ := C.toEquiv.surjective u
    change E (action (Plane.quotientMap g) (C q)) = action (a (Plane.quotientMap g)) (E (C q))
    have hh := radicalLinearCoordinates_conjugate g q.toMul
    change C (Additive.ofMul (Plane.conjugate g q.toMul)) = action (Plane.quotientMap g) (C q) at hh
    rw [← hh, hEcoord, hc, ha, hEcoorda]
    exact radicalLinearCoordinates_conjugate (α g) (r q.toMul)
  have hf (u : Space F) (hu : u 2 = 0) : E u = u := by
    obtain ⟨q, rfl⟩ := C.toEquiv.surjective u
    change E (C q) = C q
    change C q 2 = 0 at hu
    rw [hEcoorda]
    apply congrArg C
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hfix q.toMul (fixed_plane_mem_point_radical q.toMul hu)
  have hF : 2 < Nat.card F := by
    rw [hcard]
    calc
      2 = 2^1 := rfl
      _ < 2^n := Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨t, ht⟩ := cover_actor_fixing_plane hF a E hE hf
  refine ⟨t, fun q => ?_⟩
  have hh := radicalLinearCoordinates_conjugate (Plane.levi (upper t)) q
  change C (Additive.ofMul (Plane.conjugate (Plane.levi (upper t)) q)) =
    action (Plane.quotientMap (Plane.levi (upper t))) (C (Additive.ofMul q)) at hh
  rw [Plane.quotientMap_levi] at hh
  have hh' := C.injective ((hEcoord q).symm.trans ((ht (C (Additive.ofMul q))).trans hh.symm))
  exact congrArg (fun q : Additive (Plane.radical (F := F)) => q.toMul.val) hh'

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCoreMatrix
