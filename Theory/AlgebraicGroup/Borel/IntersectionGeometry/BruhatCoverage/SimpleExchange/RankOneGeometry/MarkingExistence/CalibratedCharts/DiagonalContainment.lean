module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.Instance.PSL
public import Theory.AlgebraicGroup.Morphism.SL2RootRegularity
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLDiagonalTorus
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Product

/-!
Compatible opposite root curves and their diagonal containment.

A point homomorphism from SL₂ that realizes the two literal root curves
already has its diagonal in the maximal torus. Inverse conjugation by a torus
point scales the upper and lower parameters reciprocally. Transvection
induction identifies this action with the matrix scaling automorphism, which
fixes the diagonal. Regularity of the two curves makes the homomorphism
algebraic. Multiplying its diagonal cocharacter with the ambient torus then
gives a larger torus, so maximality proves the required containment.

The constructors below discharge the diagonal clause of `SL2RootMarking`.
They do not construct compatible curves. The existence of those curves from
reductivity is still required in the final source-theorem assembly. The family-level
application in `CalibratedCharts` supplies exactly the local-marking input to
`nonempty_of_local_markings_borel_fixed_roots` in `MarkingExistence`.

Sources: GLS3, §§1.9 and 1.12, especially the inverse-conjugation convention
of 1.9.2 and the opposite-root words of 1.12.1; Borel, §§13.13--13.14 and
13.18. The construction works in every characteristic and does not identify
the fundamental roots of an arbitrary positive system with `D.simple`.
-/

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup


namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts
variable {k X : Type*} [Field k] [Group X]

private def scale (a : k) (ha : a ≠ 0) : SL(2, k) →* SL(2, k) where
  toFun x := ⟨!![x.val 0 0, a * x.val 0 1; a⁻¹ * x.val 1 0, x.val 1 1], by
    have hx := x.property
    rw [det_fin_two] at hx ⊢
    simpa [ha, mul_assoc, mul_left_comm, mul_comm] using hx⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Subtype.ext
    change !![(x*y).val 0 0, a*(x*y).val 0 1; a⁻¹*(x*y).val 1 0, (x*y).val 1 1] =
      !![x.val 0 0, a*x.val 0 1; a⁻¹*x.val 1 0, x.val 1 1] *
        !![y.val 0 0, a*y.val 0 1; a⁻¹*y.val 1 0, y.val 1 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two] <;>
      field_simp

private theorem scale_upper (a : k) (ha : a ≠ 0) (b : k) :
    scale a ha (BruhatGeneration.SL2.upper b) = BruhatGeneration.SL2.upper (a*b) := by
  apply Subtype.ext
  change !![_, _; _, _] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BruhatGeneration.SL2.upper, SpecialLinearGroup.transvection_coe]

private theorem scale_lower (a : k) (ha : a ≠ 0) (b : k) :
    scale a ha (BruhatGeneration.SL2.lower b) = BruhatGeneration.SL2.lower (a⁻¹*b) := by
  apply Subtype.ext
  change !![_, _; _, _] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BruhatGeneration.SL2.lower, SpecialLinearGroup.transvection_coe]

private theorem scale_diag (a : k) (ha : a ≠ 0) (b : k) (hb : b ≠ 0) :
    scale a ha (SpecialLinearGroup.diag2 b hb) = SpecialLinearGroup.diag2 b hb := by
  apply Subtype.ext
  change !![_, _; _, _] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.diag2_coe']


private theorem hom_ext (f g : SL(2, k) →* X)
    (hu : ∀ b, f (BruhatGeneration.SL2.upper b) = g (BruhatGeneration.SL2.upper b))
    (hl : ∀ b, f (BruhatGeneration.SL2.lower b) = g (BruhatGeneration.SL2.lower b)) : f = g := by
  ext A
  refine Matrix.SL2.transvection_induction (fun A => f A = g A) ?_ ?_ A
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu c
    · exact hl c
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul, map_mul, hA, hB]

/-- Reciprocal scaling of the two root curves fixes every diagonal image.
No algebraic closure or characteristic restriction is used in this matrix argument. -/
public theorem diagonal_commute_of_root_scaling (f : SL(2, k) →* X) (z : X) (a : k) (ha : a ≠ 0)
    (hu : ∀ b, z⁻¹ * f (BruhatGeneration.SL2.upper b) * z =
      f (BruhatGeneration.SL2.upper (a*b)))
    (hl : ∀ b, z⁻¹ * f (BruhatGeneration.SL2.lower b) * z =
      f (BruhatGeneration.SL2.lower (a⁻¹*b))) (b : k) (hb : b ≠ 0) :
    Commute z (f (SpecialLinearGroup.diag2 b hb)) := by
  have heq : (MulAut.conj z⁻¹).toMonoidHom.comp f = f.comp (scale a ha) := by
    apply hom_ext
    · intro c
      change z⁻¹ * f (BruhatGeneration.SL2.upper c) * (z⁻¹)⁻¹ = _
      rw [inv_inv, hu]
      change _ = f (scale a ha (BruhatGeneration.SL2.upper c))
      rw [scale_upper]
    · intro c
      change z⁻¹ * f (BruhatGeneration.SL2.lower c) * (z⁻¹)⁻¹ = _
      rw [inv_inv, hl]
      change _ = f (scale a ha (BruhatGeneration.SL2.lower c))
      rw [scale_lower]
  have hd := DFunLike.congr_fun heq (SpecialLinearGroup.diag2 b hb)
  change z⁻¹ * f (SpecialLinearGroup.diag2 b hb) * (z⁻¹)⁻¹ =
    f (scale a ha (SpecialLinearGroup.diag2 b hb)) at hd
  rw [inv_inv, scale_diag] at hd
  change z * f (SpecialLinearGroup.diag2 b hb) = f (SpecialLinearGroup.diag2 b hb) * z
  calc
    _ = z * (z⁻¹ * f (SpecialLinearGroup.diag2 b hb) * z) := congrArg (z * ·) hd.symm
    _ = _ := by group

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- A cocharacter commuting with a maximal torus has image in that torus.
The image of the product morphism is a torus containing the original one. -/
public theorem cocharacter_mem_maximalTorus_of_commutes (hT : IsMaximalTorus T) (c : Morphism (KMult k) G)
    (hc : ∀ t s, Commute (T.includePoint t) (c.onPoints s))
    (s : Variety.Point (KMult k)) : c.onPoints s ∈ T.toSubgroup := by
  obtain ⟨n, ⟨e⟩⟩ := hT.1
  let Z := Variety.prod (dVariety k n) (KMult k)
  let l : Morphism Z G := T.inclusion.comp (e.hom.comp (Morphism.fst _ _))
  let r : Morphism Z G := c.comp (Morphism.snd _ _)
  have hcomm (x y : Variety.Point Z) : Commute (l.onPoints y) (r.onPoints x) :=
    hc _ _
  let m : Morphism Z G :=
    { toVariety := (mulMorphism G).comp (Morphism.prod l r).toVariety
      map_one := by change l.onPoints 1 * r.onPoints 1 = 1; simp
      map_mul := by
        intro x y
        change l.onPoints (x*y) * r.onPoints (x*y) =
          (l.onPoints x * r.onPoints x) * (l.onPoints y * r.onPoints y)
        simp only [map_mul]
        calc
          (l.onPoints x * l.onPoints y) * (r.onPoints x * r.onPoints y) =
              l.onPoints x * (l.onPoints y * r.onPoints x) * r.onPoints y := by group
          _ = l.onPoints x * (r.onPoints x * l.onPoints y) * r.onPoints y := by
            rw [(hcomm x y).eq]
          _ = _ := by group }
  have hTle : T ≤ m.imageClosedSubgroup := by
    intro t ht
    let t₀ := T.pointEquiv.symm ⟨t, ht⟩
    refine ⟨(Variety.prodPointEquiv _ _).symm (e.inv.onPoints t₀, 1), ?_⟩
    change T.inclusion.onPoints (e.hom.onPoints (e.inv.onPoints t₀)) * c.onPoints 1 = t
    rw [e.inv_hom_id, map_one, mul_one]
    exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  have hm : m.imageClosedSubgroup = T := hT.2 _
    (morphism_image_isTorus m ⟨n+1, ⟨dVarietySuccProdIso n⟩⟩) hTle
  rw [← hm]
  refine ⟨(Variety.prodPointEquiv _ _).symm (1, s), ?_⟩
  change T.inclusion.onPoints (e.hom.onPoints 1) * c.onPoints s = c.onPoints s
  rw [map_one, map_one, one_mul]


private theorem diagonal_matrix (t : Variety.Point (KMult k)) :
    slPointMulEquiv 2 ((typeASLDiagonalMorphism (k := k) 1).onPoints t) =
      SpecialLinearGroup.diag2 (dPointEquiv 1 t 0 : k) (Units.ne_zero _) := by
  rw [slPointMulEquiv_apply]
  apply Subtype.ext
  change slPointMatrix 2 (typeASLDiagonalPoint 1 t) = _
  rw [typeASLDiagonalPoint_matrix]
  have h0 : typeASLDiagonalEntries 1 t 0 = dPointEquiv 1 t 0 :=
    typeASLDiagonalEntries_castSucc 1 t 0
  have h1 : typeASLDiagonalEntries 1 t 1 = (dPointEquiv 1 t 0)⁻¹ := by
    simpa using typeASLDiagonalEntries_last 1 t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeASLDiagonalMatrix, h0, h1, SpecialLinearGroup.diag2_coe']

variable {D : RootGroupData G T} {α : D.Root}
variable (plus : OneParameterParametrization (D.rootSubgroup α).carrierVariety)
variable (minus : OneParameterParametrization (D.rootSubgroup (D.neg α)).carrierVariety)
variable (f : SL(2, k) →* Variety.Point G)
variable (hu : ∀ t, f (BruhatGeneration.SL2.upper t) =
  (D.rootSubgroup α).includePoint (plus.value t))
variable (hl : ∀ t, f (BruhatGeneration.SL2.lower t) =
  (D.rootSubgroup (D.neg α)).includePoint (minus.value t))

include plus minus hu hl in
private theorem exists_algebraicHom :
    ∃ F : Morphism (slVariety k 2) G,
      F.onPoints = f.comp (slPointMulEquiv (k := k) 2).toMonoidHom := by
  apply exists_sl2Morphism_of_regular_rootCurves _
    ((D.rootSubgroup α).inclusion.comp plus.hom)
    ((D.rootSubgroup (D.neg α)).inclusion.comp minus.hom)
  · intro s
    obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
    change f (slPointMulEquiv 2 _) = _
    rw [slPointMulEquiv_apply]
    exact hu t
  · intro s
    obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
    change f (slPointMulEquiv 2 _) = _
    rw [slPointMulEquiv_apply]
    exact hl t

omit [IsAlgClosed k] in
include plus minus hu hl in
/-- The realized inverse-conjugation weights force every diagonal image
to commute with every point of the torus. -/
public theorem diagonal_commute (hD : D.IsRealization)
    (s : Variety.Point T.carrierVariety) (t : k) (ht : t ≠ 0) :
    Commute (T.includePoint s) (f (SpecialLinearGroup.diag2 t ht)) := by
  let a := (D.rootWeight α).pointCharacter s
  have ha : a ≠ 0 := Units.ne_zero (dPointEquiv 1 ((D.rootWeight α).onPoints s) 0)
  have hneg : (D.rootWeight (D.neg α)).pointCharacter s = a⁻¹ := by
    rw [hD.2.2.2.1 α]
    change (dPointEquiv 1 (((D.rootWeight α).onPoints s)⁻¹) 0 : k) = _
    have hmul := dPointEquiv_mul 1 ((D.rootWeight α).onPoints s)
      (((D.rootWeight α).onPoints s)⁻¹)
    rw [mul_inv_cancel, dPointEquiv_one] at hmul
    have hzero := congrArg (fun z : Fin 1 → kˣ => (z 0 : k)) hmul
    change 1 = a * (dPointEquiv 1 (((D.rootWeight α).onPoints s)⁻¹) 0 : k) at hzero
    apply mul_left_cancel₀ ha
    rw [← hzero, mul_inv_cancel₀ ha]
  apply diagonal_commute_of_root_scaling f (T.includePoint s) a ha
  · intro b
    simp_rw [hu]
    exact (hD.2.2.1 α).2 plus b s
  · intro b
    simp_rw [hl]
    rw [← hneg]
    exact (hD.2.2.1 (D.neg α)).2 minus b s

include plus minus hu hl in
/-- Two compatible regular root curves force diagonal containment.
Only realization and torus maximality are needed, without reductivity or a Borel. -/
public theorem diagonal_mem (hD : D.IsRealization) (hT : IsMaximalTorus T)
    (t : k) (ht : t ≠ 0) : f (SpecialLinearGroup.diag2 t ht) ∈ T.toSubgroup := by
  obtain ⟨F, hF⟩ := exists_algebraicHom plus minus f hu hl
  let c : Morphism (KMult k) G := F.comp (typeASLDiagonalMorphism 1)
  have hc (s : Variety.Point (KMult k)) :
      c.onPoints s = f (SpecialLinearGroup.diag2 (dPointEquiv 1 s 0 : k) (Units.ne_zero _)) := by
    change F.onPoints _ = _
    rw [hF]
    change f (slPointMulEquiv 2 _) = _
    exact congrArg f (diagonal_matrix s)
  have hcomm (s : Variety.Point T.carrierVariety) (a : Variety.Point (KMult k)) :
      Commute (T.includePoint s) (c.onPoints a) := by
    rw [hc]
    exact diagonal_commute plus minus f hu hl hD _ _ _
  have hmem := cocharacter_mem_maximalTorus_of_commutes hT c hcomm
    ((dPointEquiv 1).symm (fun _ => Units.mk0 t ht))
  rw [hc] at hmem
  simpa only [Equiv.apply_symm_apply, Units.val_mk0] using hmem

/-- Complete a pair of compatible point-level root curves to an SL₂ marking
by proving its diagonal-containment clause. -/
public noncomputable def marking_of_root_curves (hD : D.IsRealization) (hT : IsMaximalTorus T) :
    SL2RootMarking D α where
  plus := plus
  minus := minus
  hom := f
  upper_eq := hu
  lower_eq := hl
  diagonal_mem := diagonal_mem plus minus f hu hl hD hT


/-- Convert literal algebraic upper/lower curve identities into an SL₂
marking, including the diagonal condition derived from maximality. -/
public noncomputable def marking_of_algebraic_root_curves
    (hD : D.IsRealization) (hT : IsMaximalTorus T)
    (F : Morphism (slVariety k 2) G)
    (hupper : F.comp standardSL2UpperMorphism = (D.rootSubgroup α).inclusion.comp plus.hom)
    (hlower : F.comp standardSL2LowerMorphism =
      (D.rootSubgroup (D.neg α)).inclusion.comp minus.hom) : SL2RootMarking D α := by
  let φ := F.onPoints.comp (slPointMulEquiv (k := k) 2).symm.toMonoidHom
  apply marking_of_root_curves plus minus φ (hD := hD) (hT := hT)
  · intro t
    have he : slPointMulEquiv 2 (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
        BruhatGeneration.SL2.upper t := by
      rw [slPointMulEquiv_apply]
      rfl
    change F.onPoints ((slPointMulEquiv 2).symm (BruhatGeneration.SL2.upper t)) = _
    rw [← he, MulEquiv.symm_apply_apply]
    exact congrArg (fun m : Morphism (KPlus k) G => m.onPoints (kPlusPoint t)) hupper
  · intro t
    have he : slPointMulEquiv 2 (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
        BruhatGeneration.SL2.lower t := by
      rw [slPointMulEquiv_apply]
      rfl
    change F.onPoints ((slPointMulEquiv 2).symm (BruhatGeneration.SL2.lower t)) = _
    rw [← he, MulEquiv.symm_apply_apply]
    exact congrArg (fun m : Morphism (KPlus k) G => m.onPoints (kPlusPoint t)) hlower

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts
