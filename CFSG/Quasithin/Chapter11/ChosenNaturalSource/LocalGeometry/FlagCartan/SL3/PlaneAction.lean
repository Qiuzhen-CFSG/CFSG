module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Model
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Flag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Uniqueness
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.Reductions
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.SpecialLinearThreeTransitivity
/-!
# The original SL₃ local plane action and its geometry

Conjugate the supplied component quotient by the one alignment defining the
original Sylow flag. The two normalizer residuals then map onto the literal
point and plane locals. The upper-left block gives the plane action onto SL₂,
with kernel exactly the local two-core. The original quotient coordinates,
after the proved vanishing of C_V(L), give the binary linear intertwiner.

Nonzero-vector transitivity proves Irr⁺ and discharges the action premises of
11.1.3. A lifted upper-unipotent Sylow fixes exactly the original point; Sylow
conjugacy identifies its full fixed-subgroup family and supplies the orbit
reduction in 11.2.4. Field-line transitivity is transported through the same
coordinates. Finally, the two model locals generate SL₃, and perfectness of L
removes the solvable kernel supplement, proving generation by its actual locals.
The genuine relative-component and relative-normality premises remain explicit
in their respective source applications.

Source: Aschbacher--Smith, opening §11.1, 11.1.3 and 11.2.4,
printed pp.760--761,765,769--770 of `refs/quasithin.pdf`.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup Representation
open Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {F : Type*} [Field F] [Finite F]

def parabolic (i : Fin 2) : Subgroup SL(3,F) :=
  ![pointParabolicSL F, lineParabolicSL F] i

def localGroup (i : Fin 2) : Subgroup SL(3,F) :=
  ![pointLocalSL F, lineLocalSL F] i

private theorem parabolic_preserves (i : Fin 2) {a : SL(3,F)} (ha : a ∈ parabolic i)
    {v : Fin 3 → F} (hv : v ∈ Model.flag i.castSucc) :
    specialLinearNatural 3 a v ∈ Model.flag i.castSucc := by
  fin_cases i
  · have ha := (mem_pointParabolicSL_iff F a).mp ha
    have hv : v 1 = 0 ∧ v 2 = 0 := hv
    change (a.val.mulVec v) 1 = 0 ∧ (a.val.mulVec v) 2 = 0
    simp [mulVec,dotProduct,Fin.sum_univ_three,ha.1,ha.2,hv.1,hv.2]
  · have ha := (mem_lineParabolicSL_iff F a).mp ha
    have hv : v 2 = 0 := hv
    change (a.val.mulVec v) 2 = 0
    simp [mulVec,dotProduct,Fin.sum_univ_three,ha.1,ha.2,hv]

theorem mem_parabolic_iff (i : Fin 2) (a : SL(3,F)) :
    a ∈ parabolic i ↔ ∀ v, specialLinearNatural 3 a v ∈ Model.flag i.castSucc ↔
      v ∈ Model.flag i.castSucc := by
  constructor
  · intro ha v
    constructor
    · intro hv
      simpa [map_inv] using parabolic_preserves i ((parabolic i).inv_mem ha) hv
    · exact parabolic_preserves i ha
  · intro h
    fin_cases i
    · have he := (h ![1,0,0]).mpr (by change (0:F) = 0 ∧ (0:F) = 0; simp)
      apply (mem_pointParabolicSL_iff F a).mpr
      change (a.val.mulVec ![1,0,0]) 1 = 0 ∧ (a.val.mulVec ![1,0,0]) 2 = 0 at he
      simpa [mulVec,dotProduct,Fin.sum_univ_three] using he
    · have he0 := (h ![1,0,0]).mpr (by rfl)
      have he1 := (h ![0,1,0]).mpr (by rfl)
      apply (mem_lineParabolicSL_iff F a).mpr
      change (a.val.mulVec ![1,0,0]) 2 = 0 at he0
      change (a.val.mulVec ![0,1,0]) 2 = 0 at he1
      simpa [mulVec,dotProduct,Fin.sum_univ_three] using And.intro he0 he1

omit [Finite F] in
theorem mem_flagFor_iff (a : SL(3,F)) (i : Fin 3) (v : Fin 3 → F) :
    v ∈ Model.flagFor a i ↔ specialLinearNatural 3 a⁻¹ v ∈ Model.flag i := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa [map_inv] using hw
  · intro hv
    exact ⟨specialLinearNatural 3 a⁻¹ v,hv,by simp [map_inv]⟩

theorem aligned_stabilizer (a g : SL(3,F)) (i : Fin 2) :
    (∀ v, specialLinearNatural 3 g v ∈ Model.flagFor a i.castSucc ↔
      v ∈ Model.flagFor a i.castSucc) ↔
    MulAut.conj a⁻¹ g ∈ parabolic i := by
  rw [mem_parabolic_iff]
  constructor
  · intro h w
    specialize h (specialLinearNatural 3 a w)
    simpa [mem_flagFor_iff, MulAut.conj_apply, map_mul, map_inv] using h
  · intro h v
    specialize h (specialLinearNatural 3 a⁻¹ v)
    simpa [mem_flagFor_iff, MulAut.conj_apply, map_mul, map_inv] using h

theorem parabolic_residual (hcard : 4 ≤ Nat.card F) (i : Fin 2) :
    (solvableResidual (parabolic (F := F) i)).map (parabolic i).subtype = localGroup i := by
  fin_cases i
  · exact pointParabolicSL_residual F hcard
  · exact lineParabolicSL_residual F hcard

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original component quotient, in the common basis of its Sylow flag. -/
def alignedQuotient : L →* SL(3,S.field.Carrier) :=
  (MulAut.conj (alignment D S m)⁻¹).toMonoidHom.comp (coordinates D S m).quotientMap

theorem alignedQuotient_surjective : Function.Surjective (alignedQuotient D S m) :=
  (MulAut.conj (alignment D S m)⁻¹).surjective.comp (coordinates D S m).quotientMap_surjective

def parabolicEquiv (i : Fin 2) :
    (coordinates D S m).modelStabilizer ((flag D S m).space i.castSucc) ≃*
      parabolic (F := S.field.Carrier) i where
  toFun g := ⟨MulAut.conj (alignment D S m)⁻¹ g.val,
    (aligned_stabilizer _ _ i).mp g.property⟩
  invFun g := ⟨(MulAut.conj (alignment D S m)⁻¹).symm g,
    (aligned_stabilizer _ _ i).mpr (by
      simpa only [MulEquiv.apply_symm_apply] using g.property)⟩
  left_inv g := Subtype.ext ((MulAut.conj (alignment D S m)⁻¹).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((MulAut.conj (alignment D S m)⁻¹).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (map_mul (MulAut.conj (alignment D S m)⁻¹) g.val h.val)

theorem field_card : 4 ≤ Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  change (2 : ℕ)^2 ≤ 2 ^ S.field.degree
  exact Nat.pow_le_pow_right (by decide) (by have := S.nonbinary; omega)

def residualEquiv (i : Fin 2) :
    solvableResidual ((coordinates D S m).modelStabilizer ((flag D S m).space i.castSucc)) ≃*
      localGroup (F := S.field.Carrier) i :=
  (parabolicEquiv D S m i).solvableResidualEquiv.trans
    (((solvableResidual (parabolic (F := S.field.Carrier) i)).equivMapOfInjective
      (parabolic i).subtype (parabolic i).subtype_injective).trans
        (MulEquiv.subgroupCongr (parabolic_residual (field_card D S) i)))

/-- Each original local residual maps onto the appropriate literal SL₃ local. -/
def localProjection (i : Fin 2) : (flag D S m).Li i →* localGroup (F := S.field.Carrier) i :=
  (residualEquiv D S m i).toMonoidHom.comp
    ((coordinates D S m).residualProjection ((flag D S m).space i.castSucc))

theorem localProjection_surjective (i : Fin 2) :
    Function.Surjective (localProjection D S m i) :=
  (residualEquiv D S m i).surjective.comp
    ((coordinates D S m).residualProjection_surjective ((flag D S m).space i.castSucc))

/-- This projection retains the original quotient and the single flag alignment. -/
theorem localProjection_coe (i : Fin 2) (l : (flag D S m).Li i) :
    (localProjection D S m i l : SL(3,S.field.Carrier)) =
      alignedQuotient D S m ⟨l,(localResidual_le _ l.property).1⟩ := by
  change (((parabolicEquiv D S m i).solvableResidualEquiv
    ((coordinates D S m).residualProjection ((flag D S m).space i.castSucc) l)).val :
      SL(3,S.field.Carrier)) = _
  rw [MulEquiv.solvableResidualEquiv_apply]
  change MulAut.conj (alignment D S m)⁻¹
    (((coordinates D S m).residualProjection ((flag D S m).space i.castSucc) l).val.val :
      SL(3,S.field.Carrier)) = _
  rw [Coordinates.residualProjection_coe]
  rfl

theorem localProjection_ker_isTwoGroup (i : Fin 2) :
    IsPGroup 2 (localProjection D S m i).ker := by
  have he : (localProjection D S m i).ker =
      ((coordinates D S m).residualProjection ((flag D S m).space i.castSucc)).ker := by
    ext x
    exact map_eq_one_iff _ (residualEquiv D S m i).injective
  rw [he]
  exact (coordinates D S m).residualProjection_ker_isTwoGroup _

/-- The upper-left block is the action on the actual second flag member. -/
def planeProjection : (flag D S m).Li 1 →* SL(2,S.field.Carrier) :=
  (SemidirectProduct.rightHom : Matrix.SL2.Affine S.field.Carrier →* SL(2,S.field.Carrier)).comp
    ((lineLocalAffineEquiv S.field.Carrier).toMonoidHom.comp (localProjection D S m 1))

theorem planeProjection_surjective : Function.Surjective (planeProjection D S m) := by
  intro a
  obtain ⟨l,hl⟩ := localProjection_surjective D S m 1
    ((lineLocalAffineEquiv S.field.Carrier).symm (SemidirectProduct.inr a))
  refine ⟨l,?_⟩
  change (lineLocalAffineEquiv S.field.Carrier (localProjection D S m 1 l)).right = a
  rw [hl, MulEquiv.apply_symm_apply]
  rfl

theorem planeProjection_ker : (planeProjection D S m).ker = pCore 2 ((flag D S m).Li 1) := by
  have hc := (localProjection D S m 1).comap_pCore_of_ker_isPGroup
    (localProjection_surjective D S m 1) (localProjection_ker_isTwoGroup D S m 1)
  rw [← hc]
  change _ = (pCore 2 (lineLocalSL S.field.Carrier)).comap (localProjection D S m 1)
  rw [lineLocalSL_twoCore_eq]
  rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {F : Type*} [Field F]

def alignedPlaneEquiv (a : SL(3,F)) : Model.flagFor a 1 ≃ₗ[F] Model.plane (F := F) where
  toFun v := ⟨specialLinearNatural 3 a⁻¹ v,(mem_flagFor_iff a 1 v).mp v.property⟩
  invFun v := ⟨specialLinearNatural 3 a v,⟨v,v.property,rfl⟩⟩
  left_inv v := by apply Subtype.ext; simp [map_inv]
  right_inv v := by apply Subtype.ext; simp [map_inv]
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' t v := by apply Subtype.ext; exact map_smul _ _ _

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

def planeEquiv : Additive ((flag D S m).Vi 1) ≃ₗ[ZMod 2] (Fin 2 → S.field.Carrier) :=
  let e₀ : Additive ((flag D S m).Vi 1) ≃+ Model.flagFor (alignment D S m) 1 :=
    (subspaceEquiv D S m ((flag D S m).space 1)).toAdditiveLeft
  let e := (e₀.trans (alignedPlaneEquiv (alignment D S m)).toAddEquiv).trans
    Model.planeEquiv.toAddEquiv
  { e with map_smul' := ZMod.map_smul e }

theorem planeEquiv_apply (v : Additive ((flag D S m).Vi 1)) (i : Fin 2) :
    planeEquiv D S m v i = (specialLinearNatural 3 (alignment D S m)⁻¹
      ((coordinates D S m).projection
        ⟨v.toMul,D.centralQuotientPreimage_le _ v.toMul.property⟩).toAdd) i.castSucc := rfl

/-- The literal ambient conjugation intertwines the marked upper-left block. -/
theorem planeEquiv_intertwines (l : (flag D S m).Li 1)
    (v : Additive ((flag D S m).Vi 1)) :
    planeEquiv D S m (Components.flagAction (flag D S m) 1
      ⟨l,(localResidual_le _ l.property).2⟩ v) =
      specialLinearNatural 2 (planeProjection D S m l) (planeEquiv D S m v) := by
  let a := alignment D S m
  let c := coordinates D S m
  let v' : V := ⟨v.toMul,D.centralQuotientPreimage_le _ v.toMul.property⟩
  let l' : L := ⟨l,(localResidual_le _ l.property).1⟩
  let w := specialLinearNatural 3 a⁻¹ (c.projection v').toAdd
  have hw : w 2 = 0 :=
    (mem_flagFor_iff a 1 _).mp ((c.mem_preimage ((flag D S m).space 1) v').mp v.toMul.property)
  have he : specialLinearNatural 3 a⁻¹
      (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l') v')).toAdd =
      specialLinearNatural 3 (localProjection D S m 1 l).val w := by
    rw [c.projection_component_conjugation,localProjection_coe]
    change specialLinearNatural 3 a⁻¹ (specialLinearNatural 3 (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l'))
      (c.projection v').toAdd) = specialLinearNatural 3 (a⁻¹ * m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l') * (a⁻¹)⁻¹) w
    simp [w,map_mul,map_inv]
  ext i
  rw [planeEquiv_apply]
  change (specialLinearNatural 3 a⁻¹
    (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l') v')).toAdd) i.castSucc = _
  rw [he]
  change ((localProjection D S m 1 l).val.val.mulVec w) i.castSucc =
    ((lineToAffine S.field.Carrier (localProjection D S m 1 l)).right.val.mulVec
      (fun j => w j.castSucc)) i
  fin_cases i <;>
    simp [lineToAffine,mulVec,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three,hw]

/-- The intrinsic two-core centralizes the original plane, not only its quotient. -/
theorem plane_core_centralizes :
    ((flag D S m).Li 1).pCoreIn 2 ≤ centralizer ((flag D S m).Vi 1 : Set G) := by
  rintro x ⟨l,hl,rfl⟩ v hv
  have hl' : planeProjection D S m l = 1 := by
    exact (show l ∈ (planeProjection D S m).ker from (planeProjection_ker D S m).symm ▸ hl)
  have he := planeEquiv_intertwines D S m l (Additive.ofMul ⟨v,hv⟩)
  rw [hl',map_one,Module.End.one_apply] at he
  have hh := congrArg (fun w : Additive ((flag D S m).Vi 1) => (w.toMul : G))
    ((planeEquiv D S m).injective he)
  change (l : G) * v * (l : G)⁻¹ = v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

theorem plane_nonzero_transitive (v w : Additive ((flag D S m).Vi 1))
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ l : (flag D S m).Li 1,
      Components.flagAction (flag D S m) 1 ⟨l,(localResidual_le _ l.property).2⟩ v = w := by
  let e := planeEquiv D S m
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier (e v) (e w)
    (fun h => hv (e.injective (h.trans e.map_zero.symm)))
    (fun h => hw (e.injective (h.trans e.map_zero.symm)))
  obtain ⟨l,hl⟩ := planeProjection_surjective D S m a
  refine ⟨l,e.injective ?_⟩
  rw [planeEquiv_intertwines,hl]
  exact ha

private theorem plane_invariant_dichotomy
    (W : Submodule (ZMod 2) (Additive ((flag D S m).Vi 1)))
    (hW : ((flag D S m).Li 1).subgroupOf (normalizer ((flag D S m).Vi 1 : Set G)) ≤
      subspaceStabilizer (Components.flagAction (flag D S m) 1) W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hz : W = ⊥
  · exact Or.inl hz
  right
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ W.zero_mem
  obtain ⟨l,hl⟩ := plane_nonzero_transitive D S m v w hv0 hw
  exact hl ▸ (hW (show (⟨l,(localResidual_le _ l.property).2⟩ :
    normalizer ((flag D S m).Vi 1 : Set G)) ∈
      ((flag D S m).Li 1).subgroupOf _ from l.property) v).mpr hv

theorem plane_isIrrPlus : IsIrrPlus (Components.flagAction (flag D S m) 1)
    (((flag D S m).Li 1).subgroupOf (normalizer ((flag D S m).Vi 1 : Set G))) ⊤ := by
  let ρ := Components.flagAction (flag D S m) 1
  let K := ((flag D S m).Li 1).subgroupOf (normalizer ((flag D S m).Vi 1 : Set G))
  have hn : ¬ (⊤ : Submodule (ZMod 2) (Additive ((flag D S m).Vi 1))) ≤ fixedSpace ρ K := by
    intro h
    let e := planeEquiv D S m
    let v := e.symm ![1,0]
    let w := e.symm ![0,1]
    have hv : v ≠ 0 := by
      intro hz
      have hh := congrArg e hz
      simp [v] at hh
    have hw : w ≠ 0 := by
      intro hz
      have hh := congrArg e hz
      simp [w] at hh
    obtain ⟨l,hl⟩ := plane_nonzero_transitive D S m v w hv hw
    have hh := h (show v ∈ (⊤ : Submodule (ZMod 2) _) from trivial)
      (⟨⟨l,(localResidual_le _ l.property).2⟩,l.property⟩ : K)
    have he : w = v := hl.symm.trans hh
    have h0 := congrFun (congrArg e he) 0
    simp [v,w] at h0
  have hc : subspaceCommutator ρ ⊤ K = ⊤ := by
    rcases plane_invariant_dichotomy D S m _ (subspaceCommutator_invariant ρ ⊤ K) with h | h
    · exact (hn ((subspaceCommutator_eq_bot_iff ρ ⊤ K).mp h)).elim
    · exact h
  apply isIrrPlus_of_minimal ρ (by intro x hx v; simp) hc hn
  intro W hW _
  rcases plane_invariant_dichotomy D S m W hW with h | h
  · exact Or.inr (h ▸ bot_le)
  · exact Or.inl h

/-- The local-action premises of source 11.1.3 are now discharged; only its
preceding, genuinely relative component assertion remains explicit. -/
theorem uniqueNoncentral_second
    (hL : Source.ComponentIn (normalizer ((flag D S m).Vi 1 : Set G)) ((flag D S m).Li 1)) :
    Source.UniqueNoncentralComponent (normalizer ((flag D S m).Vi 1 : Set G))
      ((flag D S m).Vi 1) ((flag D S m).Li 1) :=
  Components.uniqueNoncentral_second (flag D S m) S hL
    (plane_isIrrPlus D S m) (plane_core_centralizes D S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

theorem alignedQuotient_ker : (alignedQuotient D S m).ker = pCore 2 L := by
  ext x
  change MulAut.conj (alignment D S m)⁻¹ (m.groupEquiv
    (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff _ (MulAut.conj (alignment D S m)⁻¹).injective,
    map_eq_one_iff _ m.groupEquiv.injective]
  exact QuotientGroup.eq_one_iff _

theorem local_image (i : Fin 2) :
    (((flag D S m).Li i).subgroupOf L).map (alignedQuotient D S m) =
      localGroup (F := S.field.Carrier) i := by
  ext g
  constructor
  · rintro ⟨l,hl,rfl⟩
    have he := localProjection_coe D S m i ⟨l,hl⟩
    exact he ▸ (localProjection D S m i ⟨l,hl⟩).property
  · intro hg
    obtain ⟨l,hl⟩ := localProjection_surjective D S m i ⟨g,hg⟩
    refine ⟨⟨l,(localResidual_le _ l.property).1⟩,l.property,?_⟩
    exact (localProjection_coe D S m i l).symm.trans (congrArg Subtype.val hl)

theorem core_normalizes_local (i : Fin 2) :
    L.pCoreIn 2 ≤ normalizer ((flag D S m).Li i : Set G) := by
  rintro x ⟨l,hl,rfl⟩
  let c := coordinates D S m
  let U := (flag D S m).Vi i.castSucc
  let H := L ⊓ normalizer (U : Set G)
  have hq : c.quotientMap l = 1 := by
    change c.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff _).mpr hl
    exact (congrArg c.groupEquiv he).trans c.groupEquiv.map_one
  have hx : (l : G) ∈ H := by
    refine ⟨l.property,?_⟩
    apply (c.mem_normalizer_preimage_iff ((flag D S m).space i.castSucc) l).mpr
    rw [hq,map_one]
    intro v
    rfl
  exact normalizer_le_normalizer_characteristic_image H (solvableResidual H)
    (H.le_normalizer hx)

/-- The two original local residuals generate L, including its solvable kernel.
Perfectness eliminates the solvable supplement after quotient generation. -/
theorem locals_generate : L = (flag D S m).Li 0 ⊔ (flag D S m).Li 1 := by
  let f := flag D S m
  let A := (f.Li 0).subgroupOf L
  let B := (f.Li 1).subgroupOf L
  let J := A ⊔ B
  let q := alignedQuotient D S m
  have ha : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hb : f.Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  have hj : J.map L.subtype = f.Li 0 ⊔ f.Li 1 := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le ha,map_subgroupOf_eq_of_le hb]
  have him : J.map q = ⊤ := by
    rw [Subgroup.map_sup,local_image D S m 0,local_image D S m 1]
    exact localsSL_sup_eq_top S.field.Carrier
  have hsup : J ⊔ q.ker = ⊤ := by
    rw [← comap_map_eq,him,comap_top]
  have hnorm : q.ker ≤ normalizer (J : Set L) := by
    apply le_trans (le_inf ?_ ?_) (normalizer_inf_normalizer_le_normalizer_sup A B)
    · intro l hl
      have hk : (l : G) ∈ L.pCoreIn 2 :=
        mem_map_of_mem L.subtype ((alignedQuotient_ker D S m) ▸ hl)
      rw [← subgroupOf_normalizer_eq ha]
      exact core_normalizes_local D S m 0 hk
    · intro l hl
      have hk : (l : G) ∈ L.pCoreIn 2 :=
        mem_map_of_mem L.subtype ((alignedQuotient_ker D S m) ▸ hl)
      rw [← subgroupOf_normalizer_eq hb]
      exact core_normalizes_local D S m 1 hk
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  let : Group.IsPerfect (f.Li 1) := localResidual_perfect _
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe ha).symm.toMonoidHom) (subgroupOfEquivOfLe ha).symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hb).symm.toMonoidHom) (subgroupOfEquivOfLe hb).symm.surjective
  let : Group.IsPerfect J := by
    rw [isPerfect_iff]
    apply le_antisymm (commutator_le_self _)
    exact sup_le ((commutator_eq_self (H := A)).symm.le.trans
      (commutator_mono le_sup_left le_sup_left))
      ((commutator_eq_self (H := B)).symm.le.trans (commutator_mono le_sup_right le_sup_right))
  let : Group.IsNilpotent q.ker := by rw [alignedQuotient_ker]; exact pCore_isNilpotent
  have he := map_solvableResidual_sup_eq_of_perfect_normalized J q.ker hnorm
  rw [hsup,solvableResidual_eq_top,← MonoidHom.range_eq_map,range_subtype] at he
  have hJ : J = ⊤ := he.symm
  rw [← hj,hJ,← MonoidHom.range_eq_map,range_subtype]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {F : Type*} [Field F]

private theorem upper_fixed (v : Fin 2 → F) : v 1 = 0 ↔
    ∀ g ∈ upperUnipotent F, specialLinearNatural 2 g v = v := by
  constructor
  · intro hv g hg
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F g).mp hg
    ext i
    fin_cases i <;> simp [specialLinearNatural_apply,transvection_coe,mulVec,dotProduct,
      Fin.sum_univ_two,hv]
  · intro h
    have he := congrFun (h (transvection zero_ne_one (1:F))
      ((mem_upperUnipotent F _).mpr ⟨1,rfl⟩)) 0
    simpa [specialLinearNatural_apply,transvection_coe,mulVec,dotProduct,Fin.sum_univ_two] using he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

def planeSylow : Sylow 2 ((flag D S m).Li 1) :=
  (Sylow.mapSurjective_surjective (planeProjection_surjective D S m) 2
    (upperUnipotentSylow S.field.Carrier 2)).choose

theorem planeSylow_image :
    (planeSylow D S m : Subgroup ((flag D S m).Li 1)).map (planeProjection D S m) =
      upperUnipotent S.field.Carrier :=
  congrArg (fun P : Sylow 2 SL(2,S.field.Carrier) => (P : Subgroup SL(2,S.field.Carrier)))
    (Sylow.mapSurjective_surjective (planeProjection_surjective D S m) 2
      (upperUnipotentSylow S.field.Carrier 2)).choose_spec

private theorem point_mem_iff (v : (flag D S m).Vi 1) :
    (v : G) ∈ (flag D S m).Vi 0 ↔ planeEquiv D S m (Additive.ofMul v) 1 = 0 := by
  let c := coordinates D S m
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ v.property⟩
  have hv := (c.mem_preimage ((flag D S m).space 1) v').mp v.property
  change (c.projection v').toAdd ∈ Model.flagFor (alignment D S m) 1 at hv
  rw [mem_flagFor_iff] at hv
  rw [planeEquiv_apply]
  change (v' : G) ∈ c.preimage ((flag D S m).space 0) ↔ _
  rw [c.mem_preimage]
  change (c.projection v').toAdd ∈ Model.flagFor (alignment D S m) 0 ↔ _
  rw [mem_flagFor_iff]
  change (_ = 0 ∧ _ = 0) ↔ _ = 0
  exact ⟨And.left, fun h => ⟨h,hv⟩⟩

/-- The original point is the fixed subgroup of an actual Sylow of L₂. -/
theorem planeSylow_fixed :
    (flag D S m).Vi 0 = (flag D S m).Vi 1 ⊓
      centralizer (((planeSylow D S m : Subgroup ((flag D S m).Li 1))).map
        ((flag D S m).Li 1).subtype : Set G) := by
  let f := flag D S m
  ext v
  constructor
  · intro hv
    have hv2 : v ∈ f.Vi 1 := f.Vi_mono (by decide : (0:Fin 3) ≤ 1) hv
    refine ⟨hv2,?_⟩
    rintro x ⟨l,hl,rfl⟩
    have hz := (point_mem_iff D S m ⟨v,hv2⟩).mp hv
    have hq : planeProjection D S m l ∈ upperUnipotent S.field.Carrier :=
      planeSylow_image D S m ▸ mem_map_of_mem _ hl
    have he := planeEquiv_intertwines D S m l (Additive.ofMul ⟨v,hv2⟩)
    rw [(upper_fixed _).mp hz _ hq] at he
    have hh := congrArg (fun w : Additive (f.Vi 1) => (w.toMul : G))
      ((planeEquiv D S m).injective he)
    change (l : G) * v * (l : G)⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · rintro ⟨hv,hc⟩
    apply (point_mem_iff D S m ⟨v,hv⟩).mpr
    apply (upper_fixed _).mpr
    intro g hg
    rw [← planeSylow_image D S m] at hg
    obtain ⟨l,hl,rfl⟩ := hg
    rw [← planeEquiv_intertwines]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * v * (l : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (hc l (mem_map_of_mem _ hl))

/-- The fixed-space family supplies the exact 11.2.4 orbit reduction.
Relative normality is the separate preceding source premise. -/
theorem point_orbit
    (hN : normalizer ((flag D S m).Vi 1 : Set G) ≤
      normalizer ((flag D S m).Li 1 : Set G)) :
    ∀ y ∈ normalizer ((flag D S m).Vi 1 : Set G),
      ∃ l ∈ (flag D S m).Li 1,
        ((flag D S m).Vi 0).map (MulAut.conj y).toMonoidHom =
          ((flag D S m).Vi 0).map (MulAut.conj l).toMonoidHom :=
  WeakClosure.Nonnormalization.point_orbit_of_sylow_fixed D S
    (flag D S m) hN (planeSylow D S m) (planeSylow_fixed D S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- L is transitive on the original preimages of all field lines. -/
theorem field_lines_transitive
    (U W : Submodule S.field.Carrier (Fin 3 → S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1)
    (hW : Module.finrank S.field.Carrier W = 1) :
    ∃ l : L, ((coordinates D S m).preimage U).map (MulAut.conj (l : G)).toMonoidHom =
      (coordinates D S m).preimage W := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show U ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hU; omega)
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hW; omega)
  obtain ⟨a,ha⟩ := SpecialLinearGroup.exists_mulVec_eq_three v w hv0 hw0
  obtain ⟨l,hl⟩ := (coordinates D S m).quotientMap_surjective a
  refine ⟨l,?_⟩
  rw [← (coordinates D S m).preimage_map_action l U]
  congr 1
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hU hv hv0,
    eq_span_singleton_of_mem_of_finrank_eq_one hW hw hw0]
  rw [Submodule.map_span,Set.image_singleton]
  rw [hl]
  exact congrArg (fun v => Submodule.span S.field.Carrier {v}) ha

/-- L₂ is transitive on the original preimages of field lines inside V₂. -/
theorem plane_field_lines_transitive
    (U W : Submodule S.field.Carrier (Fin 3 → S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1)
    (hW : Module.finrank S.field.Carrier W = 1)
    (hUP : U ≤ (flag D S m).space 1) (hWP : W ≤ (flag D S m).space 1) :
    ∃ l : (flag D S m).Li 1,
      ((coordinates D S m).preimage U).map (MulAut.conj (l : G)).toMonoidHom =
        (coordinates D S m).preimage W := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show U ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hU; omega)
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hW; omega)
  let e := (alignedPlaneEquiv (alignment D S m)).trans Model.planeEquiv
  let v' : (flag D S m).space 1 := ⟨v,hUP hv⟩
  let w' : (flag D S m).space 1 := ⟨w,hWP hw⟩
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier (e v') (e w')
    (fun h => hv0 (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm))))
    (fun h => hw0 (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm))))
  obtain ⟨l,hl⟩ := planeProjection_surjective D S m a
  let c := coordinates D S m
  let v0 : (flag D S m).Vi 1 := (subspaceEquiv D S m _).symm (Multiplicative.ofAdd v')
  let w0 : (flag D S m).Vi 1 := (subspaceEquiv D S m _).symm (Multiplicative.ofAdd w')
  have hev : planeEquiv D S m (Additive.ofMul v0) = e v' := by
    change e ((subspaceEquiv D S m _) v0).toAdd = e v'
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hew : planeEquiv D S m (Additive.ofMul w0) = e w' := by
    change e ((subspaceEquiv D S m _) w0).toAdd = e w'
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have he := planeEquiv_intertwines D S m l (Additive.ofMul v0)
  rw [hl,hev] at he
  have hact := (planeEquiv D S m).injective (he.trans (ha.trans hew.symm))
  let l' : L := ⟨l,(localResidual_le _ l.property).1⟩
  have hvec : c.modelAction (c.quotientMap l') v = w := by
    have he := congrArg (fun z : Additive ((flag D S m).Vi 1) =>
      ((subspaceEquiv D S m _) z.toMul).toAdd.val) hact
    change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l')
      ⟨v0,D.centralQuotientPreimage_le _ v0.property⟩)).toAdd =
      ((subspaceEquiv D S m _) w0).toAdd.val at he
    rw [c.projection_component_conjugation] at he
    change c.modelAction (c.quotientMap l') ((subspaceEquiv D S m _) v0).toAdd.val =
      ((subspaceEquiv D S m _) w0).toAdd.val at he
    simpa only [v0,w0,MulEquiv.apply_symm_apply,toAdd_ofAdd] using he
  refine ⟨l,?_⟩
  rw [← c.preimage_map_action l']
  congr 1
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hU hv hv0,
    eq_span_singleton_of_mem_of_finrank_eq_one hW hw hw0,
    Submodule.map_span,Set.image_singleton,hvec]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

private theorem fixed_conjugate (P : Sylow 2 ((flag D S m).Li 1))
    (l : (flag D S m).Li 1) :
    (((flag D S m).Vi 1 ⊓ centralizer
      ((P : Subgroup ((flag D S m).Li 1)).map ((flag D S m).Li 1).subtype : Set G))).map
        (MulAut.conj (l : G)).toMonoidHom =
      (flag D S m).Vi 1 ⊓ centralizer
        (((l • P : Sylow 2 ((flag D S m).Li 1)) : Subgroup ((flag D S m).Li 1)).map
          ((flag D S m).Li 1).subtype : Set G) := by
  let f := flag D S m
  have hV : (f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom = f.Vi 1 :=
    mem_normalizer_iff_map_conj_eq.mp (localResidual_le _ l.property).2
  rw [map_inf _ _ _ (MulAut.conj (l : G)).injective,hV,
    Theory.GroupTheory.map_centralizer_equiv]
  have he : ((P : Subgroup (f.Li 1)).map (f.Li 1).subtype).map
      (MulAut.conj (l : G)).toMonoidHom =
      ((l • P : Sylow 2 (f.Li 1)) : Subgroup (f.Li 1)).map (f.Li 1).subtype := by
    rw [Sylow.coe_subgroup_smul]
    change _ = ((P : Subgroup (f.Li 1)).map (MulAut.conj l).toMonoidHom).map _
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
  exact congrArg (fun X : Subgroup G => f.Vi 1 ⊓ centralizer (X : Set G)) he

/-- The orbit of the original point is exactly the family of fixed subgroups
of all Sylow 2-subgroups of the actual local residual. -/
theorem point_orbit_eq_sylow_fixed :
    {U : Subgroup G | ∃ l ∈ (flag D S m).Li 1,
      ((flag D S m).Vi 0).map (MulAut.conj l).toMonoidHom = U} =
    {U : Subgroup G | ∃ P : Sylow 2 ((flag D S m).Li 1),
      U = (flag D S m).Vi 1 ⊓ centralizer
        ((P : Subgroup ((flag D S m).Li 1)).map ((flag D S m).Li 1).subtype : Set G)} := by
  let P := planeSylow D S m
  ext U
  constructor
  · rintro ⟨l,hl,rfl⟩
    refine ⟨(⟨l,hl⟩ : (flag D S m).Li 1) • P,?_⟩
    rw [planeSylow_fixed]
    exact fixed_conjugate D S m P ⟨l,hl⟩
  · rintro ⟨Q,rfl⟩
    obtain ⟨l,hl⟩ := MulAction.exists_smul_eq ((flag D S m).Li 1) P Q
    refine ⟨l,l.property,?_⟩
    rw [planeSylow_fixed]
    rw [fixed_conjugate,hl]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.PlaneAction