module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Flag
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ResidualGeneration
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The literal rank-one quotients of the marked Sp4 flag

Conjugation identifies the marked stabilizers with the standard parabolics.
Their solvable residuals are the explicit determinant kernels. The standard
two-core quotients are SL2, and the canonical central quotient gives PSL2 in
characteristic two. Composing with the original residual projection retains
the original groups L_i and their literal two-cores.

Source: Aschbacher--Smith, opening section 11.1, pp.760--761.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped MatrixGroups
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4

section Model
variable {K : Type*} [Field K]

/-- Setwise subspace stabilizers conjugate by the actual natural matrix action. -/
theorem stabilizer_map (g : Sp K) (W : Submodule K (Vector K)) :
    stabilizer (W.map (toLinear g).toLinearMap) =
      (stabilizer W).map (MulAut.conj g).toMonoidHom := by
  ext a
  rw [mem_stabilizer_iff, Subgroup.mem_map_equiv]
  change (∀ x ∈ W.map (toLinear g).toLinearMap,
    a • x ∈ W.map (toLinear g).toLinearMap) ↔ g⁻¹ * a * g ∈ stabilizer W
  rw [mem_stabilizer_iff]
  constructor
  · intro h x hx
    have hh := h (g • x) ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hh
    change g • y = a • (g • x) at he
    have he' := congrArg (fun z => g⁻¹ • z) he
    simp only [inv_smul_smul] at he'
    rw [mul_smul, mul_smul, ← he']
    exact hy
  · rintro h _ ⟨x,hx,rfl⟩
    refine ⟨(g⁻¹ * a * g) • x, h x hx, ?_⟩
    change g • ((g⁻¹ * a * g) • x) = a • (g • x)
    simp only [mul_smul, smul_inv_smul]

end Model

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))

/-- The model stabilizer from the marking equals the literal matrix stabilizer. -/
theorem modelStabilizer_eq (U : Submodule F.Carrier (Coordinates.sp4 m).Space) :
    (Coordinates.sp4 m).modelStabilizer U = stabilizer U := by
  ext g
  change Sp F.Carrier at g
  change (∀ x : Vector F.Carrier, (g : Sp F.Carrier) • x ∈ U ↔ x ∈ U) ↔ _
  rw [mem_stabilizer_iff]
  constructor
  · exact fun h x hx => (h x).mpr hx
  · intro h x
    have hg := (mem_stabilizer_iff U g).mpr h
    constructor
    · intro hx
      have hh := (mem_stabilizer_iff U g⁻¹).mp ((stabilizer U).inv_mem hg) _ hx
      simpa only [inv_smul_smul] using hh
    · exact h x

/-- The marked parabolic is the conjugate of the standard one. -/
theorem modelStabilizer_space (i : Fin 2) :
    (Coordinates.sp4 m).modelStabilizer (space m i.castSucc.succ) =
      (stabilizer (ModelFlag.stage (F := F.Carrier) i.castSucc.succ)).map
        (MulAut.conj (alignment m)).toMonoidHom := by
  rw [modelStabilizer_eq]
  exact stabilizer_map _ _

/-- The actual stabilizer equivalence underlying residual transport. -/
def stabilizerEquiv (i : Fin 2) :
    (Coordinates.sp4 m).modelStabilizer (space m i.castSucc.succ) ≃*
      stabilizer (ModelFlag.stage (F := F.Carrier) i.castSucc.succ) :=
  (MulEquiv.subgroupCongr (modelStabilizer_space m i)).trans
    ((MulAut.conj (alignment m)).subgroupMap _).symm

/-- Standard point and plane determinant kernels in the matrix group. -/
def standardLocal (i : Fin 2) : Subgroup (Sp F.Carrier) :=
  if i = 0 then pointLocal else planeLocal

/-- The residual isomorphism retains the literal standard local subgroup. -/
def standardResidualEquiv (hn : 1 < F.degree) (i : Fin 2) :
    solvableResidual (stabilizer (ModelFlag.stage (F := F.Carrier) i.castSucc.succ)) ≃*
      standardLocal (F := F) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ((solvableResidual (pointParabolic (F := F.Carrier))).equivMapOfInjective
      pointParabolic.subtype pointParabolic.subtype_injective).trans
        (MulEquiv.subgroupCongr (pointParabolic_solvableResidual_eq F.card_eq hn))
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ((solvableResidual (planeParabolic (F := F.Carrier))).equivMapOfInjective
      planeParabolic.subtype planeParabolic.subtype_injective).trans
        (MulEquiv.subgroupCongr (planeParabolic_solvableResidual_eq F.card_eq hn))

/-- The marked residual and the concrete determinant kernel are isomorphic. -/
def modelResidualEquiv (hn : 1 < F.degree) (i : Fin 2) :
    solvableResidual ((Coordinates.sp4 m).modelStabilizer (space m i.castSucc.succ)) ≃*
      standardLocal (F := F) i :=
  (stabilizerEquiv m i).solvableResidualEquiv.trans (standardResidualEquiv hn i)

/-- The standard local two-core quotient, over this exact defining field. -/
def standardLocalCoreQuotientEquiv (hn : 1 < F.degree) (i : Fin 2) :
    (standardLocal (F := F) i ⧸ pCore 2 (standardLocal (F := F) i)) ≃* PSL(2,F.Carrier) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (pointLocalCoreQuotientEquiv F.card_eq hn).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (planeLocalCoreQuotientEquiv F.card_eq hn).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL

/-- The source parabolic residual has the literal PSL2 two-core quotient. -/
def localCoreQuotientEquiv (hn : 1 < F.degree) (i : Fin 2) :
    (localResidual L ((Coordinates.sp4 m).preimage (space m i.castSucc.succ)) ⧸
      pCore 2 (localResidual L ((Coordinates.sp4 m).preimage (space m i.castSucc.succ)))) ≃*
        PSL(2,F.Carrier) :=
  ((Coordinates.sp4 m).residualCoreQuotientEquiv _).trans
    ((QuotientGroup.congr _ _ (modelResidualEquiv m hn i)
      (pCore_map_iso 2 (modelResidualEquiv m hn i))).trans
        (standardLocalCoreQuotientEquiv hn i))

/-- Application to the actual constructed source flag, with no model callback. -/
def flag_Li_quotientEquiv (S : D.NonbinaryNaturalInput)
    (hn : 1 < F.degree) (i : Fin 2) :
    ((flag m S).Li i ⧸ pCore 2 ((flag m S).Li i)) ≃* PSL(2,F.Carrier) :=
  localCoreQuotientEquiv m hn i

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4
