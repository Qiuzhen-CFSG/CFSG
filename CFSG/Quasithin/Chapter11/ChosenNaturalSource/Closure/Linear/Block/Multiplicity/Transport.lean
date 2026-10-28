module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity.Fixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Action

/-!
# Natural markings on the literal quotient U/V₁

Factor the original map U→G₁/V₁, identifying its image with U/V₁.
This multiplicative equivalence respects conjugation. The binary action
and its ActionEquiv are transported through precisely that equivalence;
pointAction_apply records agreement with the original quotient action.
The two-copy specialization constructs the NaturalPair used by the
selected outside-subgroup consumer.
Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

def quotientEquiv (hseed : E.V₃ = V) :
    (E.W ⧸ E.V₁.subgroupOf E.W) ≃* E.tilde (E.localClosure E.G₁) :=
  (Outside.quotientTildeEquiv E).trans (MulEquiv.subgroupCongr (by
    change E.tilde E.W = E.tilde (conjugateSpanBy E.V₃ E.G₁)
    rw [hseed]
    rfl))

theorem quotientEquiv_apply_mk (hseed : E.V₃ = V) (w : E.W) :
    (quotientEquiv E hseed (QuotientGroup.mk' (E.V₁.subgroupOf E.W) w) : E.Tilde) =
      QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
        ⟨w, Outside.closure_le_point_normalizer E w.property⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem quotientEquiv_action (hseed : E.V₃ = V) (f : E.ClosureFlag)
    (hK : E.K = E.L₁) (k : E.K) (w : E.W ⧸ E.V₁.subgroupOf E.W) :
    Additive.ofMul (quotientEquiv E hseed (Outside.quotientAction E E.K E.K_le_G₁ k w)) =
      action E f hK (QuotientGroup.mk' (pCore 2 E.K) k)
        (Additive.ofMul (quotientEquiv E hseed w)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [Geometry.ClosureFlag.quotientAction_apply]
  change (Outside.quotientTildeEquiv E
    (Outside.quotientAction E E.K E.K_le_G₁ k w) : E.Tilde) = _
  rw [Outside.quotientTildeEquiv_action]
  rfl

def PointSpace (_f : E.ClosureFlag) (_hseed : E.V₃ = V) :=
  Additive (E.W ⧸ E.V₁.subgroupOf E.W)

theorem pointElementary (f : E.ClosureFlag) (hseed : E.V₃ = V) :
    IsElementaryAbelian 2 (E.W ⧸ E.V₁.subgroupOf E.W) := by
  let := f.elementary E.G₁ le_rfl (sup_le E.L₁_le_G₁ f.sylow_normalizes_point)
  exact IsElementaryAbelian.of_injective (quotientEquiv E hseed).toMonoidHom
    (quotientEquiv E hseed).injective

instance pointAddCommGroup (f : E.ClosureFlag) (hseed : E.V₃ = V) :
    AddCommGroup (PointSpace E f hseed) := by
  letI := pointElementary E f hseed
  exact inferInstanceAs (AddCommGroup (Additive (E.W ⧸ E.V₁.subgroupOf E.W)))

instance pointModule (f : E.ClosureFlag) (hseed : E.V₃ = V) :
    Module (ZMod 2) (PointSpace E f hseed) := by
  letI := pointElementary E f hseed
  exact inferInstanceAs (Module (ZMod 2) (Additive (E.W ⧸ E.V₁.subgroupOf E.W)))

def pointEquiv (f : E.ClosureFlag) (hseed : E.V₃ = V) :
    PointSpace E f hseed ≃ₗ[ZMod 2] Space E f where
  __ := (quotientEquiv E hseed).toAdditive
  map_smul' c v := ZMod.map_smul
    (show PointSpace E f hseed ≃+ Space E f from (quotientEquiv E hseed).toAdditive) c v

def pointAction (f : E.ClosureFlag) (hseed : E.V₃ = V) (hK : E.K = E.L₁) :
    Representation (ZMod 2) (E.K ⧸ pCore 2 E.K) (PointSpace E f hseed) where
  toFun k := (pointEquiv E f hseed).symm.toLinearMap.comp
    ((action E f hK k).comp (pointEquiv E f hseed).toLinearMap)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [Module.End.mul_apply]

theorem pointAction_apply (f : E.ClosureFlag) (hseed : E.V₃ = V) (hK : E.K = E.L₁)
    (k : E.K) (w : PointSpace E f hseed) :
    pointAction E f hseed hK (QuotientGroup.mk' (pCore 2 E.K) k) w =
      Additive.ofMul (Outside.quotientAction E E.K E.K_le_G₁ k w.toMul) := by
  apply (pointEquiv E f hseed).injective
  change (pointEquiv E f hseed) ((pointEquiv E f hseed).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (quotientEquiv_action E hseed f hK k w.toMul).symm

def pointMarking (f : E.ClosureFlag) (hseed : E.V₃ = V) (hK : E.K = E.L₁) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r)) :
    ActionEquiv (pointAction E f hseed hK) (repeated (linearNatural E.input.field 2) r) where
  groupEquiv := e.groupEquiv
  linearEquiv := (pointEquiv E f hseed).trans e.linearEquiv
  intertwines k w := by
    change e.linearEquiv ((pointEquiv E f hseed) ((pointEquiv E f hseed).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact e.intertwines k _

def naturalPair (f : E.ClosureFlag) (hseed : E.V₃ = V) (hK : E.K = E.L₁)
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) 2)) :
    Outside.NaturalPair E where
  actor := e.groupEquiv
  coordinates := (quotientEquiv E hseed).trans e.linearEquiv.toAddEquiv.toMultiplicative
  natural k w := by
    change e.linearEquiv (Additive.ofMul (quotientEquiv E hseed
      (Outside.quotientAction E E.K E.K_le_G₁ k w))) = _
    rw [quotientEquiv_action]
    exact e.intertwines _ _

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
