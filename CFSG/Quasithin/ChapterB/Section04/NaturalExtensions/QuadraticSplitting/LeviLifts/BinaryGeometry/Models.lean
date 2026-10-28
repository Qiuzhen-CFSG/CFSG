module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry.Preparation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# Shared models for the binary block coordinates

The standard Levi is the actual stabilizer of the coordinate hyperplane and
pointwise fixer of its complementary line inside SL_n(2). Its elementary
roots are explicit subtype elements. Field transport identifies every
one-degree defining field with ZMod 2 and preserves those elementary matrices.

`BlockCoordinates` asks for the standard fixed-line-plus-natural decomposition;
`OriginalCoordinates` asks for its separate transport from the original natural
submodule, allowing the reversed root from the contragredient marking. These
are geometric construction targets, not source assumptions. Their application
and the independent seed-placement proof are in the parent BinaryGeometry.

Source: Aschbacher–Smith, B.4.9(1), printed pp.92–93.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open Representation.OneCohomology.SLHigherNatural Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
open QuasisimpleSource
variable {F : BinaryField} {n : ℕ}

/-- The actual defining-field identification at degree one. -/
noncomputable def fieldEquiv (hF : F.degree = 1) : F.Carrier ≃+* ZMod 2 := by
  letI := Fintype.ofFinite F.Carrier
  have hc : Fintype.card F.Carrier = 2 := by
    simpa [hF] using F.card_eq
  exact (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two hc).symm

/-- Entrywise field transport on both actors and natural vectors. -/
noncomputable def naturalFieldEquiv (hF : F.degree = 1) (n : ℕ) :
    ActionEquiv (linearNatural F n) (specialLinearNatural (k := ZMod 2) n) := by
  let e := fieldEquiv hF
  let l : F.Carrier ≃ₗ[ZMod 2] ZMod 2 :=
    { e.toAddEquiv with map_smul' := ZMod.map_smul e }
  refine ⟨Atlas.fieldEquivSL n e, LinearEquiv.piCongrRight (fun _ : Fin n => l), ?_⟩
  intro g v
  funext i
  change e (∑ j, g.val i j * v j) = ∑ j, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

/-- Field transport preserves the unit elementary matrices. -/
theorem naturalFieldEquiv_root (hF : F.degree = 1) {a b : Fin n} (hab : a ≠ b) :
    (naturalFieldEquiv hF n).groupEquiv (transvection hab 1) = transvection hab 1 := by
  ext i j
  change fieldEquiv hF ((transvection hab (1 : F.Carrier)).val i j) =
    (transvection hab (1 : ZMod 2)).val i j
  simp [transvection_coe, Matrix.one_apply, Matrix.single_apply]

/-- The coordinate hyperplane x_j = 0. -/
def standardAxis (n : ℕ) (j : Fin n) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (LinearMap.proj j)

/-- The complementary coordinate line. -/
def standardLine (n : ℕ) (j : Fin n) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {Pi.single j 1}

/-- The literal block Levi in the binary matrix group. -/
noncomputable def standardLevi (n : ℕ) (j : Fin n) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  subspaceStabilizer (specialLinearNatural n) (standardAxis n j) ⊓
    subspaceKernel (specialLinearNatural n) (standardLine n j) ⊤

/-- Its restriction on the full original n-dimensional natural space. -/
noncomputable def standardAction (n : ℕ) (j : Fin n) :
    Representation (ZMod 2) (standardLevi n j) (Fin n → ZMod 2) :=
  (specialLinearNatural n).comp (standardLevi n j).subtype

/-- Every elementary root avoiding j lies in the standard block Levi. -/
theorem standard_root_mem {j a b : Fin n} (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j) :
    transvection hab (1 : ZMod 2) ∈ standardLevi n j := by
  constructor
  · intro v
    change (specialLinearNatural n (transvection hab 1) v) j = 0 ↔ v j = 0
    rw [action_transvection]
    simp [Pi.single_eq_of_ne haj.symm]
  · refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [action_transvection]
    simp [Pi.single_eq_of_ne hbj]

/-- An elementary root as an element of the standard Levi. -/
noncomputable def standardRoot {j a b : Fin n} (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j) :
    standardLevi n j := ⟨transvection hab 1, standard_root_mem hab haj hbj⟩

/-- The standard block action and elementary-root compatibility to construct. -/
structure BlockCoordinates (n : ℕ) (j : Fin n) where
  action : ActionEquiv (standardAction n j) (binaryModel (n - 1))
  roots : ∀ (a b : Fin n) (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j),
    ∃ u v : Fin (n - 1), ∃ huv : u ≠ v,
      action.groupEquiv (standardRoot hab haj hbj) = transvection huv 1

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {d : DoubleNatural F n ρ}

/-- Transport of the original natural submodule, with either coherent root orientation. -/
structure OriginalCoordinates (m : QuotientCoordinates d) (j : Fin n) where
  action : ActionEquiv (d.space.toRepresentation.comp (m.K j).subtype) (standardAction n j)
  roots : ∀ (a b : Fin n) (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j),
    action.groupEquiv ⟨m.action.groupEquiv.symm (transvection hab 1),
      elementary_mem_Levi m hbj hab haj 1⟩ = standardRoot hab haj hbj ∨
    action.groupEquiv ⟨m.action.groupEquiv.symm (transvection hab 1),
      elementary_mem_Levi m hbj hab haj 1⟩ = standardRoot hab.symm hbj haj

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
