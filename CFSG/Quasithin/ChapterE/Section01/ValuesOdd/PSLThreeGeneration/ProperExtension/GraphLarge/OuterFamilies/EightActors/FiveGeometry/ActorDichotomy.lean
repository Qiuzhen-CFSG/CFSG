module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.Families
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.MonomialGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.FieldTransport

/-!
# The prime-five actor dichotomy

The finite calculation is confined to the literal PSL₃(ZMod 5):2 carrier.
Field transport carries an arbitrary field of order five to that carrier,
including its marked inner subgroup, centralizer residual supplement,
solvable radical, quotient map and derived subgroup. The family calculation
then retains an actual original-family actor, or a solvable generating
overgroup. The final theorem applies `fiveGeometryAt_of_unmarked` with the
independently supplied S₅ quotient model.

The proved monomial join and outer-actor reselection discharge both finite
calculations. If every nonidentity family member in the Sylow lies in the
first orbit, equality of weak closures gives the solvable-overgroup alternative.
Otherwise an actual family conjugate supplies the quotient alternative.
The original conditional reductions remain available. The final geometry
theorems retain only the independent S₅ quotient-model premise, whose producer
is `FiveQuotientModel.residual_quotient_model`; the parent owns its discharge
and the remaining E.1.14(7) assembly.
Source: Aschbacher--Smith E.1.1--5, E.1.8, E.1.10, E.1.13 and E.1.14(7),
printed pp.209--214. Field transport reuses the attributed ATLAS port;
its source and license remain in `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩


section FieldTransport
variable {F E : Type*} [Field F] [Field E]

/-- Field transport carries the marked inner subgroup to the marked inner
subgroup, not to an arbitrary isomorphic simple subgroup. -/
theorem fieldEquiv_innerPart (f : F ≃+* E) :
    (innerPart F).map ((FieldTransport.graphExtensionEquiv f) : graphExtension F →* graphExtension E) = innerPart E := by
  let e := FieldTransport.graphExtensionEquiv f
  apply Subgroup.map_injective (graphExtension E).subtype_injective
  rw [map_map]
  have he : (graphExtension E).subtype.comp (e : graphExtension F →* graphExtension E) =
      (MulAut.congr (Atlas.fieldEquivPSL 3 f)).toMonoidHom.comp (graphExtension F).subtype := by
    apply MonoidHom.ext
    intro x
    exact FieldTransport.graphExtensionEquiv_apply f x
  change (innerPart F).map ((graphExtension E).subtype.comp (e : graphExtension F →* graphExtension E)) = _
  rw [he, ← map_map]
  rw [innerPart, innerPart, map_subgroupOf_eq_of_le (show
    MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from le_sup_left),
    map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3,E) ≤ graphExtension E from le_sup_left)]
  exact MulAut.map_innerSubgroup_congr (Atlas.fieldEquivPSL 3 f)

end FieldTransport

variable (F : Type*) [Field F] [Finite F]

/-- Reduction of the requested unmarked geometry to two concrete calculations
on ZMod 5. All field, Sylow, family and literal quotient transports are proved. -/
theorem unmarked_of_model_calculations (hF : Nat.card F = 5)
    (hjoin : MonomialJoin) (hreselect : ModelReselection)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup _) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (z : graphExtension F) (hz : orderOf z = 2)
    (hzL : z ∈ innerPart F) (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    UnmarkedFiveGeometryAt F T Ω z := by
  classical
  let _ := Fintype.ofFinite F
  let f : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let e := FieldTransport.graphExtensionEquiv f
  let S := T.mapSurjective (f := (e : graphExtension F →* Model)) e.surjective
  let Γ : Set (Subgroup Model) := {B | B.map (e.symm : Model →* graphExtension F) ∈ Ω}
  have hΓ : IsElementaryFamily Γ := by
    simpa only [Γ, MulEquiv.toMonoidHom_eq_coe] using hΩ.comap_equiv e.symm
  have hback : (S : Subgroup Model).map (e.symm : Model →* graphExtension F) = (T : Subgroup _) := by
    change ((T : Subgroup _).map (e : graphExtension F →* Model)).map (e.symm : Model →* graphExtension F) = _
    simp [map_map]
  have h8 (B : Subgroup Model) (hB : B ∈ Γ) (hBS : B ≤ (S : Subgroup Model))
      (hb : B ≠ ⊥) : Nat.card B = 8 := by
    have hBT : B.map (e.symm : Model →* graphExtension F) ≤ (T : Subgroup _) := hback ▸ map_mono hBS
    have hne : B.map (e.symm : Model →* graphExtension F) ≠ ⊥ := by
      intro he
      apply hb
      have hm := congrArg (Subgroup.map (e : graphExtension F →* Model)) he
      simpa [map_map] using hm
    have hc := hEight (B.map (e.symm : Model →* graphExtension F)) hB hBT hne
    rwa [card_map_of_injective e.symm.injective] at hc
  have hAS : A.map (e : graphExtension F →* Model) ≤ (S : Subgroup Model) := map_mono hAT
  have hAΓ : A.map (e : graphExtension F →* Model) ∈ Γ := by
    change (A.map (e : graphExtension F →* Model)).map (e.symm : Model →* graphExtension F) ∈ Ω
    simpa [map_map] using hA
  have hc : Nat.card (A.map (e : graphExtension F →* Model)) = 8 := by
    rw [card_map_of_injective e.injective, hcard]
  have hzi : e z ∈ FiveSourceAudit.inner := by
    change e z ∈ innerPart (ZMod 5)
    rw [← fieldEquiv_innerPart f]
    exact mem_map_of_mem (e : graphExtension F →* Model) hzL
  have hSz : (S : Subgroup Model) ≤ centralizer ({e z} : Set Model) := by
    rw [← map_elementCentralizer e z]
    exact map_mono hTz
  have hz' : orderOf (e z) = 2 := (e.orderOf_eq z).trans hz
  have hm := residualQuotientModel_map e T z hmodel
  have hg := unmarked_model_of_calculations hjoin S Γ hΓ h8 (A.map (e : graphExtension F →* Model))
    hAΓ hAS hc (e z) (hreselect S (e z) hz' hzi hSz hm)
  have ht := unmarked_map_equiv e.symm S Ω (e z) hg
  have hs : S.mapSurjective (f := (e.symm : Model →* graphExtension F)) e.symm.surjective = T := by
    apply Sylow.ext
    exact hback
  simpa only [hs, MulEquiv.symm_apply_apply] using ht

/-- The actual conditional application to the published marked geometry.
Only the two finite calculations and the independent quotient model remain. -/
theorem fiveGeometry_of_model_calculations (hF : Nat.card F = 5)
    (hjoin : MonomialJoin) (hreselect : ModelReselection)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup _) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (z : graphExtension F) (hz : orderOf z = 2)
    (hzL : z ∈ innerPart F) (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    FiveGeometryAt F T Ω z :=
  fiveGeometryAt_of_unmarked F T Ω z
    (unmarked_of_model_calculations F hF hjoin hreselect T Ω hΩ hEight A hA hAT hcard
      z hz hzL hTz hmodel) hmodel

/-- The complete finite-family dichotomy at five. Both concrete orbit
calculations are discharged, and the quotient alternative uses an actual
member of the original family and the literal residual radical quotient.
The independent identification of that quotient with S₅ remains explicit. -/
theorem unmarked_of_quotient_model (hF : Nat.card F = 5)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup _) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (z : graphExtension F) (hz : orderOf z = 2)
    (hzL : z ∈ innerPart F) (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    UnmarkedFiveGeometryAt F T Ω z :=
  unmarked_of_model_calculations F hF monomialJoin OuterReselection.modelReselection
    T Ω hΩ hEight A hA hAT hcard z hz hzL hTz hmodel

/-- Mark the proved family dichotomy using the given quotient isomorphism.
This is the geometry consumed by `familyEscapes_of_five_geometry`. -/
theorem fiveGeometry_of_quotient_model (hF : Nat.card F = 5)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup _) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (z : graphExtension F) (hz : orderOf z = 2)
    (hzL : z ∈ innerPart F) (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    FiveGeometryAt F T Ω z :=
  fiveGeometryAt_of_unmarked F T Ω z
    (unmarked_of_quotient_model F hF T Ω hΩ hEight A hA hAT hcard z hz hzL hTz hmodel)
    hmodel

/-- The exact positioned-eight geometry contract used by the parent branch.
Its quotient-model premise is supplied by the independent literal-centralizer
producer; no monomial-generation or reselection premise remains. -/
theorem fiveEightGeometry_of_quotient_models (hF : Nat.card F = 5)
    (hmodels : ∀ (T : Sylow 2 (graphExtension F)) (z : graphExtension F),
      orderOf z = 2 → z ∈ innerPart F →
      (T : Subgroup _) ≤ centralizer ({z} : Set _) →
      let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    FiveEightGeometry F := by
  intro T Ω hΩ _hlarge _houter hEight A hA hAT hcard _hfour z hz hzL _hzA hTz
  exact fiveGeometry_of_quotient_model F hF T Ω hΩ hEight A hA hAT hcard z hz hzL hTz
    (hmodels T z hz hzL hTz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
