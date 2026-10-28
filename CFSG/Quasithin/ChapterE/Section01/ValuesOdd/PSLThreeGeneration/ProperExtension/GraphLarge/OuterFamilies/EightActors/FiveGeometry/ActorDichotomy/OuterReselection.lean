module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.Families
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Position

/-!
# Reselection from a fixed Sylow and a literal representative

Sylow conjugacy sends the original actor and the specified inner involution
to the fixed coordinates. The central involution is unique there. Fusion to
the representative and the representative's radical-quotient position then
produce an actual conjugate of the whole original actor back in its original
Sylow. The quotient maps and derived subgroups are transported by their
induced isomorphisms.

The exhaustive fusion and quotient-position calculations are discharged by
the fixed-coordinate proofs, establishing `ModelReselection`. The family
application retains the independent monomial join and S₅ quotient-model
premises; the full source E.1.14(7) assembly remains with its consumer.
Source: Aschbacher--Smith E.1.1--5, E.1.8, E.1.10 and E.1.14(7),
printed pp.209--214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace OuterReselection

private theorem inverse_map_eq {G : Type*} [Group G] (e : G ≃* G)
    (K H : Subgroup G) (h : K.map (e : G →* G) = H) :
    H.map (e.symm : G →* G) = K :=
  (map_symm_eq_iff_map_eq (K := K) (H := H) (e := e)).mpr h

/-- Sylow conjugacy also transports the prescribed inner central involution
into the fixed coordinates, by the proved uniqueness there. -/
theorem exists_conjugate_standard_pair (T : Sylow 2 Model) (z : Model)
    (hz : orderOf z = 2) (hzi : z ∈ FiveSourceAudit.inner)
    (hTz : (T : Subgroup Model) ≤ centralizer ({z} : Set Model)) :
    ∃ g : Model, (T : Subgroup Model).map (MulAut.conj g).toMonoidHom =
      (standardSylow : Subgroup Model) ∧ MulAut.conj g z = centralElement := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T standardSylow
  let e := MulAut.conj g
  have hTS : (T : Subgroup Model).map (e : Model →* Model) =
      (standardSylow : Subgroup Model) :=
    congrArg (fun P : Sylow 2 Model => (P : Subgroup Model)) hg
  have hSz : (standardSylow : Subgroup Model) ≤ centralizer ({e z} : Set Model) := by
    rw [← hTS, ← map_elementCentralizer e z]
    exact map_mono hTz
  let _ : FiveSourceAudit.inner.Normal :=
    inferInstanceAs (Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure.innerPart (ZMod 5)).Normal
  have hzi' : e z ∈ FiveSourceAudit.inner :=
    Subgroup.Normal.conj_mem inferInstance z hzi g
  have hez : e z = centralElement := centralElement_unique _
    ((e.orderOf_eq z).trans hz) hzi' hSz
  exact ⟨g, hTS, hez⟩

private theorem conjugation_composition {G : Type*} [Group G]
    (A : Subgroup G) (g u : G) :
    A.map (MulAut.conj (g⁻¹ * u * g)).toMonoidHom =
      ((A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj u).toMonoidHom).map
        ((MulAut.conj g).symm : G →* G) := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem return_conjugate (T : Sylow 2 Model) (z : Model)
    (A : Subgroup Model) (g u : Model)
    (hTS : (T : Subgroup Model).map (MulAut.conj g).toMonoidHom =
      (standardSylow : Subgroup Model))
    (hez : MulAut.conj g z = centralElement)
    (hu : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj u).toMonoidHom = representative)
    (hposition : QuotientActor (centralizerResidualOvergroup standardSylow centralElement) representative) :
    ∃ v : Model, A.map (MulAut.conj v).toMonoidHom ≤ (T : Subgroup Model) ∧
      QuotientActor (centralizerResidualOvergroup T z) (A.map (MulAut.conj v).toMonoidHom) := by
  let e := MulAut.conj g
  have hs : T.mapSurjective (f := (e : Model →* Model)) e.surjective = standardSylow :=
    Sylow.ext hTS
  have hSback : (standardSylow : Subgroup Model).map (e.symm : Model →* Model) =
      (T : Subgroup Model) := by
    exact inverse_map_eq e (T : Subgroup Model) (standardSylow : Subgroup Model) hTS
  have hK : (centralizerResidualOvergroup T z).map (e : Model →* Model) =
      centralizerResidualOvergroup standardSylow centralElement := by
    exact (map_residualOvergroup e T z).trans (congrArg₂ centralizerResidualOvergroup hs hez)
  have hKback : (centralizerResidualOvergroup standardSylow centralElement).map
      (e.symm : Model →* Model) = centralizerResidualOvergroup T z := by
    exact inverse_map_eq e (centralizerResidualOvergroup T z)
      (centralizerResidualOvergroup standardSylow centralElement) hK
  have hrep : A.map (MulAut.conj (g⁻¹ * u * g)).toMonoidHom =
      representative.map (e.symm : Model →* Model) := by
    calc
      _ = ((A.map (e : Model →* Model)).map (MulAut.conj u).toMonoidHom).map
          (e.symm : Model →* Model) := conjugation_composition A g u
      _ = _ := congrArg (Subgroup.map (e.symm : Model →* Model)) hu
  refine ⟨g⁻¹ * u * g, ?_, ?_⟩
  · rw [hrep]
    exact hSback ▸ map_mono representative_le_standardSylow
  · rw [hrep]
    have hq := QuotientActor.map e.symm hposition
    rwa [hKback] at hq

/-- Fixed-coordinate fusion and position suffice for every original Sylow,
inner central involution and full elementary eight-actor. -/
theorem modelReselection_of_standard_calculations
    (hfuse : StandardFusion) (hposition : StandardPosition) : ModelReselection := by
  classical
  intro T z hz hzi hTz hmodel A hA hAT hcard hnot
  let _ := hA
  obtain ⟨g, hTS, hez⟩ := exists_conjugate_standard_pair T z hz hzi hTz
  let e := MulAut.conj g
  change (T : Subgroup Model).map (e : Model →* Model) = _ at hTS
  change e z = centralElement at hez
  have hs : T.mapSurjective (f := (e : Model →* Model)) e.surjective = standardSylow :=
    Sylow.ext hTS
  have hm := residualQuotientModel_map e T z hmodel
  rw [hs, hez] at hm
  have hA' : IsElementaryAbelian 2 (A.map (e : Model →* Model)) := IsElementaryAbelian.map _
  have hAS : A.map (e : Model →* Model) ≤ (standardSylow : Subgroup Model) := hTS ▸ map_mono hAT
  have hc : Nat.card (A.map (e : Model →* Model)) = 8 := by
    rw [card_map_of_injective e.injective, hcard]
  have hf : A.map (e : Model →* Model) ∉ family := by
    intro ha
    apply hnot
    have hb := family_elementary.2 g⁻¹ _ ha
    have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (e : Model →* Model) = MonoidHom.id Model := by
      ext x
      simp [e, MulAut.conj_apply, mul_assoc]
    simpa only [map_map, hi, map_id] using hb
  obtain ⟨u, hu⟩ := (hfuse _ hA' hAS hc).resolve_left hf
  exact return_conjugate T z A g u hTS hez hu (hposition hm)

/-- The actual arbitrary-family consumer, with the independent monomial
join explicit and both outstanding finite calculations visible. -/
theorem unmarked_model_of_standard_calculations (hjoin : MonomialJoin)
    (hfuse : StandardFusion) (hposition : StandardPosition)
    (T : Sylow 2 Model) (Ω : Set (Subgroup Model)) (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup Model) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup Model) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup Model))
    (hcard : Nat.card A = 8) (z : Model) (hz : orderOf z = 2)
    (hzi : z ∈ FiveSourceAudit.inner)
    (hTz : (T : Subgroup Model) ≤ centralizer ({z} : Set Model))
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    UnmarkedFiveGeometryAt (ZMod 5) T Ω z :=
  unmarked_model_of_calculations hjoin T Ω hΩ hEight A hA hAT hcard z
    (modelReselection_of_standard_calculations hfuse hposition T z hz hzi hTz hmodel)

/-- Every full elementary eight-actor outside the first orbit has an actual
ambient conjugate in its original Sylow whose literal radical-quotient image
is a four-group outside the derived subgroup. The only model premise is the
S₅ quotient identification already present in `ModelReselection`. -/
theorem modelReselection : ModelReselection :=
  modelReselection_of_standard_calculations standardFusion standardPosition

/-- Apply the proved reselection theorem to an arbitrary invariant eight-only
family. The independent monomial join and quotient-model inputs remain explicit
for the source-theorem assembly; no fusion or actor-position premise remains. -/
theorem unmarked_model (hjoin : MonomialJoin)
    (T : Sylow 2 Model) (Ω : Set (Subgroup Model)) (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup Model) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup Model) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup Model))
    (hcard : Nat.card A = 8) (z : Model) (hz : orderOf z = 2)
    (hzi : z ∈ FiveSourceAudit.inner)
    (hTz : (T : Subgroup Model) ≤ centralizer ({z} : Set Model))
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    UnmarkedFiveGeometryAt (ZMod 5) T Ω z :=
  unmarked_model_of_calculations hjoin T Ω hΩ hEight A hA hAT hcard z
    (modelReselection T z hz hzi hTz hmodel)

end OuterReselection
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
