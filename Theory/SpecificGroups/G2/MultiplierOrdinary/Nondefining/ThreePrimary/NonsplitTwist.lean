module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Split
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Split
public import Theory.SpecificGroups.G2.PRegularClasses.GeometricTorus
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang

/-!
# A nonsplit torus twist in the actual even-characteristic G₂ model

The square of the Coxeter Weyl element is a nonidentity element of order
three. Its centralizer is connected, by the proved geometric torus and
centralizer results. Lang's theorem in this centralizer therefore solves
the Frobenius equation for the cube of the Coxeter element. This avoids
requiring a separate connectedness theorem for the entire G₂ variety.

Conjugation by the inverse of this solution descends every compatible
point through the literal field embedding. In particular, both norm-one
torus coordinates are inverted by Frobenius and by the Coxeter cube, so
the entire two-dimensional torus descends into the actual finite-field
split-octonion group. The Sylow normalizer construction remains separate.

Sources: Steinberg 8.5 and 10.7–10.8 in refs/KGroup/GLS3/Chapter2St2.tex;
Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
The coordinate model and Weyl maps are licensed ATLAS ports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Atlas.SplitOctonion
namespace Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
open PRegularClasses PRegularClasses.FieldExtension PRegularClasses.RationalFusion

private theorem embedding_weylR {F K : Type*} [Field F] [Field K]
    (f : F →+* K) : fieldEmbedding f (weylR : Model F) = weylR := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f (weylR : Model F)).val (basisVector j) = _
  rw [fieldEmbedding_basis]
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [coeffMap, weylR, weylREquiv, weylRLinear, weylRApply, basisVector]

private theorem embedding_weylS {F K : Type*} [Field F] [Field K]
    (f : F →+* K) : fieldEmbedding f (weylS : Model F) = weylS := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f (weylS : Model F)).val (basisVector j) = _
  rw [fieldEmbedding_basis]
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [coeffMap, weylS, weylSEquiv, weylSLinear, weylSApply, basisVector]

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local notation "K" => AlgebraicClosure F

private theorem exists_coxeter_twist :
    ∃ u : Model K, u * (frobenius F u)⁻¹ = (weylR * weylS)^3 := by
  let c : Model F := (weylR * weylS)^2
  have hc1 : c ≠ 1 := by
    intro h
    exact OddThreePrimary.cycle_not_mem_torus (h ▸ (show Subgroup (Model F) from splitTorus).one_mem)
  have hc3 : c^3 = 1 := OddThreePrimary.cycle_cube
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have he : fieldEmbedding (algebraMap F K) c = (weylR * weylS)^2 := by
    simp only [c, map_pow, map_mul, embedding_weylR, embedding_weylS]
  obtain ⟨u, _, hu⟩ := CentralizerLang.exists_lang F
    (fun g hg => isConj_torus_of_odd_order g hg) c (by rw [hcord]; decide) hc1
    ((weylR * weylS)^3) (by rw [he]; exact (Commute.refl (weylR * weylS)).pow_pow 3 2)
  exact ⟨u, hu⟩

/-- A Coxeter-inversion twist and descent for every compatible conjugate. -/
public theorem exists_twist_with_descent :
    ∃ u : Model K, u * (frobenius F u)⁻¹ = (weylR * weylS)^3 ∧
      ∀ g : Model K,
        (weylR * weylS)^3 * frobenius F g * ((weylR * weylS)^3)⁻¹ = g →
        ∃ d : Model F,
          fieldEmbedding (algebraMap F K) d = u⁻¹ * g * u := by
  obtain ⟨u, hu⟩ := exists_coxeter_twist F
  refine ⟨u, hu, ?_⟩
  intro g hg
  apply (frobenius_fixed_iff F _).mp
  have hfu : frobenius F u = ((weylR * weylS)^3)⁻¹ * u := by
    rw [← hu]
    group
  rw [map_mul, map_mul, map_inv, hfu]
  calc
    _ = u⁻¹ * ((weylR * weylS)^3 * frobenius F g * ((weylR * weylS)^3)⁻¹) * u := by group
    _ = u⁻¹ * g * u := by rw [hg]

omit [CharP F 2] in
private theorem frobenius_torus (l m : Kˣ) :
    frobenius F (torus l m) = torus (l ^ Nat.card F) (m ^ Nat.card F) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (frobenius F (torus l m)).val (basisVector j) = _
  ext i
  rw [← coordinateMatrix_entry, frobenius_entry]
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix_entry, torus, torusEquiv, torusLinear, torusWeights,
      basisVector, mul_pow, Nat.card_pos.ne']

/-- One twist descends every point of the two-dimensional norm-one torus
through the literal field embedding of octonion automorphisms. -/
public theorem exists_nonsplit_torus_descent :
    ∃ u : Model K, u * (frobenius F u)⁻¹ = (weylR * weylS)^3 ∧
      ∀ l m : Kˣ, l ^ (Nat.card F + 1) = 1 → m ^ (Nat.card F + 1) = 1 →
        ∃ d : Model F,
          fieldEmbedding (algebraMap F K) d = u⁻¹ * torus l m * u := by
  obtain ⟨u, hu, hd⟩ := exists_twist_with_descent F
  refine ⟨u, hu, ?_⟩
  intro l m hl hm
  apply hd
  have hlq : l ^ Nat.card F = l⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [pow_succ] using hl)
  have hmq : m ^ Nat.card F = m⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [pow_succ] using hm)
  rw [frobenius_torus, hlq, hmq]
  change OddThreePrimary.inverter * torus l⁻¹ m⁻¹ * OddThreePrimary.inverter⁻¹ = _
  rw [OddThreePrimary.inverter_torus]
  have hi : torus l⁻¹ m⁻¹ = (torus l m : Model K)⁻¹ := by
    exact map_inv torusHom (l,m)
  rw [hi, inv_inv]

end Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
