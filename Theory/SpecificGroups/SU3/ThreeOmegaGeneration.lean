module
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.RankOneInvariantKernelOmega
/-!
# Three conjugate omega-centers in binary unitary groups

The existing three-center generation of SU₃(2ⁿ), n ≥ 2, uses full Sylow
centers. Hermitian root coordinates make these centers elementary, hence
equal to their first omega subgroups. The literal scalar projection restricts
to a Sylow isomorphism, so mapping the three generators proves the projective
version as well. Both the arbitrary Hermitian form and the possible scalar
center are retained. No generation assertion is made for n = 1.

The DGS Chapter 11 consumer lifts these exact omega-centers to neighboring
source centers and bounds the whole beta core by three neighboring indices.
Source: DGS85, Groups and Graphs (1985), (5.4) and (11.8), printed pp.106,176;
Hermitian coordinates and three-center generation as cited in ThreeRoots.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Representation.SU3.CubicDegree.InnerActors
namespace BenderSuzuki.MatrixGroups.HermitianForm.ThreeOmegaGeneration
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E]
private theorem special_omega (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    omegaCenterIn (P : Subgroup J.specialSubgroup) = sylowCenter P ∧
    omegaOneAmbient (P : Subgroup J.specialSubgroup) = sylowCenter P := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hcard hf
  have hw := SylowOmega.omega_of_special_equiv (standardForm J) hn hcard hf rfl
    (specialEquiv J C hC) P
  have he : omegaOneAmbient (P : Subgroup J.specialSubgroup) = sylowCenter P := hw.1
  let : IsElementaryAbelian 2 ((center (P : Subgroup J.specialSubgroup)).map
      (P : Subgroup J.specialSubgroup).subtype) := by
    change IsElementaryAbelian 2 (sylowCenter P)
    exact he ▸ hw.2.1
  exact ⟨(omegaCenterIn_eq_omegaOneAmbient _).trans (omegaOneAmbient_eq_self _),he⟩

/-- Three conjugate Sylow omega-centers generate the full special unitary group. -/
theorem special (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    ∃ c : Fin 3 → J.specialSubgroup,
      (⨆ i, (omegaCenterIn (P : Subgroup J.specialSubgroup)).map
        (MulAut.conj (c i)).toMonoidHom) = ⊤ := by
  rw [(special_omega J hn hcard hconj P).1]
  exact ThreeRoots.generation J hn hcard hconj P

private theorem projection_omega (J : HermitianForm 3 E)
    (P : Sylow 2 J.specialSubgroup) :
    (omegaCenterIn (P : Subgroup J.specialSubgroup)).map J.specialToProjective =
      omegaCenterIn (P.mapSurjective J.specialToProjective_surjective :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let Q := P.mapSurjective J.specialToProjective_surjective
  let e := SylowOmega.specialSylowEquivProjective J P
  have he : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype.comp e.toMonoidHom =
      J.specialToProjective.comp (P : Subgroup J.specialSubgroup).subtype := by
    apply MonoidHom.ext
    intro x
    exact SylowOmega.specialSylowEquivProjective_apply J P x
  have htop : (⊤ : Subgroup P).map e.toMonoidHom = ⊤ := map_top_of_surjective _ e.surjective
  have hw := NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective (⊤ : Subgroup P)
  have hm := congrArg (map (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype) hw
  rw [htop] at hm
  rw [map_map,he,←map_map] at hm
  rw [NilesRankOneKernel.omegaCenterIn_map_injective (P : Subgroup J.specialSubgroup).subtype (P : Subgroup J.specialSubgroup).subtype_injective,
    NilesRankOneKernel.omegaCenterIn_map_injective (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype_injective,
    ←MonoidHom.range_eq_map,range_subtype,←MonoidHom.range_eq_map,range_subtype] at hm
  exact hm

/-- The same generation under the literal scalar projection to the projective group. -/
theorem projective (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ c : Fin 3 → ProjectiveSpecialUnitaryMatrixGroup J,
      (⨆ i, (omegaCenterIn (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
        (MulAut.conj (c i)).toMonoidHom) = ⊤ := by
  obtain ⟨R,rfl⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 P
  obtain ⟨c,hc⟩ := special J hn hcard hconj R
  refine ⟨fun i => J.specialToProjective (c i),?_⟩
  have hm := congrArg (map J.specialToProjective) hc
  simpa only [Subgroup.map_iSup,ThreeRoots.map_conjugate,projection_omega,
    map_top_of_surjective _ J.specialToProjective_surjective] using hm
/-- An actual group isomorphism transports the three literal omega-center generators. -/
theorem of_equiv {H K : Type*} [Group H] [Group K] [Finite H]
    (e : H ≃* K)
    (hK : ∀ P : Sylow 2 K, ∃ c : Fin 3 → K,
      (⨆ i, (omegaCenterIn (P : Subgroup K)).map (MulAut.conj (c i)).toMonoidHom) = ⊤)
    (P : Sylow 2 H) :
    ∃ c : Fin 3 → H,
      (⨆ i, (omegaCenterIn (P : Subgroup H)).map (MulAut.conj (c i)).toMonoidHom) = ⊤ := by
  obtain ⟨c,hc⟩ := hK (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change (⨆ i, (omegaCenterIn ((P : Subgroup H).map e.toMonoidHom)).map
    (MulAut.conj (c i)).toMonoidHom) = ⊤ at hc
  refine ⟨fun i => e.symm (c i),?_⟩
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_iSup,map_top_of_surjective _ e.surjective]
  simpa only [ThreeRoots.map_conjugate,
    NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
    MulEquiv.coe_toMonoidHom,e.apply_symm_apply,Sylow.coe_mapSurjective] using hc

end BenderSuzuki.MatrixGroups.HermitianForm.ThreeOmegaGeneration
