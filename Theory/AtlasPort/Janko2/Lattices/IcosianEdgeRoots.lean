/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianEdgeRoots.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianEdgePairs

/-!
# Icosian Edge Roots

Edge roots have one zero coordinate and two norm-two coordinates with
equal reduction. Permuting the zero coordinate and reconstructing the
pair yields an injective parametrization and the count 2880.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianEdgeRoots.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix Quaternion QuadraticAlgebra BigOperators

def icosianEdgeRootBase (p : IcosianEdgePair) : IcosianRoot :=
  ⟨![0,p.val.1.val,p.val.2.val],by
    constructor
    · rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
      intro j
      have hp := p.property.2 j
      have he := congrFun (congrFun p.property.1 1) j
      have hf := congrFun (congrFun p.property.1 0) j
      change icosianModuloTwo (0 : icosianOrder) 1 j=icosianModuloTwo p.val.1.val 1 j ∧
        icosianModuloTwo p.val.1.val 1 j=icosianModuloTwo p.val.2.val 1 j ∧
        icosianModuloTwo (0 : icosianOrder) 0 j+icosianModuloTwo p.val.1.val 0 j+icosianModuloTwo p.val.2.val 0 j=0
      rw [map_zero]
      refine ⟨hp.symm,he,?_⟩
      rw [hf]
      ext <;> simp [CharTwo.add_self_eq_zero]
    · change icosianHermitian (icosianCoordinateEmbedding ![0,p.val.1.val,p.val.2.val])
        (icosianCoordinateEmbedding ![0,p.val.1.val,p.val.2.val])=2
      have h1 : Quaternion.normSq p.val.1.val.val=(2 : GoldenRational) := p.val.1.property
      have h2 : Quaternion.normSq p.val.2.val.val=(2 : GoldenRational) := p.val.2.property
      simp [icosianHermitian,icosianCoordinateEmbedding,Fin.sum_univ_succ,
        Quaternion.star_mul_self,h1,h2]
      ext <;> norm_num [QuaternionAlgebra.re_ofNat,QuaternionAlgebra.imI_ofNat,
        QuaternionAlgebra.imJ_ofNat,QuaternionAlgebra.imK_ofNat]⟩

theorem icosianEdgeRootBase_zero (p : IcosianEdgePair) : (icosianEdgeRootBase p).val 0=0 := rfl

theorem icosianEdgeRootBase_norm (p : IcosianEdgePair) (j : Fin 3) (hj : j≠0) :
    icosianNorm ((icosianEdgeRootBase p).val j).val=2 := by
  fin_cases j
  · exact (hj rfl).elim
  · exact p.val.1.property
  · exact p.val.2.property

def icosianEdgeRootParameter (p : Fin 3 × IcosianEdgePair) : IcosianRoot :=
  icosianRootPermute (Equiv.swap 0 p.1) (icosianEdgeRootBase p.2)

theorem icosianEdgeRootParameter_zero (p : Fin 3 × IcosianEdgePair) :
    (icosianEdgeRootParameter p).val p.1=0 := by
  simp [icosianEdgeRootParameter,Equiv.swap_apply_right,icosianEdgeRootBase_zero]

theorem icosianEdgeRootParameter_norm (p : Fin 3 × IcosianEdgePair) (j : Fin 3) (hj : j≠p.1) :
    icosianNorm ((icosianEdgeRootParameter p).val j).val=2 := by
  apply icosianEdgeRootBase_norm
  intro he
  apply hj
  have hh := congrArg (Equiv.swap 0 p.1) he
  simpa using hh

theorem icosianEdgeRootParameter_injective : Function.Injective icosianEdgeRootParameter := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  have hij : i=j := by
    by_contra hn
    have hn2 := icosianEdgeRootParameter_norm (j,q) i hn
    have hz := icosianEdgeRootParameter_zero (i,p)
    rw [h] at hz
    rw [hz] at hn2
    have hr := congrArg QuadraticAlgebra.re hn2
    norm_num [icosianNorm_coordinates] at hr
  subst j
  have hb : icosianEdgeRootBase p=icosianEdgeRootBase q :=
    (icosianRootPermute (Equiv.swap 0 i)).injective h
  have h1 := congrArg (fun r : IcosianRoot => r.val 1) hb
  have h2 := congrArg (fun r : IcosianRoot => r.val 2) hb
  have hp : p=q := by
    apply Subtype.ext
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  exact congrArg (fun z => (i,z)) hp

/-- The actual root family obtained from one zero block and two equal
rank-one reductions of norm-two icosians. -/
def IcosianEdgeRoot := {r : IcosianRoot // r∈Set.range icosianEdgeRootParameter}

def icosianEdgeRootEquiv : (Fin 3 × IcosianEdgePair) ≃ IcosianEdgeRoot :=
  Equiv.ofInjective icosianEdgeRootParameter icosianEdgeRootParameter_injective

theorem icosianEdgeRoots_card : Nat.card IcosianEdgeRoot=2880 := by
  rw [← Nat.card_congr icosianEdgeRootEquiv,Nat.card_prod,icosianEdgePairs_card]
  norm_num

theorem icosianEdgeRootBase_reconstruct (r : IcosianRoot) (hz : r.val 0=0)
    (h1 : icosianNorm (r.val 1).val=2) (h2 : icosianNorm (r.val 2).val=2) :
    ∃ p : IcosianEdgePair,icosianEdgeRootBase p=r := by
  have hp : r.val 1∈icosianP := icosianLeechModule_zero_row r.val r.property.1 0 hz 1
  have hm : icosianModuloTwo (r.val 1)=icosianModuloTwo (r.val 2) := by
    funext a j
    fin_cases a
    · have hs := ((icosianMatrixGlue_constraints _).mp
        ((icosianLeechModule_matrix_glue r.val).mp r.property.1) j).2.2
      rw [hz,map_zero] at hs
      have hs2 : icosianModuloTwo (r.val 1) 0 j+icosianModuloTwo (r.val 2) 0 j=0 := by simpa using hs
      have he := eq_neg_of_add_eq_zero_left hs2
      have hn : -icosianModuloTwo (r.val 2) 0 j=icosianModuloTwo (r.val 2) 0 j := by
        ext <;> simp [CharTwo.neg_eq]
      exact he.trans hn
    · change icosianModuloTwo (r.val 1) 1 j=icosianModuloTwo (r.val 2) 1 j
      rw [icosianLeechModule_zero_row r.val r.property.1 0 hz 1 j,
        icosianLeechModule_zero_row r.val r.property.1 0 hz 2 j]
  let p : IcosianEdgePair := ⟨(⟨r.val 1,h1⟩,⟨r.val 2,h2⟩),hm,hp⟩
  refine ⟨p,?_⟩
  apply Subtype.ext
  funext j
  fin_cases j
  · exact hz.symm
  · rfl
  · rfl

theorem icosianEdgeRoot_recognition (r : IcosianRoot) (i : Fin 3)
    (hz : r.val i=0) (hn : ∀ j,j≠i → icosianNorm (r.val j).val=2) :
    r∈Set.range icosianEdgeRootParameter := by
  let rr := icosianRootPermute (Equiv.swap 0 i) r
  have hzero : rr.val 0=0 := by simpa [rr] using hz
  have hother (k : Fin 3) (hk : k≠0) : icosianNorm (rr.val k).val=2 := by
    apply hn
    intro h
    have hh := congrArg (Equiv.swap 0 i) h
    apply hk
    simpa using hh
  obtain ⟨p,hp⟩ := icosianEdgeRootBase_reconstruct rr hzero
    (hother 1 (by decide)) (hother 2 (by decide))
  refine ⟨(i,p),?_⟩
  apply Subtype.ext
  funext j
  simp [icosianEdgeRootParameter,hp,rr,icosianRootPermute,icosianPermute]

end Atlas.Lattices
