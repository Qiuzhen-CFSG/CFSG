/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianAxisRoots.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRoots

/-!
# Icosian Axis Roots

Axis roots are parametrized bijectively by three coordinate axes and the
120 norm-one icosians. Dividing the sole nonzero coordinate by two
constructs the inverse and gives the count 360.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianAxisRoots.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

def icosianUnitIntegral (u : icosianNormOneGroup) : icosianOrder := ⟨u.val.val,u.property⟩

def icosianAxisRoot (p : Fin 3 × icosianNormOneGroup) : IcosianRoot :=
  ⟨icosianSingle p.1 (2*icosianUnitIntegral p.2),by
    constructor
    · apply (icosianSingle_mem _ _).mpr
      exact (icosianModuloTwo_eq_zero_iff_two_mul _).mpr ⟨icosianUnitIntegral p.2,rfl⟩
    · rw [icosianSingle_norm]
      change (1/2 : ℚ) • (icosianNorm (2*p.2.val.val) : IcosianQuaternion)=2
      rw [icosianNorm_double,icosianNormOneGroup_norm]
      ext <;> norm_num [QuaternionAlgebra.re_ofNat,QuaternionAlgebra.imI_ofNat,QuaternionAlgebra.imJ_ofNat,QuaternionAlgebra.imK_ofNat]⟩

def IsIcosianAxisRoot (r : IcosianRoot) : Prop := ∃ i,∀ j,j≠i → r.val j=0

def IcosianAxisRoot := {r : IcosianRoot // IsIcosianAxisRoot r}

theorem icosianAxisRoot_axis (p : Fin 3 × icosianNormOneGroup) :
    IsIcosianAxisRoot (icosianAxisRoot p) := by
  exact ⟨p.1,fun j hj => by simp [icosianAxisRoot,icosianSingle,hj]⟩

theorem icosianAxisRoot_nonzero (p : Fin 3 × icosianNormOneGroup) :
    (icosianAxisRoot p).val p.1≠0 := by
  intro h
  have hn := icosianRoot_single_norm (icosianAxisRoot p) p.1
    (fun j hj => by simp [icosianAxisRoot,icosianSingle,hj])
  rw [h] at hn
  have hr := congrArg QuadraticAlgebra.re hn
  norm_num [icosianNorm_coordinates] at hr

theorem icosianAxisRoot_injective : Function.Injective icosianAxisRoot := by
  rintro ⟨i,u⟩ ⟨j,v⟩ h
  have hij : i=j := by
    by_contra hn
    have he := congrArg (fun r : IcosianRoot => r.val i) h
    have hz : (icosianAxisRoot (j,v)).val i=0 := by
      simp [icosianAxisRoot,icosianSingle,hn]
    exact icosianAxisRoot_nonzero (i,u) (he.trans hz)
  subst j
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun r : IcosianRoot => (r.val i).val) h
  simp only [icosianAxisRoot,icosianSingle,ite_true] at he
  change (2 : IcosianQuaternion)*u.val.val=(2 : IcosianQuaternion)*v.val.val at he
  rw [two_mul,two_mul] at he
  have hcoords := congrArg (fun z : IcosianQuaternion => (1/2 : ℚ) • z) he
  simpa [smul_add,← add_smul] using hcoords

theorem icosianAxisRoot_surjective : ∀ r : IcosianAxisRoot,
    ∃ p : Fin 3 × icosianNormOneGroup,icosianAxisRoot p=r.val := by
  intro r
  obtain ⟨i,hi⟩ := r.property
  have he : r.val.val=icosianSingle i (r.val.val i) := by
    funext j
    by_cases hj : j=i
    · simp [icosianSingle,hj]
    · simp [icosianSingle,hj,hi j hj]
  have hm := r.val.property.1
  rw [he,icosianSingle_mem] at hm
  obtain ⟨y,hy⟩ := (icosianModuloTwo_eq_zero_iff_two_mul _).mp hm
  have hn := icosianRoot_single_norm r.val i hi
  rw [hy] at hn
  change icosianNorm (2*y.val)=4 at hn
  rw [icosianNorm_double] at hn
  have hy1 : icosianNorm y.val=1 := by
    have h4 : (4 : GoldenRational)≠0 := by
      intro h
      have hr := congrArg QuadraticAlgebra.re h
      norm_num at hr
    apply mul_left_cancel₀ h4
    simpa using hn
  let u := icosianNormOneGroupOf y.val y.property hy1
  refine ⟨(i,u),?_⟩
  apply Subtype.ext
  change icosianSingle i (2*icosianUnitIntegral u)=r.val.val
  rw [he,hy]
  rfl

def icosianAxisRootEquiv : (Fin 3 × icosianNormOneGroup) ≃ IcosianAxisRoot :=
  Equiv.ofBijective (fun p => ⟨icosianAxisRoot p,icosianAxisRoot_axis p⟩) (by
    constructor
    · intro p q h
      exact icosianAxisRoot_injective (congrArg Subtype.val h)
    · intro r
      obtain ⟨p,hp⟩ := icosianAxisRoot_surjective r
      exact ⟨p,Subtype.ext hp⟩)

theorem icosianAxisRoots_card : Nat.card IcosianAxisRoot=360 := by
  rw [← Nat.card_congr icosianAxisRootEquiv,Nat.card_prod,icosianNormOneGroup_card]
  norm_num

end Atlas.Lattices
