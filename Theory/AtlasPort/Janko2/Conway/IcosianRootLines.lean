/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootLines.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianQuaternionLines
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootLineScalars
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneCard

/-!
# IcosianRootLines

Integral norm-one right scalars act freely on each root line. Scalar saturation
identifies every fiber with the 120-element unit group.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootLines.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion

theorem icosianRoot_embedding_ne_zero (r : IcosianRoot) :
    icosianCoordinateEmbedding r.val≠0 := by
  intro h
  have hn := r.property.2
  rw [h] at hn
  have hz : icosianHermitian 0 0=0 := by simp [icosianHermitian]
  rw [hz] at hn
  exact (show (0 : IcosianQuaternion)≠2 by intro he; have hh := congrArg (fun z : IcosianQuaternion => z.re.re) he; norm_num [QuaternionAlgebra.re_ofNat, QuadraticAlgebra.re_ofNat] at hh) hn

/-- The actual right quaternionic line through an actual lattice root. -/
def icosianRootPoint (r : IcosianRoot) : IcosianQuaternionPoint :=
  Projectivization.mk _ (icosianCoordinateEmbedding r.val) (icosianRoot_embedding_ne_zero r)

/-- Direct right multiplication, used as coordinates on a root-line fiber. -/
def icosianRootRightUnit (r : IcosianRoot) (u : icosianNormOneGroup) : IcosianRoot := by
  let x : IcosianCoordinates := fun i => r.val i*icosianNormOneToOrder u
  have hx : x∈icosianLeechModule :=
    icosianLeechModule.smul_mem (MulOpposite.op (icosianNormOneToOrder u)) r.property.1
  have he : icosianCoordinateEmbedding x=
      icosianRightMul (icosianCoordinateEmbedding r.val) u.val.val := rfl
  refine ⟨x,hx,?_⟩
  rw [he,icosianHermitian_rightMul_left,icosianHermitian_rightMul_right,r.property.2]
  calc
    star u.val.val*(2*u.val.val)=2*(star u.val.val*u.val.val) := by noncomm_ring
    _=2 := by rw [Unitary.coe_star_mul_self]; simp

theorem icosianRootPoint_rightUnit (r : IcosianRoot) (u : icosianNormOneGroup) :
    icosianRootPoint (icosianRootRightUnit r u)=icosianRootPoint r := by
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  exact ⟨MulOpposite.op u.val.val,rfl⟩

/-- Equality of actual quaternionic root lines is exactly integral unit association. -/
theorem icosianRootPoint_eq_iff (r s : IcosianRoot) :
    icosianRootPoint s=icosianRootPoint r ↔ ∃ u : icosianNormOneGroup,s=icosianRootRightUnit r u := by
  constructor
  · intro hp
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp hp
    have h : ∀ i,(s.val i).val=(r.val i).val*MulOpposite.unop a :=
      fun i => (congrFun ha i).symm
    obtain ⟨u,hu⟩ := icosianRoot_scalar_unit r s (MulOpposite.unop a) h
    refine ⟨u,?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact (h i).trans (congrArg ((r.val i).val*·) hu)
  · rintro ⟨u,rfl⟩
    exact icosianRootPoint_rightUnit r u

/-- Every integral unit gives a distinct root on the fixed quaternionic line. -/
theorem icosianRootRightUnit_injective (r : IcosianRoot) :
    Function.Injective (icosianRootRightUnit r) := by
  intro u v h
  have hn : ∃ i,(r.val i).val≠0 := by
    by_contra! hz
    apply icosianRoot_embedding_ne_zero r
    funext i
    exact hz i
  obtain ⟨i,hi⟩ := hn
  have he := congrArg (fun s : IcosianRoot => (s.val i).val) h
  have hv : u.val.val=v.val.val := mul_left_cancel₀ hi he
  apply Subtype.ext
  apply Subtype.ext
  exact hv

def icosianRootLineFiberEquiv (r : IcosianRoot) :
    icosianNormOneGroup ≃ {s : IcosianRoot // icosianRootPoint s=icosianRootPoint r} :=
  Equiv.ofBijective (fun u => ⟨icosianRootRightUnit r u,icosianRootPoint_rightUnit r u⟩)
    ⟨fun u v h => icosianRootRightUnit_injective r (congrArg Subtype.val h),by
      rintro ⟨s,hs⟩
      obtain ⟨u,hu⟩ := (icosianRootPoint_eq_iff r s).mp hs
      exact ⟨u,Subtype.ext hu.symm⟩⟩

theorem icosianRootLineFiber_card (r : IcosianRoot) :
    Nat.card {s : IcosianRoot // icosianRootPoint s=icosianRootPoint r}=120 := by
  rw [← Nat.card_congr (icosianRootLineFiberEquiv r),icosianNormOneGroup_card]

/-- The finite quaternionic root-line geometry, as actual projective points. -/
def IcosianRootPoint := {p : IcosianQuaternionPoint // ∃ r : IcosianRoot,icosianRootPoint r=p}

end Atlas.Conway
