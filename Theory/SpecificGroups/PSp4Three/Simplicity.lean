module

public import Theory.SpecificGroups.PSp4Three.Primitivity
public import Theory.SpecificGroups.PSp4Three.Perfectness
public import Mathlib.GroupTheory.GroupAction.Iwasawa

/-!
# Simplicity of the concrete PSp₄(3)

The faithful primitive action on projective points has an equivariant generating
family of abelian transvection subgroups. Ternary perfectness and Iwasawa’s
criterion imply simplicity of the actual central quotient.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/LinearGroups/Symplectic/Nontrivial.lean`, `Atlas/LinearGroups/Symplectic/LineTransvections.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

/-- Every nonidentity transvection has a nonidentity image in the actual central quotient. -/
theorem projection_transvection_ne_one {v : Vector n F} (hv : v ≠ 0) {a : F} (ha : a ≠ 0) :
    projection (transvection v a) ≠ 1 := by
  intro h
  have hc : transvection v a ∈ Subgroup.center (Sp n F) := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨c,hc⟩ := central_is_scalar _ hc
  have hcv : c • v = (1 : F) • v := by
    simpa [transvection_apply] using (hc v).symm
  have hc1 := smul_left_injective F hv hcv
  have ht : transvection v a = 1 := by
    apply ext_action
    intro x
    rw [hc,hc1,one_smul,one_smul]
  exact transvection_ne_one hv ha ht

theorem projective_nontrivial (hn : 0 < n) : Nontrivial (PSp n F) := by
  let i : Fin n := ⟨0,hn⟩
  have he : e (F := F) i ≠ 0 := by
    intro h
    have := congrFun h (.inl i)
    simp [e] at this
  exact ⟨⟨projection (transvection (e i) 1),1,projection_transvection_ne_one he one_ne_zero⟩⟩

end Matrix.PSp4Three
end

noncomputable section
open scoped Pointwise LinearAlgebra.Projectivization
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

def parameterHom (v : Vector n F) : Multiplicative F →* Sp n F where
  toFun a := transvection v a.toAdd
  map_one' := transvection_zero v
  map_mul' a b := transvection_add v a.toAdd b.toAdd

def directionGroup (v : Vector n F) : Subgroup (PSp n F) :=
  (projection.comp (parameterHom v)).range

theorem mem_directionGroup (v : Vector n F) (g : PSp n F) :
    g ∈ directionGroup v ↔ ∃ a : F, projection (transvection v a) = g := Iff.rfl

theorem directionGroup_scale (v : Vector n F) (c : F) (hc : c ≠ 0) :
    directionGroup (c • v) = directionGroup v := by
  ext g
  rw [mem_directionGroup,mem_directionGroup]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨c^2*a,by rw [transvection_scale]⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a/c^2,?_⟩
    rw [transvection_scale,mul_div_cancel₀ a (pow_ne_zero _ hc)]

theorem directionGroup_conj (g : Sp n F) (v : Vector n F) :
    directionGroup (g • v) = MulAut.conj (projection g) • directionGroup v := by
  ext t
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨projection (transvection v a.toAdd),⟨a,rfl⟩,?_⟩
    change projection g * projection (transvection v a.toAdd) * (projection g)⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,transvection_conjugate]
    rfl
  · rintro ⟨t,⟨a,rfl⟩,rfl⟩
    refine ⟨a,?_⟩
    change projection (transvection (g • v) a.toAdd) =
      projection g * projection (transvection v a.toAdd) * (projection g)⁻¹
    rw [← map_inv,← map_mul,← map_mul,transvection_conjugate]

/-- Actual projective transvections with a fixed direction line. -/
def lineTransvections (p : Points n F) : Subgroup (PSp n F) := directionGroup p.rep

theorem lineTransvections_abelian (p : Points n F) : IsMulCommutative (lineTransvections p) :=
  Subgroup.range_isMulCommutative _

theorem lineTransvections_mk {v : Vector n F} (hv : v ≠ 0) :
    lineTransvections (Projectivization.mk F v hv) = directionGroup v := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  unfold lineTransvections
  rw [← ha,Units.smul_def,directionGroup_scale v a.val a.ne_zero]

theorem lineTransvections_conj (g : PSp n F) (p : Points n F) :
    lineTransvections (g • p) = MulAut.conj g • lineTransvections p := by
  obtain ⟨g,rfl⟩ := projection_surjective g
  rw [projection_smul,← Projectivization.mk_rep p,Projectivization.smul_mk,
    lineTransvections_mk,directionGroup_conj,lineTransvections_mk]

theorem lineTransvections_generate : (⨆ p : Points n F,lineTransvections p) = ⊤ := by
  apply top_unique
  rw [← projectiveTransvectionGroup_eq_top (n := n) (F := F)]
  apply (Subgroup.closure_le _).mpr
  rintro t ⟨v,a,rfl⟩
  by_cases hv : v=0
  · subst v
    simp
  · have hmem : projection (transvection v a) ∈ lineTransvections (Projectivization.mk F v hv) := by
      rw [lineTransvections_mk,mem_directionGroup]
      exact ⟨a,rfl⟩
    exact (le_iSup lineTransvections (Projectivization.mk F v hv)) hmem

def iwasawa : MulAction.IwasawaStructure (PSp n F) (Points n F) where
  T := lineTransvections
  is_comm := lineTransvections_abelian
  is_conj := lineTransvections_conj
  is_generator := lineTransvections_generate

end Matrix.PSp4Three
end

namespace Matrix.PSp4Three

/-- Simplicity of the actual matrix symplectic group modulo its center. -/
theorem isSimpleGroup : IsSimpleGroup (PSp 2 (ZMod 3)) := by
  let := projective_preprimitive_three
  let := projective_nontrivial (F := ZMod 3) (n := 2) (by decide)
  let := perfect_of_card_three (n := 2) (by decide)
  let : Group.IsPerfect (PSp 2 (ZMod 3)) := inferInstance
  exact iwasawa.isSimpleGroup (Group.IsPerfect.commutator_eq_top (G := PSp 2 (ZMod 3)))
    inferInstance

end Matrix.PSp4Three
