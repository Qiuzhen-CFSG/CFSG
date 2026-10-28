module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/IwasawaLocal.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.LocalNormalizer
public import Mathlib.GroupTheory.GroupAction.Iwasawa

/-! Transport the long-root local subgroup over singular points to construct an Iwasawa structure. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open scoped Pointwise
variable {K : Type*} [Field K]

def pointTransport (p : SingularPoints K) : Model K :=
  (MulAction.exists_smul_eq (Model K) firstPoint p).choose

theorem pointTransport_action (p : SingularPoints K) : pointTransport p • firstPoint = p :=
  (MulAction.exists_smul_eq (Model K) firstPoint p).choose_spec

def localAt (p : SingularPoints K) : Subgroup (Model K) :=
  MulAut.conj (pointTransport p) • longRootLocal

theorem conjugate_local_eq {g h : Model K}
    (he : g • firstPoint = h • firstPoint (K := K)) :
    MulAut.conj g • longRootLocal (F := K) = MulAut.conj h • longRootLocal := by
  have hk : h⁻¹*g ∈ pointStabilizer := by
    change (h⁻¹*g) • firstPoint = firstPoint
    rw [mul_smul,he,inv_smul_smul]
  have hn := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (pointStabilizer_le_longRootNormalizer hk)
  have hn' : MulAut.conj (h⁻¹*g) • longRootLocal (F := K) = longRootLocal := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (pointStabilizer_le_longRootNormalizer hk) a).mp ha
    · intro hx
      refine ⟨(h⁻¹*g)⁻¹*x*(h⁻¹*g),?_,?_⟩
      · exact (Subgroup.mem_normalizer_iff''.mp (pointStabilizer_le_longRootNormalizer hk) x).mp hx
      · change (h⁻¹*g)*((h⁻¹*g)⁻¹*x*(h⁻¹*g))*(h⁻¹*g)⁻¹=x
        group
  have heq : g = h*(h⁻¹*g) := by group
  rw [heq,map_mul,mul_smul,hn']

theorem localAt_eq_of_transport (p : SingularPoints K) (g : Model K)
    (hg : g • firstPoint = p) : localAt p = MulAut.conj g • longRootLocal :=
  conjugate_local_eq ((pointTransport_action p).trans hg.symm)

theorem localAt_first : localAt (firstPoint (K := K)) = longRootLocal := by
  rw [localAt_eq_of_transport firstPoint 1 (one_smul _ _)]
  simp

theorem localAt_conj (g : Model K) (p : SingularPoints K) :
    localAt (g • p) = MulAut.conj g • localAt p := by
  rw [localAt_eq_of_transport (g • p) (g*pointTransport p)
    (by rw [mul_smul,pointTransport_action]),map_mul,mul_smul]
  rfl

theorem localAt_commutative (p : SingularPoints K) : IsMulCommutative (localAt p) := by
  change IsMulCommutative (longRootLocal.map (MulAut.conj (pointTransport p)).toMonoidHom)
  infer_instance

def localAtEquiv (p : SingularPoints K) : longRootLocal (F := K) ≃* localAt p :=
  longRootLocal.equivMapOfInjective (MulAut.conj (pointTransport p)).toMonoidHom
    (MulAut.conj (pointTransport p)).injective

theorem card_localAt [Finite K] (p : SingularPoints K) : Nat.card (localAt p) = Nat.card K^2 := by
  rw [← Nat.card_congr (localAtEquiv p).toEquiv,card_longRootLocal]

theorem localAt_iSup_eq_normalClosure : (⨆ p : SingularPoints K,localAt p) = longRootNormalClosure := by
  apply le_antisymm
  · apply iSup_le
    intro p
    rintro x ⟨a,ha,rfl⟩
    exact (inferInstance : longRootNormalClosure.Normal).conj_mem a
      (Subgroup.subset_normalClosure ha) (pointTransport p)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    apply (le_iSup localAt (g • firstPoint))
    rw [localAt_eq_of_transport (g • firstPoint) g rfl]
    exact ⟨a,ha,rfl⟩

def iwasawa [Finite K] (hq : 2 < Nat.card K) :
    MulAction.IwasawaStructure (Model K) (SingularPoints K) where
  T := localAt
  is_comm := localAt_commutative
  is_conj := localAt_conj
  is_generator := localAt_iSup_eq_normalClosure.trans (longRootNormalClosure_eq_top hq)

end Atlas.G2
