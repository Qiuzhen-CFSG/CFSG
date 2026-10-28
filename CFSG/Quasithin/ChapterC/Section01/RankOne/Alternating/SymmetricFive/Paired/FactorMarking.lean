module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.FactorMaximal

/-!
# The same marked paired factors give the local S₄ geometry

The alternating subgroup of either actual symmetric factor is a component.
An exchanger in the prescribed Sylow prevents a whole factor from lying in
the unique maximal overgroup.  The source A₄ Borel argument therefore fixes
its exact S₄ intersection in the original product coordinates.

Source: Aschbacher--Smith C.1.24 and E.2.3(3).
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB ChapterB.Offenders
variable {G : Type*} [Group G] [Finite G]

def leftFactorMap (Y : Subgroup G) (e : Y ≃* Sym × Sym) : Sym →* G :=
  Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl Sym Sym))

def rightFactorMap (Y : Subgroup G) (e : Y ≃* Sym × Sym) : Sym →* G :=
  Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr Sym Sym))

omit [Finite G] in
theorem leftFactorMap_range (Y : Subgroup G) (e : Y ≃* Sym × Sym) :
    (leftFactorMap Y e).range = ((⊤ : Subgroup Sym).prod ⊥).map
      (Y.subtype.comp e.symm.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(a,1),⟨mem_top _,one_mem _⟩,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨a.1,?_⟩
    change (Y.subtype.comp e.symm.toMonoidHom) (a.1,1) = (Y.subtype.comp e.symm.toMonoidHom) a
    exact congrArg _ (Prod.ext rfl ha.2.symm)

omit [Finite G] in
theorem rightFactorMap_range (Y : Subgroup G) (e : Y ≃* Sym × Sym) :
    (rightFactorMap Y e).range = ((⊥ : Subgroup Sym).prod ⊤).map
      (Y.subtype.comp e.symm.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(1,a),⟨one_mem _,mem_top _⟩,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨a.2,?_⟩
    change (Y.subtype.comp e.symm.toMonoidHom) (1,a.2) = (Y.subtype.comp e.symm.toMonoidHom) a
    exact congrArg _ (Prod.ext ha.1.symm rfl)

omit [Finite G] in
theorem leftFactorMap_injective (Y : Subgroup G) (e : Y ≃* Sym × Sym) :
    Function.Injective (leftFactorMap Y e) :=
  Y.subtype_injective.comp (e.symm.injective.comp (fun _ _ h => congrArg Prod.fst h))

private theorem left_alternating_map :
    (alternatingGroup (Fin 5)).map (MonoidHom.inl Sym Sym) =
      (alternatingGroup (Fin 5)).prod (⊥ : Subgroup Sym) := by
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩; exact ⟨hg,one_mem _⟩
  · rintro ⟨h₁,h₂⟩; exact ⟨x.1,h₁,Prod.ext rfl h₂.symm⟩

omit [Finite G] in
theorem leftFactorMap_component (Y : Subgroup G) [Y.Normal] (e : Y ≃* Sym × Sym) :
    IsComponent G ((alternatingGroup (Fin 5)).map (leftFactorMap Y e)) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let A : Subgroup (Sym × Sym) := (alternatingGroup (Fin 5)).prod (⊥ : Subgroup Sym)
  let B := A.map e.symm.toMonoidHom
  let : B.Normal := (inferInstance : A.Normal).map _ e.symm.surjective
  have hn : (B.map Y.subtype).IsSubnormal :=
    (inferInstance : B.Normal).isSubnormal.trans' (inferInstance : Y.Normal).isSubnormal
  have hm : (alternatingGroup (Fin 5)).map (leftFactorMap Y e) = B.map Y.subtype := by
    change _ = (A.map e.symm.toMonoidHom).map Y.subtype
    rw [show A = (alternatingGroup (Fin 5)).prod (⊥ : Subgroup Sym) from rfl,
      ←left_alternating_map,map_map,map_map]
    rfl
  exact ⟨hm ▸ hn,IsQuasisimple.of_mulEquiv
    ((alternatingGroup (Fin 5)).equivMapOfInjective _ (leftFactorMap_injective Y e))⟩

omit [Finite G] in
theorem leftFactorMap_not_le_maximal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) (e : Y ≃* Sym × Sym) (hYT : Y ⊔ (T : Subgroup G) = ⊤)
    (t : G) (ht : t ∈ T)
    (hex : (leftFactorMap Y e).range.map (MulAut.conj t).toMonoidHom = (rightFactorMap Y e).range) :
    ¬ (leftFactorMap Y e).range ≤ minimalParabolicMax T hP := by
  intro hleft
  let M := minimalParabolicMax T hP
  have htM : t ∈ M := (minimalParabolicMax_spec T hP).2 ht
  have hright : (rightFactorMap Y e).range ≤ M := by
    rw [←hex]
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hleft
    change _ ≤ M.map (MulAut.conj t).toMonoidHom at hh
    have hm : M.map (MulAut.conj t).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer htM)
    exact hh.trans hm.le
  have hYM : Y ≤ M := by
    intro y hy
    have h₁ : leftFactorMap Y e (e ⟨y,hy⟩).1 ∈ M := hleft ⟨_,rfl⟩
    have h₂ : rightFactorMap Y e (e ⟨y,hy⟩).2 ∈ M := hright ⟨_,rfl⟩
    have heq : leftFactorMap Y e (e ⟨y,hy⟩).1 * rightFactorMap Y e (e ⟨y,hy⟩).2 = y := by
      change (e.symm ((e ⟨y,hy⟩).1,1) : G) * (e.symm (1,(e ⟨y,hy⟩).2) : G) = y
      rw [←Subgroup.coe_mul,←map_mul]
      simp
    exact heq ▸ M.mul_mem h₁ h₂
  have hh := sup_le hYM (minimalParabolicMax_spec T hP).2
  rw [hYT] at hh
  exact (minimalParabolicMax_spec T hP).1.ne_top (top_unique hh)

theorem paired_first_factor_maximal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (e : Y ≃* Sym × Sym) (hYT : Y ⊔ (T : Subgroup G) = ⊤)
    (t : G) (ht : t ∈ T)
    (hex : (leftFactorMap Y e).range.map (MulAut.conj t).toMonoidHom = (rightFactorMap Y e).range)
    (a : Sym) (hD : ((D 5).map (MulAut.conj a).toMonoidHom).map (leftFactorMap Y e) ≤ T) :
    (minimalParabolicMax T hP).comap (leftFactorMap Y e) =
      pointFour.map (MulAut.conj a).toMonoidHom := by
  let L := (alternatingGroup (Fin 5)).map (leftFactorMap Y e)
  let eL := (alternatingGroup (Fin 5)).equivMapOfInjective (leftFactorMap Y e) (leftFactorMap_injective Y e)
  apply source_symmetric_factor_maximal T hP (leftFactorMap_component Y e) eL.symm
    (leftFactorMap Y e) ?_ (leftFactorMap_not_le_maximal T hP Y e hYT t ht hex) a hD
  intro l
  have hh := congrArg Subtype.val (eL.apply_symm_apply l)
  exact hh

theorem paired_second_factor_maximal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (e : Y ≃* Sym × Sym) (hYT : Y ⊔ (T : Subgroup G) = ⊤)
    (t : G) (ht : t ∈ T)
    (hex : (rightFactorMap Y e).range.map (MulAut.conj t).toMonoidHom = (leftFactorMap Y e).range)
    (b : Sym) (hD : ((D 5).map (MulAut.conj b).toMonoidHom).map (rightFactorMap Y e) ≤ T) :
    (minimalParabolicMax T hP).comap (rightFactorMap Y e) =
      pointFour.map (MulAut.conj b).toMonoidHom := by
  exact paired_first_factor_maximal T hP Y (e.trans MulEquiv.prodComm) hYT t ht hex b hD
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
