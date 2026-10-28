module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.Geometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding all Bender models in the deleted-five branch

In each genuine simple Bender model the first omega subgroup of a Sylow
2-subgroup is its center. The original elementary commutator layer U lies
in such a center. If U is self-centralizing, the entire Sylow subgroup lies
in U. Thus U itself is Sylow and its full normalizer is solvable. The
original block normalizes its characteristic U, contradicting its A₅
quotient. This uses the existing complete model geometry uniformly, without
new parameter bounds or separate family calculations.

Source: Aschbacher–Smith 13.5.15, printed p.921, applying Theorem C and the
rank-one Sylow-normalizer facts of F.1.3(1), printed pp.259–260.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
variable {X : Type*} [Group X] [Finite X]

/-- The actual deleted-five block and its self-centralizing layer exclude
all three Bender alternatives in the source model catalogue. -/
theorem not_benderModel (K : Subgroup X) (hK : ChapterC.IsAlternatingBlock K 5)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype) : ¬ ClassificationModels.IsBenderModel X := by
  intro hm
  let U := (ChapterC.blockU K).map K.subtype
  let := hK.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map K.subtype
  obtain ⟨P,hUP⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_le_sylow
  have hb := Chapter1.QuasisimpleInvolutions.isSimpleBenderGroup_of_benderModel hm
  obtain ⟨_,_,_,hw,_⟩ :=
    Chapter2.BenderFusion.GoodCentralizers.exponent_and_omega_of_simpleBender hb P
  have hUZ : U ≤ (center P).map (P : Subgroup X).subtype := by
    rw [←hw,←omegaOneAmbient_eq_self U]
    exact omegaOneAmbient_mono hUP
  have hPC : (P : Subgroup X) ≤ centralizer (U : Set X) := by
    intro p hp
    apply mem_centralizer_iff.mpr
    intro u hu
    obtain ⟨z,hz,rfl⟩ := hUZ hu
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨p,hp⟩).symm
  have hUeq : U = (P : Subgroup X) := le_antisymm hUP (hPC.trans hself)
  have hr : ChapterF.Source.IsRankOneModel X := by
    cases hm with
    | linear n hn h => exact .linear n (by omega) h
    | unitary n hn h => exact .projective_unitary n (by omega) h
    | suzuki m _ h => exact .suzuki m h
  let : Group.IsSolvable (normalizer (P : Set X)) := (hr.rankOneSylowFacts P).solvable
  have hKN : K ≤ normalizer (P : Set X) := by
    change K ≤ normalizer ((P : Subgroup X) : Set X)
    rw [←hUeq]
    exact K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hKN) (inclusion_injective hKN)
  obtain ⟨e⟩ := hK.2.2.quotient_iso
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
