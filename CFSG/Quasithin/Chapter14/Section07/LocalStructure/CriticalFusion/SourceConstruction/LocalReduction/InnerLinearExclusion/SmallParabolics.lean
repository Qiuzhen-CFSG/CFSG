module
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourceLifting
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores
public import Theory.SpecificGroups.PSL3Two.Parabolics.CosetGeometry

/-!
# The second parabolic in the small full quotients

For an actual full quotient PSL₃(2), A₆ or S₆, the two model parabolics
lift through the literal two-core projection. The given S₃ overgroup
of a Sylow subgroup has index three over that Sylow, so it equals one
of the lifted parabolics. This constructs the other one, with its full
S₃ quotient, intersection, generation and exhaustive local lattice.

This is the opening subgroup construction of Aschbacher–Smith 14.7.11,
printed pp.1045–1046, used in 14.7.49–51 on pp.1064–1065 of
refs/quasithin.pdf. The PSL₃(2) model retains its existing ATLAS
attribution and license, LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

private def coreCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def comapCoreEquiv {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (q : A →* B) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) (P : Subgroup B) :
    (P.comap q ⧸ pCore 2 (P.comap q)) ≃* (P ⧸ pCore 2 P) := by
  let f : P.comap q →* P := (q.comp (P.comap q).subtype).codRestrict P (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨⟨x,show q x ∈ P from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
  have hfk : IsPGroup 2 f.ker := by
    let g : f.ker →* q.ker :=
      ((P.comap q).subtype.comp f.ker.subtype).codRestrict q.ker (by
        intro x
        exact congrArg Subtype.val x.property)
    apply hk.of_injective g
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => (z : A)) he))
  exact f.pCoreQuotientEquiv hf hfk

private theorem model_pair {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (B P R : Subgroup A)
    (hB : B = (S : Subgroup A)) (hI : P ⊓ R = B) (hne : P ≠ R)
    (hc : ∀ U : Subgroup A, (IsCoatom U ∧ (S : Subgroup A) ≤ U) ↔ U = P ∨ U = R)
    (ep : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (er : (R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) :
    ∃ P R : Subgroup A, RankTwoParabolics A (S : Subgroup A) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) :=
  ⟨P,R,⟨((hc P).mpr (Or.inl rfl)).1,((hc R).mpr (Or.inr rfl)).1,
    hne,hI.trans hB,fun U hSU hU => (hc U).mp ⟨hU,hSU⟩⟩,⟨ep⟩,⟨er⟩⟩

private theorem three_model_pair (S : Sylow 2 Matrix.PSL3Two.PSL) :
    ∃ P R : Subgroup Matrix.PSL3Two.PSL,
      RankTwoParabolics _ (S : Subgroup _) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) := by
  open Matrix.PSL3Two in
  obtain ⟨g,hg,hne,hi,hc⟩ := Fano.sylow_parabolics_conjugate S
  open Matrix.PSL3Two in
  exact model_pair S _ _ _ rfl hi hne hc
    ((coreCongr ((MulAut.conj g).subgroupMap pointParabolic)).symm.trans
      pointParabolicCoreQuotientEquivS3)
    ((coreCongr ((MulAut.conj g).subgroupMap lineParabolic)).symm.trans
      lineParabolicCoreQuotientEquivS3)

private theorem six_model_pair (S : Sylow 2 (Equiv.Perm (Fin 6))) :
    ∃ P R : Subgroup (Equiv.Perm (Fin 6)),
      RankTwoParabolics _ (S : Subgroup _) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) := by
  open Theory.SpecificGroups.SymmetricSix in
  obtain ⟨g,hg,hc⟩ := coatoms_over_sylow S
  let a := MulAut.conj g
  open Theory.SpecificGroups.SymmetricSix in
  exact model_pair S _ _ _ hg (a.mapSubgroup.map_inf _ _).symm
    (fun he => synthemeStabilizer_not_le_duad (le_of_eq (a.mapSubgroup.injective he).symm)) hc
    ((coreCongr (a.subgroupMap duadStabilizer)).symm.trans duadCoreQuotientEquiv)
    ((coreCongr (a.subgroupMap synthemeStabilizer)).symm.trans synthemeCoreQuotientEquiv)

private theorem alternating_model_pair (S : Sylow 2 (alternatingGroup (Fin 6))) :
    ∃ P R : Subgroup (alternatingGroup (Fin 6)),
      RankTwoParabolics _ (S : Subgroup _) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) := by
  open Theory.SpecificGroups.SymmetricSix in
  obtain ⟨g,hg,hc⟩ := a6_coatoms_over_sylow S
  let a := MulAut.conj g
  open Theory.SpecificGroups.SymmetricSix in
  exact model_pair S _ _ _ hg (a.mapSubgroup.map_inf _ _).symm
    (fun he => a6SynthemeStabilizer_not_le_duad (le_of_eq (a.mapSubgroup.injective he).symm)) hc
    ((coreCongr (a.subgroupMap a6DuadStabilizer)).symm.trans a6DuadCoreQuotientEquiv)
    ((coreCongr (a.subgroupMap a6SynthemeStabilizer)).symm.trans a6SynthemeCoreQuotientEquiv)

private theorem lift_model_pair {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (S : Sylow 2 A) (q : A →* B) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hm : ∃ P R : Subgroup B, RankTwoParabolics B ((S.mapSurjective hq) : Subgroup B) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3))) :
    ∃ P R : Subgroup A, RankTwoParabolics A (S : Subgroup A) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨P,R,hpr,⟨ep⟩,⟨er⟩⟩ := hm
  have hS : ((S.mapSurjective hq : Sylow 2 B) : Subgroup B).comap q = (S : Subgroup A) :=
    comap_map_eq_self (hk.le_sylow_of_normal S)
  exact ⟨P.comap q,R.comap q,hS ▸ hpr.comap_surjective q hq,
    ⟨(comapCoreEquiv q hq hk P).trans ep⟩,⟨(comapCoreEquiv q hq hk R).trans er⟩⟩

/-- The original S₃ overgroup selects one of the two parabolics in each
of the three full quotients of 14.7.11; the other parabolic is constructed. -/
theorem small_quotient_second_parabolic {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (B : Subgroup X) (hSB : (S : Subgroup X) ≤ B) (hB : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hm : Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 6))) :
    ∃ R : Subgroup X, RankTwoParabolics X (S : Subgroup X) B R ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) := by
  have pairs : ∃ P R : Subgroup X, RankTwoParabolics X (S : Subgroup X) P R ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3)) := by
    have pull {A : Type} [Group A] [Finite A] (e : (X ⧸ pCore 2 X) ≃* A)
        (hm : ∀ U : Sylow 2 A, ∃ P R : Subgroup A,
          RankTwoParabolics A (U : Subgroup A) P R ∧
          Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
          Nonempty ((R ⧸ pCore 2 R) ≃* Equiv.Perm (Fin 3))) := by
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
      have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hk : IsPGroup 2 q.ker := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
        exact pCore_isPGroup
      exact lift_model_pair S q hq hk (hm (S.mapSurjective hq))
    rcases hm with he | he | he
    · exact pull he.some three_model_pair
    · exact pull he.some alternating_model_pair
    · exact pull he.some six_model_pair
  obtain ⟨P,R,hpr,⟨ep⟩,⟨er⟩⟩ := pairs
  have hSP : (S : Subgroup X) ≤ P := hpr.borel_eq ▸ inf_le_left
  have hSR : (S : Subgroup X) ≤ R := hpr.borel_eq ▸ inf_le_right
  have index_three (U : Subgroup X) (hSU : (S : Subgroup X) ≤ U)
      (e : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
      (S : Subgroup X).relIndex U = 3 :=
    SymmetricThreeTwoCore.sylow_index_three e (S.subtype hSU)
  have eq_of_le (U : Subgroup X) (hSU : (S : Subgroup X) ≤ U)
      (e : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (hBU : B ≤ U) : B = U := by
    have hi := relIndex_mul_relIndex (S : Subgroup X) B U hSB hBU
    rw [index_three B hSB eB,index_three U hSU e] at hi
    have hb : B.relIndex U = 1 := by omega
    exact le_antisymm hBU (relIndex_eq_one.mp hb)
  obtain ⟨U,hU,hBU⟩ := (eq_top_or_exists_le_coatom B).resolve_left hB
  rcases hpr.exhaustive U (hSB.trans hBU) hU with hUP | hUR
  · have he := eq_of_le P hSP ep (hUP ▸ hBU)
    exact ⟨R,he.symm ▸ hpr,⟨er⟩⟩
  · have he := eq_of_le R hSR er (hUR ▸ hBU)
    exact ⟨P,he.symm ▸ hpr.symm,⟨ep⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
