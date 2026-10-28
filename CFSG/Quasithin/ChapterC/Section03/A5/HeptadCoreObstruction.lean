module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
public import CFSG.Quasithin.ChapterC.Section03.A5.QuintetCoreObstruction
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
/-!
# The deleted-five obstruction in the native heptad local

The literal U equals the heptad two-core. Its faithful action kills the
entire two-core of the original block, so the image is an actual A5.
If it were local at a full Sylow, the five-rank bound would make that
Sylow normalize the same A5. Seven-letter placement then makes its
cubics three-cycles, which act without nonzero fixed vectors on the
heptad core. This contradicts the deleted-five module of the block.

Source: Aschbacher–Smith, proof of 2.4.25, printed p.543, using H.14.2(3),
p.397. The quotient and core maps retain their native source markings.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
/-- A two-kernel quotient retains the literal A5 marking of the block image. -/
private noncomputable def alternatingFive_quotient_equiv
    {G H : Type*} [Group G] [Group H]
    (q : G →* H) (hk : IsPGroup 2 q.ker) (A : Subgroup G)
    (hA : IsAlternatingBlock A 5)
    (hcore : (pCore 2 A).map A.subtype ≤ q.ker) :
    A.map q ≃* alternatingGroup (Fin 5) := by
  let f := q.subgroupMap A
  have heker : f.ker = pCore 2 A := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance,?_⟩
      change IsPGroup 2 (q.subgroupMap A).ker
      rw [Subgroup.ker_subgroupMap]
      exact hk.comap_subtype
    · intro a ha
      apply Subtype.ext
      exact hcore (mem_map_of_mem A.subtype ha)
  let e := (QuotientGroup.quotientMulEquivOfEq heker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective A))
  exact e.symm.trans hA.2.2.quotient_iso.some


private theorem heptad_threeCycle_fixed
    (a : alternatingGroup (Fin 7)) (ha : a.val.IsThreeCycle)
    (v : Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.Four)
    (hv : Sporadic.Mathieu.M23Geometry.heptadLinearAction a v = v) : v = 0 := by
  open Sporadic.Mathieu.M23Geometry in
    obtain ⟨g,hg⟩ := isConj_iff.mp (alternatingGroup.isThreeCycle_isConj (by simp)
      (show AlternatingSection.c.val.IsThreeCycle by
        apply card_support_eq_three_iff.mp
        decide +kernel) ha)
    have hh := congrArg (heptadLinearAction g⁻¹) hv
    rw [←hg,map_mul,map_mul,map_inv] at hh
    change (heptadLinearAction g).symm ((heptadLinearAction g)
      ((heptadLinearAction AlternatingSection.c) ((heptadLinearAction g).symm v))) =
      (heptadLinearAction g).symm v at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    have hz := (heptadLinearAction_cycle_fixed_iff _).mp hh
    have he := congrArg (heptadLinearAction g) hz
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using he

private theorem no_fixedFree_core_actor
    {G V : Type*} [Group G] [Group V] (A : Subgroup G)
    (hA : IsAlternatingBlock A 5)
    (E : V ≃* pCore 2 G) (hU : (blockU A).map A.subtype = pCore 2 G)
    (g : G) (hg : g ∈ A) (a : MulAut V) (ha : a^3=1)
    (hfix : ∀ v, a v = v → v=1)
    (hact : ∀ v, (E (a v) : G) = g * (E v : G) * g⁻¹) : False := by
  let U := (blockU A).map A.subtype
  let D : V ≃* U := E.trans (MulEquiv.subgroupCongr hU.symm)
  let f := MulAut.congr D a
  have hf (u : U) : f u = D (a (D.symm u)) := rfl
  have hD (v : V) : (D v : G) = (E v : G) := rfl
  apply hA.no_fixedFree_cubic_in_normalizer g (A.le_normalizer hg) f
  · rw [←map_pow,ha,map_one]
  · intro u hu
    have hh := congrArg D.symm hu
    rw [hf,D.symm_apply_apply] at hh
    apply D.symm.injective
    rw [map_one]
    exact hfix _ hh
  · intro u
    rw [hf,hD,hact]
    have he : (E (D.symm u) : G) = u.val :=
      (hD _).symm.trans (congrArg U.subtype (D.apply_symm_apply u))
    rw [he]

/-- The actual heptad core's deleted-five block is never local at a full Sylow. -/
theorem native_heptad_not_local_alternatingFive_core
    (A : Subgroup Sporadic.Mathieu.M23Geometry.CommonFour.markedHeptadStabilizer)
    (hA : IsAlternatingBlock A 5)
    (hU : (blockU A).map A.subtype = pCore 2 _)
    (S : Sylow 2 Sporadic.Mathieu.M23Geometry.CommonFour.markedHeptadStabilizer) :
    A ∉ ChapterA.Section03.localCComponents S := by
  open Sporadic.Mathieu.M23Geometry Sporadic.Mathieu.M23Geometry.ChapterHLocalActions in
    intro hlocal
    let G := CommonFour.markedHeptadStabilizer
    let q := sourceQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
    have hq : Function.Surjective q := sourceQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = pCore 2 G := by
      rw [MonoidHom.ker_comp_of_injective _ _ sourceQuotientEquiv.injective,QuotientGroup.ker_mk']
    have hp : IsPGroup 2 q.ker := hk ▸ pCore_isPGroup
    have hcent : centralizer (pCore 2 G : Set G) ≤ pCore 2 G :=
      (Theory.Quasithin.centralizer_pCore_le_iff 2 sourceStabilizerEquiv).mp
        heptadStabilizer_core_selfCentralizing
    have hcore : (pCore 2 A).map A.subtype ≤ q.ker := by
      rw [hk]
      rintro _ ⟨a,ha,rfl⟩
      apply hcent
      rw [←hU]
      rintro _ ⟨b,hb,rfl⟩
      exact congrArg A.subtype (hA.2.1.core_centralizes_blockU ha b hb)
    let B := A.map q
    let e := alternatingFive_quotient_equiv q hp A hA hcore
    let Q := S.mapSurjective hq
    let := hp.isNilpotent
    have hl : B ∈ ChapterA.Section03.localCComponents Q :=
      Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal q
    have hn := ChapterA.Section03.SourceEmbeddings.alternatingSeven_local_five_normalized B e Q hl
    have hc : Nat.card B = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num
    obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hc]; decide)
    have hcycle := Theory.SpecificGroups.Alternating.SevenFivePlacement.isThreeCycle_of_order_three B e Q hn a ha
    obtain ⟨g,hg,hga⟩ := a.property
    let f0 : MulAut (Multiplicative Four) := (heptadLinearAction a.val).toAddEquiv.toMultiplicative
    apply no_fixedFree_core_actor A hA sourceBinaryEquiv hU g hg f0
    · apply MulEquiv.ext
      intro v
      apply Multiplicative.toAdd.injective
      have hh : (heptadLinearAction a.val)^3=1 := by
        rw [←map_pow,show a.val^3=1 from congrArg B.subtype (ha ▸ pow_orderOf_eq_one a),map_one]
      exact DFunLike.congr_fun hh v.toAdd
    · intro v hv
      apply Multiplicative.toAdd.injective
      exact heptad_threeCycle_fixed a.val hcycle v.toAdd (congrArg Multiplicative.toAdd hv)
    · intro v
      change (sourceBinaryEquiv (Multiplicative.ofAdd (heptadRepresentation a.val v.toAdd))).val = _
      rw [←hga]
      exact (sourceBinaryEquiv_conjugation g v.toAdd).symm
end CFSG.Quasithin.ChapterC
