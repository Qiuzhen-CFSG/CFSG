module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightComplete
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ActionImage
public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure

/-!
# Excluding the two block rows for a diagram-selected right factor

The original component inherits characteristic two from H. Its two-core
normalizes each perfect parabolic preimage. If that factor were short,
C.1.11 would make the two-core centralize its commutator layer U; the
core-centralizer bound would then put U in the original two-core.
The marked parabolic projection kills U but has a nontrivial perfect
characteristic-two image. This contradicts C.1.8, since a nontrivial
perfect quotient of a short group modulo U is quasisimple.

The argument treats both linear and symplectic diagram factors. In the
linear case the literal projective marking retains its scalar kernel,
including at field order four. The source selector and Chapter 12
application use the same canonical factors and S = O₂(N_G(L) ∩ H).
This is the exclusion of the two block amalgam rows in 5.2.6; the other
diagram rows and ambient completion recognition remain to be proved.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651, using C.1.8,11,
printed pp.123–124 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]

private theorem not_short_of_core_killed
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (R : Subgroup X) (hR : pCore 2 X ≤ normalizer (R : Set X))
    [Nontrivial Y] [Group.IsPerfect Y]
    (f : R →* Y) (hf : Function.Surjective f)
    (hkill : ∀ x : R, (x : X) ∈ pCore 2 X → f x = 1)
    (hfit : generalizedFitting Y = pCore 2 Y) : ¬ ChapterC.IsShort R := by
  intro hs
  have hU : (ChapterC.blockU R).map R.subtype ≤ pCore 2 X :=
    (le_centralizer_iff.mp
      (hs.normalizing_twoGroup_centralizes_blockU pCore_isPGroup
        le_normalizer_of_normal hR)).trans hX
  have hk : ChapterC.blockU R ≤ f.ker := by
    intro x hx
    exact hkill x (hU (mem_map_of_mem R.subtype hx))
  let q := QuotientGroup.lift (ChapterC.blockU R) f hk
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  rcases hs.quotient_blockU with hquasi | hthree
  · let := hquasi
    let : IsQuasisimple Y := IsQuasisimple.of_surjective q hq
    have hc : (⊤ : Subgroup Y) ≤ pCore 2 Y := by
      apply ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit).trans'
      exact le_centralizer_iff.mpr ((IsQuasisimple.pCore_le_center 2).trans
        (by intro x hx; exact mem_centralizer_iff.mpr fun y _ => mem_center_iff.mp hx y))
    have hp : IsPGroup 2 Y :=
      (show IsPGroup 2 (⊤ : Subgroup Y) from top_le_iff.mp hc ▸ pCore_isPGroup).of_equiv topEquiv
    exact Group.IsPerfect.not_isNilpotent Y hp.isNilpotent
  · let : IsCyclic (R ⧸ ChapterC.blockU R) := isCyclic_of_prime_card hthree
    let : Group.IsSolvable Y := Group.isSolvable_of_surjective hq
    exact Group.IsPerfect.not_isSolvable Y inferInstance

private theorem not_short_residual_of_core_killed
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (r : X →* Y) (hr : Function.Surjective r) (hk : pCore 2 X ≤ r.ker)
    (P B : Subgroup Y) [Nontrivial B] [Group.IsPerfect B]
    (he : (solvableResidual P).map P.subtype = B)
    (hfit : generalizedFitting B = pCore 2 B) :
    ¬ ChapterC.IsShort ((solvableResidual (P.comap r)).map (P.comap r).subtype) := by
  let J := P.comap r
  let R := (solvableResidual J).map J.subtype
  have hQJ : pCore 2 X ≤ J := hk.trans (P.ker_le_comap r)
  have hn : pCore 2 X ≤ normalizer (R : Set X) :=
    (hQJ.trans J.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image J (solvableResidual J))
  have him : R.map r = B := (map_solvableResidual_comap r hr P).trans he
  let f := (MulEquiv.subgroupCongr him).toMonoidHom.comp (r.subgroupMap R)
  apply not_short_of_core_killed hX R hn f
    ((MulEquiv.subgroupCongr him).surjective.comp (r.subgroupMap_surjective R)) ?_ hfit
  intro x hx
  apply Subtype.ext
  exact hk hx

open scoped MatrixGroups
open Matrix.PSL3.LinearThree

/-- The actual linear diagram factors are not short groups. The covering
center is retained in the source map, including over field order four. -/
theorem linear_source_factor_not_short
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    {M C : Subgroup X} (hC : C.IsCComponent)
    (hO : pCore 2 X ≤ sourceKernel M)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) :
    ¬ ChapterC.IsShort (Prime.linearSourceFactor M C e i) := by
  let r := Prime.linearComponentProjection M C e
  have hr : Function.Surjective r :=
    e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective C)
  have hk : pCore 2 C ≤ r.ker := by
    intro x hx
    apply e.map_eq_one_iff.mpr
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff x.val).mpr
    exact hO (pCoreIn_le_of_subnormal 2 hC.subnormal (mem_map_of_mem C.subtype hx))
  let B := CoveredLocals.localProjective F i
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr
    (fun hb => CoveredLocals.local_not_le_borel i (hb ▸ bot_le))
  let : Group.IsPerfect B := by
    cases i
    · exact lineLocal_isPerfect F hF
    · exact pointLocal_isPerfect F hF
  have he : (solvableResidual (CoveredLocals.parabolic F i)).map
      (CoveredLocals.parabolic F i).subtype = B := by
    cases i
    · exact ParabolicResiduals.lineParabolic_residual F hF
    · exact ParabolicResiduals.pointParabolic_residual F hF
  have hfit : generalizedFitting B = pCore 2 B := by
    cases i
    · exact lineLocal_generalizedFitting_eq_twoCore F
    · exact pointLocal_generalizedFitting_eq_twoCore F
  have hn := not_short_residual_of_core_killed
    (subnormal_core_selfCentralizing hX C hC.subnormal) r hr hk
    (CoveredLocals.parabolic F i) B he hfit
  intro hs
  exact hn (ChapterC.RankOne.Solvable.isShort_of_equiv
    ((CoveredLocals.factor r i).equivMapOfInjective C.subtype C.subtype_injective).symm hs)

open Theory.SpecificGroups.SymplecticFour in
/-- The two symplectic diagram factors have the same nonshort obstruction,
on their literal original source quotient and perfect preimages. -/
theorem symplectic_source_factor_not_short
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    {M C : Subgroup X} (hO : pCore 2 X ≤ sourceKernel M)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp F) (i : Bool) :
    ¬ ChapterC.IsShort (Prime.symplecticSourceFactor M C e i) := by
  let A := Prime.symplecticModelLocal F i
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (sourceImage M C).subtype_injective.comp e.symm.injective
  let d := A.equivMapOfInjective j hj
  let : Group.IsPerfect A := by
    cases i
    · exact planeLocal_perfect hF hf
    · exact pointLocal_perfect hF hf
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^f from Nat.pow_lt_pow_right (by decide) hf)
  let := NaturalExtension.model_simple hlarge
  let : Nontrivial A := by
    cases i
    · exact Function.Surjective.nontrivial Plane.quotientMap_surjective
    · exact Function.Surjective.nontrivial pointQuotient_surjective
  let : Group.IsPerfect (A.map j) := Group.IsPerfect.map j
  let : Nontrivial (A.map j) := d.symm.toEquiv.nontrivial
  have hfit : generalizedFitting A = pCore 2 A := by
    cases i
    · exact (planeNaturalExtension hF hf).generalizedFitting_eq hlarge
    · exact (pointNaturalExtension hF hf).generalizedFitting_eq hlarge
  have hfit' : generalizedFitting (A.map j) = pCore 2 (A.map j) :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 d).mp
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit))
  apply not_short_residual_of_core_killed hX (QuotientGroup.mk' (sourceKernel M))
    (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])
    (A.map j) (A.map j) ?_ hfit'
  rw [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype]

variable {G : Type*} [Group G] [Finite G]

/-- In the marked diagram branch, choose the same normalized perfect factor
as before, retaining its actual binary linear quotient and independent
field degree. Its nonshort property excludes both natural-block rows
of the subsequent F.1.12 recognition on that literal factor. -/
theorem diagram_source_rightFactor_linear_not_short
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : RightDiagramSource T L H) :
    ∃ (R : Subgroup G) (f : ℕ), RightFactor T L H A B R ∧ Group.IsPerfect R ∧
      ¬ ChapterC.IsShort R ∧ 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1)
  let M := (normalizer (L : Set G)).subgroupOf H
  have hO : pCore 2 H ≤ sourceKernel M := normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
      (comap_mono h.sylow_normalizes))
  obtain ⟨C,f,hC,hqs,_,hf,hc,hm⟩ := hs
  rcases hm with ⟨F,_,_,_,_,hF,e,he,hmove⟩ | ⟨F,_,_,_,_,hF,e,he,hmove⟩
  · let R0 := Prime.linearSourceFactor M C e true
    let R := R0.map H.subtype
    have hlarge : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
    have hnot := linear_source_factor_not_short hchar hC hO hlarge e true
    let : Group.IsPerfect (CoveredLocals.factor (Prime.linearComponentProjection M C e) true) :=
      Group.IsPerfect.map _
    let : Group.IsPerfect R0 := Group.IsPerfect.map _
    refine ⟨R,f,linear_source_rightFactor_of_nonprojective_four h.sylow_normalizes hH hpar
      hthree c hN hC hqs hc hf hF e he hmove true,Group.IsPerfect.map H.subtype,?_,hf,?_⟩
    · intro hshort
      exact hnot (ChapterC.RankOne.Solvable.isShort_of_equiv
        (R0.equivMapOfInjective H.subtype H.subtype_injective).symm hshort)
    · exact (linear_source_factor_geometry h.sylow_normalizes hH hpar c hN
        hC hqs hc hf hF e he hmove true).2.2.2.1
  · obtain ⟨eF,_,hr⟩ := symplectic_source_rightFactors h.sylow_normalizes hH hpar c hN
      hC hqs hc hf hF e he hmove
    let R0 := Prime.symplecticSourceFactor M C eF true
    let : Group.IsPerfect R0 := by
      unfold R0 Prime.symplecticSourceFactor
      exact Group.IsPerfect.map _
    refine ⟨R0.map H.subtype,f,(hr true).1,Group.IsPerfect.map H.subtype,?_,hf,(hr true).2.1⟩
    intro hshort
    exact symplectic_source_factor_not_short hchar hO hf hF eF true
      (ChapterC.RankOne.Solvable.isShort_of_equiv
        (R0.equivMapOfInjective H.subtype H.subtype_injective).symm hshort)


/-- In the marked diagram branch, choose the same normalized perfect factor
as before and prove it is nonshort. This excludes both natural-block rows
of the subsequent F.1.12 recognition on that literal factor. -/
theorem diagram_source_rightFactor_not_short
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : RightDiagramSource T L H) :
    ∃ R : Subgroup G, RightFactor T L H A B R ∧ Group.IsPerfect R ∧
      ¬ ChapterC.IsShort R := by
  obtain ⟨R,_,hr,hp,hnot,_,_⟩ := diagram_source_rightFactor_linear_not_short
    h hH hpar hthree c hN hs
  exact ⟨R,hr,hp,hnot⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
