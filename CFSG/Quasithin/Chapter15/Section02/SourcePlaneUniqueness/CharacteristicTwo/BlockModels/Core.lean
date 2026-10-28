module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockExclusion
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# The two-core of the block-orbit extension

Write S = C_T(ZS), K = O²(H), QI = O₂(KS), X₀ for the block orbit,
and U₀ = ⟨ZS^X₀⟩. Normalization by S forces O₂(X₀QI) into S;
normality then makes this core centralize U₀. A centralizer marking
C_X₀(ZS) ≤ KS puts it in QI. For a two-perfect X₀ with simple
O₂-quotient outside the partner, C_X₀QI(U₀) is a two-group, giving
O₂(X₀QI) = C_QI(U₀) and the actual canonical best offender.

These deductions remove core and relative-normality callbacks in the
preliminary 15.2.23 block argument. The model-specific marking remains
with this task; this module does not assert its existence for every orbit.
Source: Aschbacher--Smith, printed p.1115, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

theorem plane_span_extension_core_le_sylow
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G)) :
    (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 ≤ planeSylow T ZS := by
  let Q := planeParabolicCore T H ZS
  let E := X0 ⊔ Q
  let R := E.pCoreIn 2
  have hPI : (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS ≤ I :=
    (d.residual_sup_planeSylow_le hI).trans inf_le_right
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hEI : E ≤ I := sup_le hXI hQI
  have hSI : planeSylow T ZS ≤ I := le_sup_right.trans hPI
  have hSQ : planeSylow T ZS ≤ normalizer (Q : Set G) :=
    le_sup_right.trans (((pResidual 2 H).map H.subtype ⊔ planeSylow T ZS).le_normalizer.trans
      (normalizer_le_normalizer_intrinsicCore _))
  have hSE : planeSylow T ZS ≤ normalizer (E : Set G) :=
    (le_inf (hSI.trans hn) hSQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSR : planeSylow T ZS ≤ normalizer (R : Set G) :=
    hSE.trans (normalizer_le_normalizer_intrinsicCore E)
  have hRI : R ≤ I := (pCoreIn_le 2 E).trans hEI
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hPR : (P : Subgroup I) ≤ normalizer (R.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hRI]
    intro x hx
    exact hSR (hP ▸ mem_map_of_mem I.subtype hx)
  have hRS := ((isPGroup_pCoreIn 2 E).comap_subtype (K := I)).le_sylow_of_normalized P hPR
  intro x hx
  rw [← hP]
  exact mem_map_of_mem I.subtype (hRS (show (⟨x,hRI hx⟩ : I) ∈ R.subgroupOf I from hx))

theorem plane_span_extension_core_centralizes
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G)) :
    (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 ≤
      centralizer (conjugateSpanBy ZS X0 : Set G) := by
  apply le_centralizer_conjugateSpanBy_of_normalizes
  · exact le_sup_left.trans ((X0 ⊔ planeParabolicCore T H ZS).le_normalizer.trans
      (normalizer_le_normalizer_intrinsicCore _))
  · exact (d.plane_span_extension_core_le_sylow hI hXI hn).trans inf_le_right

theorem plane_block_centralizer_normalized
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hn : I ≤ normalizer (X0 : Set G)) :
    (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS ≤
      normalizer ((X0 ⊓ centralizer (ZS : Set G) : Subgroup G) : Set G) := by
  have hPI := (d.residual_sup_planeSylow_le hI).trans inf_le_right
  have hPC : (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS ≤ centralizer (ZS : Set G) :=
    sup_le d.residual_centralizes inf_le_right
  exact (le_inf (hPI.trans hn) (hPC.trans (centralizer (ZS : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

theorem plane_span_extension_core_le_of_marking
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hmark : X0 ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS)
    : (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 ≤ planeParabolicCore T H ZS := by
  apply le_trans ?_ (d.plane_span_centralizer_core hI hn hmark
    (d.plane_block_centralizer_normalized hI hn)).le
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
  · exact le_inf (pCoreIn_le 2 _)
      ((d.plane_span_extension_core_le_sylow hI hXI hn).trans inf_le_right)
  · exact inf_le_left.trans ((X0 ⊔ planeParabolicCore T H ZS).le_normalizer.trans
      (normalizer_le_normalizer_intrinsicCore _))

theorem plane_span_extension_core_eq_of_centralizer_twoGroup
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hcore : (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 ≤ planeParabolicCore T H ZS)
    (hC : IsPGroup 2 ((X0 ⊔ planeParabolicCore T H ZS) ⊓
      centralizer (conjugateSpanBy ZS X0 : Set G) : Subgroup G)) :
    (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer (conjugateSpanBy ZS X0 : Set G) := by
  apply le_antisymm (le_inf hcore (d.plane_span_extension_core_centralizes hI hXI hn))
  apply le_trans (inf_le_inf le_sup_right le_rfl)
  apply le_pCoreIn_of_normalizes hC inf_le_left
  exact (le_inf (X0 ⊔ planeParabolicCore T H ZS).le_normalizer
    ((d.plane_span_normalized hI hn).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

theorem plane_span_extension_centralizer_twoGroup
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hpX : IsPPerfect 2 X0) [IsSimpleGroup (X0 ⧸ pCore 2 X0)]
    (hout : ¬ X0 ≤ Mc) :
    IsPGroup 2 ((X0 ⊔ planeParabolicCore T H ZS) ⊓
      centralizer (conjugateSpanBy ZS X0 : Set G) : Subgroup G) := by
  let Q := planeParabolicCore T H ZS
  let E := X0 ⊔ Q
  let U := conjugateSpanBy ZS X0
  let C := E ⊓ centralizer (U : Set G)
  let A := (centralizer (U : Set G)).comap X0.subtype
  have hEI : E ≤ I := sup_le hXI ((pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  have hXU : X0 ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (hXU.trans (normalizer_le_normalizer_centralizer U))
  have hA : A ≠ ⊤ := by
    intro he
    apply hout
    intro x hx
    have hc : x ∈ centralizer (U : Set G) :=
      show (⟨x,hx⟩ : X0) ∈ A from he ▸ mem_top _
    exact ((d.centralizer_le_intersection hI)
      (centralizer_le (le_conjugateSpanBy ZS X0) hc)).1
  have hAcore : A ≤ pCore 2 X0 := by
    let q := QuotientGroup.mk' (pCore 2 X0)
    let : (A.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    rcases (inferInstance : (A.map q).Normal).eq_bot_or_eq_top with hb | ht
    · simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp hb
    · have hgen : A ⊔ pCore 2 X0 = ⊤ := by
        rw [← QuotientGroup.ker_mk' (pCore 2 X0), ← comap_map_eq, ht, comap_top]
      exact (hA (hpX A inferInstance
        (isPGroup_quotient_of_sup_eq_top A (pCore 2 X0) pCore_isPGroup hgen))).elim
  let N := X0.subgroupOf E
  let : N.Normal := normal_subgroupOf_of_le_normalizer (hEI.trans hn)
  have hgen : N ⊔ Q.subgroupOf E = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,← MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (E ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (Q.subgroupOf E)
      (isPGroup_pCoreIn 2 _).comap_subtype hgen
  let f := (QuotientGroup.mk' N).comp (inclusion (show C ≤ E from inf_le_left))
  have hker : IsPGroup 2 f.ker := by
    let r : f.ker →* X0 := (C.subtype.comp f.ker.subtype).codRestrict X0 (by
      intro x
      exact (QuotientGroup.eq_one_iff (N := N) (inclusion inf_le_left x.val)).mp x.property)
    let r' : f.ker →* pCore 2 X0 := r.codRestrict _ (fun x => hAcore x.val.property.2)
    apply pCore_isPGroup.of_injective r'
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 X0 => (z.val : G)) hxy
  have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup f hker
  rw [comap_top] at hh
  exact hh.of_equiv topEquiv

theorem plane_span_extension_core_eq_of_simple_marking
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hpX : IsPPerfect 2 X0) [IsSimpleGroup (X0 ⧸ pCore 2 X0)]
    (hout : ¬ X0 ≤ Mc)
    (hmark : X0 ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS) :
    (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer (conjugateSpanBy ZS X0 : Set G) :=
  d.plane_span_extension_core_eq_of_centralizer_twoGroup hI hXI hn
    (d.plane_span_extension_core_le_of_marking hI hXI hn hmark)
    (d.plane_span_extension_centralizer_twoGroup hI hXI hn hpX hout)

theorem plane_span_canonical_bestOffender_of_simple_marking
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hpX : IsPPerfect 2 X0) [IsSimpleGroup (X0 ⧸ pCore 2 X0)]
    (hout : ¬ X0 ≤ Mc)
    (hmark : X0 ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS) :
    let E := X0 ⊔ planeParabolicCore T H ZS
    let U := (conjugateSpanBy ZS X0).subgroupOf E
    ∃ hnormal : U.Normal, ∃ helementary : IsElementaryAbelian 2 U,
      letI := hnormal
      letI := helementary
      let C := centralizer (U : Set E)
      let q := QuotientGroup.mk' C
      ∃ A ∈ elementaryAbelianMaxSubgroups ((planeParabolicCore T H ZS).subgroupOf E),
        Representation.BinaryOffender.IsBestOffender
          (Representation.NormalElementaryQuotient.representation U q
            (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) (A.map q) :=
  d.plane_span_canonical_bestOffender hI hfit hXI hn hout
    (d.plane_span_extension_core_eq_of_simple_marking hI hXI hn hpX hout hmark)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
