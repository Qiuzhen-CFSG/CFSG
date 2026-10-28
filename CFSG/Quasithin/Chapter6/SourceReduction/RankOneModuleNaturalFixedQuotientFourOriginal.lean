module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOffender
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSource
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreSupplement
public import Theory.Representation.SL2.BinaryHermitianIrreducibility
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NearMaximumAction
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The original Hermitian module supplies the Chapter K source

The action is the literal conjugation action of LT/O₂(LT) on the original
reduced subgroup W, with component the image of L. Full Hermitian coordinates
give irreducibility and a cubic actor of ratio 3/2. The original local
hypotheses give faithfulness, SQTK, and the generalized Fitting subgroup.
No replacement module or additional source hypotheses are assumed.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.QuasisimpleSource ChapterK.RankOne
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ} {s : ℕ} [NeZero s]

local instance originalFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance originalBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The genuine original quotient action, with its literal component image,
satisfies every Chapter K source condition and retains the supplied Hermitian
coordinates on the whole original module. -/
theorem Input.hermitian_original_source
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) :
    let J := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf J
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    let q := QuotientGroup.mk' (pCore 2 J)
    let hq := QuotientGroup.mk'_surjective (pCore 2 J)
    let hk : q.ker = centralizer (U : Set J) :=
      by exact (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
    let ρ := NormalElementaryQuotient.representation U q hq hk
    let Bq := (L.subgroupOf J).map q
    SourceHypotheses ρ Bq ∧ Nonempty (OrthogonalModel s ρ Bq) := by
  obtain ⟨e0,f0,hf0⟩ := hm
  let J := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf J
  let B := L.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  let Q := J ⧸ pCore 2 J
  let q : J →* Q := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let Bq := B.map q
  let : Bq.Normal := (inferInstance : B.Normal).map q hq
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eB : Bq ≃* Matrix.SpecialLinearGroup (Fin 2) (Field s) :=
    (coreQuotientEquivImage 2 B).symm.trans
      ((QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)).trans e0)
  let uW : U ≃* W := subgroupOfEquivOfLe h.reduced.1
  let f := uW.trans f0
  let c : Additive U ≃ₗ[ZMod 2] Space s :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  have hc : ∀ (l : Bq) x,
      c (ρ l x) = SL2.BinarySmall.hermitian s (eB l) (c x) := by
    intro l x
    obtain ⟨b,hb⟩ := q.subgroupMap_surjective B l
    let l0 : L := eb b
    have heB : eB (q.subgroupMap B b) = e0 (QuotientGroup.mk' (pCore 2 L) l0) := by
      change e0 (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb _
        ((coreQuotientEquivImage 2 B).symm (q.subgroupMap B b))) = _
      have heq : coreQuotientEquivImage 2 B (QuotientGroup.mk' (pCore 2 B) b) =
          q.subgroupMap B b := by
        apply Subtype.ext
        exact coreQuotientEquivImage_apply_mk 2 B b
      rw [←heq,MulEquiv.symm_apply_apply]
      rfl
    subst l
    rw [heB]
    let v : W := uW x.toMul
    have hact := hf0 l0 v
    have hcoords := congrArg f0
      (show f0.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian s
          (e0 (QuotientGroup.mk' (pCore 2 L) l0)) (f0 v).toAdd)) =
        W.normalizerMonoidHom ⟨l0,(le_sup_left.trans (reduced_normalizes h.reduced)) l0.property⟩ v from
          Subtype.ext hact)
    rw [f0.apply_symm_apply] at hcoords
    change c (NormalElementaryQuotient.representation U q hq hk (q b.val) x) = _
    apply Eq.trans ?_ (congrArg Multiplicative.toAdd hcoords.symm)
    apply congrArg (fun w : W => (f0 w).toAdd)
    apply Subtype.ext
    change (((NormalElementaryQuotient.representation U q hq hk (q b.val) x).toMul : J) : G) = _
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  let M : OrthogonalModel s ρ Bq := ⟨eB,c,hc⟩
  have hsup : B ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  let := h.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)).symm
  have hSQ : IsSQTK KnownSimple.IsKnownSimple J := by
    have hJL : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hJL)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (J.subgroupOf (normalizer (L : Set G))))
  change SourceHypotheses ρ Bq ∧ Nonempty (OrthogonalModel s ρ Bq)
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,⟨M⟩⟩
  · refine ⟨?_,hSQ.isKGroup.quotient (pCore 2 J)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 J) pCore_isPGroup).trans
      (hSQ.stronglyQuasithin p hp ho)
  · exact generalizedFitting_coreQuotient_eq_of_two_supplement B S S.isPGroup' hsup
  · exact IsQuasisimple.of_mulEquiv (coreQuotientEquivImage 2 B)
  · exact NormalElementaryQuotient.representation_injective U q hq hk
  · exact irreducible_of_surjective_equivariant (ρ.comp Bq.subtype)
      (SL2.BinarySmall.hermitian s) eB.toMonoidHom eB.surjective c hc
      (SL2.BinarySmall.hermitian_irreducible s)
  · exact M.ratio_upper_bounds.2.trans (by
      rw [ENNReal.div_le_iff (by norm_num) (by simp)]
      norm_num)

/-- Every actual near-maximum elementary subgroup moving the original
Hermitian module has half-degree two. Its literal quotient image has rank
one or three, and is generated by conjugates of an orthogonal transvection.
The rank-three case is retained in the numerical statement. -/
theorem Input.hermitian_original_near_maximum
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (A : Subgroup G) (hA : A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1)
    (hmove : ¬ A ≤ centralizer (W : Set G)) :
    let J := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf J
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    let q := QuotientGroup.mk' (pCore 2 J)
    let hq := QuotientGroup.mk'_surjective (pCore 2 J)
    let hk : q.ker = centralizer (U : Set J) :=
      by exact (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
    let ρ := NormalElementaryQuotient.representation U q hq hk
    let Bq := (L.subgroupOf J).map q
    let Aq := (A.subgroupOf J).map q
    s = 2 ∧ ¬ Aq ≤ Bq ∧ IsQuadratic ρ Aq ∧
      ((rank Aq = 1 ∧ fixedCodim ρ Aq = 2) ∨
        (rank Aq = 3 ∧ fixedCodim ρ Aq = 4)) ∧
      ∃ M : OrthogonalModel s ρ Bq, ∃ t : J ⧸ pCore 2 J,
        t ^ 2 = 1 ∧ t ∉ Bq ∧
        (∀ v, M.coordinates (ρ t v) =
          LinearEquiv.transvection
            (Representation.OrthogonalFourMinus.RankOne.traceFunctional_movedVector s)
            (M.coordinates v)) ∧
        Aq = closure {a | a ∈ Aq ∧ ∃ c : Bq, (c : J ⧸ pCore 2 J) * t * (c : J ⧸ pCore 2 J)⁻¹ = a} := by
  let J := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let Bq := (L.subgroupOf J).map q
  let A0 := A.subgroupOf J
  let Aq := A0.map q
  have hAJ : A ≤ J := hA.1.trans le_sup_right
  have hAm : A0.map J.subtype = A := map_subgroupOf_eq_of_le hAJ
  have hSm : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hAf : A0 ∈ ChapterB.thompsonFamily (S : Subgroup J) 1 := by
    apply (ChapterB.thompsonFamily_map_iff_of_injective J.subtype J.subtype_injective
      (S : Subgroup J) A0 1).mp
    rwa [hAm,hSm]
  have hne : Aq ≠ ⊥ := by
    intro hz
    have hc : A0 ≤ centralizer (U : Set J) := hk ▸ (map_eq_bot_iff A0).mp hz
    apply hmove
    intro a ha w hw
    exact congrArg J.subtype (hc (show (⟨a,hAJ ha⟩ : J) ∈ A0 from ha)
      ⟨w,h.reduced.1 hw⟩ hw)
  let : IsElementaryAbelian 2 A0 := hAf.2.1
  have hEA : IsElementaryTwo Aq := ⟨hne,IsElementaryAbelian.map q⟩
  have hUS : U ≤ (S : Subgroup J) := h.reduced_internal.le_pCore.trans
    (pCore_isPGroup.le_sylow_of_normal S)
  have hnear := ChapterB.near_maximum_action_codimension (S : Subgroup J) U hUS q hq hk hAf hne
  obtain ⟨hsource,⟨M⟩⟩ := h.hermitian_original_source hm
  have hcases := FourOffender.marked_near_offender_cases hsource M hs Aq hEA hnear
  obtain ⟨_,t,ht2,htB,ht,hgen⟩ :=
    FourOffender.marked_near_offender_generated_by_transvections hsource M hs Aq hEA hnear
  exact ⟨hcases.1,hcases.2.1,hcases.2.2.1,hcases.2.2.2,M,t,ht2,htB,ht,hgen⟩

/-- Away from half-degree two, the original first Thompson subgroup fixes
the whole Hermitian module. This is deduced from its actual rank-indexed
elementary generators, without assuming a bound on their quotient ranks. -/
theorem Input.hermitian_thompson_one_centralizes_of_half_degree_ne_two
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s))
    (hs : 1 < s) (hs2 : s ≠ 2) :
    ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (W : Set G) := by
  apply sSup_le
  intro A hA
  by_contra hn
  exact hs2 (h.hermitian_original_near_maximum hm hs A hA hn).1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
