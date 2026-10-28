module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointMultiplicity
public import Theory.GroupTheory.CentralizerFactorProjection
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.ReducedNumericalSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic

/-!
# The original point-quotient centralizer bound

Seed rigidity shows that the whole local quotient acts by inner automorphisms
on its normal natural factor. The factor is the literal image of L₁ and is
centerless, so the quotient splits over its actual centralizer C. Projection
onto C is surjective on the original escaping minimal parabolic H₁, since
J = L₁ H₁. The nontrivial reduced image C is therefore a minimal parabolic
and retains H₁ as an actual SQTK cover.

The faithful multiplicity action and the same original F.9 actor from
PointMultiplicity now contradict B.6.9(1). Consequently the original kernel
D = C_{G₁}(K₁/O₂(K₁)) lies in N_G(L), in both degrees four and five. No
invariant individual natural summand or chief-factor bound is assumed.
The source K₁T membership and plane-centralizer bound remain separate steps.

Source: Aschbacher--Smith 12.9.5, Case I, pp.860--861, using 12.8.5(1)
and B.6.9(1), refs/quasithin.pdf. All quotient maps and the flag are original.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Split the literal local quotient over its natural-image centralizer. -/
theorem normal_local_centralizer_projection
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) {J : Subgroup G}
    (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    [((F.Li L 1).subgroupOf J).Normal] :
    ∃ π : (J ⧸ pCore 2 J) →* localNaturalCentralizer F L J,
      Function.Surjective π ∧
      π.ker = ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ∧
      ∀ c : localNaturalCentralizer F L J, π c.val = c := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn3 : 3 < n := by rcases hn with rfl | rfl <;> decide
  have hn5 : n ≤ 5 := by rcases hn with rfl | rfl <;> decide
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient hn3.le L h.chosen.normalizes h.naturalMarking
  let A := (F.Li L 1).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := A.map q
  let b := subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)
  let e : (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) ≃* N :=
    (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans
      (coreQuotientEquivImage 2 A)
  have hem (k : F.Li L 1) :
      (e (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k) : J ⧸ pCore 2 J) =
        q (inclusion (F.Li_one_le_of_mem_Hz hJ) k) := by
    exact (congrArg (fun z => ((coreQuotientEquivImage 2 A) z : J ⧸ pCore 2 J))
      (QuotientGroup.congr_mk' _ _ b.symm (pCore_map_iso 2 b.symm) k)).trans
        (coreQuotientEquivImage_apply_mk 2 A (b.symm k))
  let m := (BinaryLinear.OuterCyclic.slEquivLinear (n-1)).trans
    ((D.fullQuotientEquiv hn3).symm.trans e)
  have hcN : center N = ⊥ := by
    apply bot_unique
    intro z hz
    have hh : m.symm z ∈ center _ := by
      rw [mem_center_iff]
      intro x
      apply m.injective
      simpa only [map_mul,m.apply_symm_apply] using mem_center_iff.mp hz (m x)
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega)] at hh
    exact m.symm.injective (hh.trans m.symm.map_one.symm)
  have hdis : Disjoint N (centralizer (N : Set (J ⧸ pCore 2 J))) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz : (⟨x,hx.1⟩ : N) ∈ center N := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hx.2 y y.property)
    rw [hcN] at hz
    exact congrArg Subtype.val hz
  apply centralizer_projection_of_inner N hdis
  intro x
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) x
  let hJK := F.normalizes_Li_one_of_relative_normal hJ
  obtain ⟨c,hc⟩ := D.seed_intertwiners_of_gt_three hn3 hn5 J hJ.2.1
    (F.sylow_le_of_mem_Hz hJ) hJK j
  obtain ⟨g,hg⟩ := D.modelConjugation_inner_of_intertwiner hn3 J hJK j c hc
  let z := e ((D.fullQuotientEquiv hn3).symm g)
  have he (k : F.Li L 1) :
      q j * (e (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k) : J ⧸ pCore 2 J) * (q j)⁻¹ =
      (z : J ⧸ pCore 2 J) * e (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k) * (z : J ⧸ pCore 2 J)⁻¹ := by
    have ha := D.modelConjugation_actor hn3 J hJK j k
    rw [←hg] at ha
    have hfull (a : F.Li L 1) : D.fullQuotientEquiv hn3
        (QuotientGroup.mk' (pCore 2 (F.Li L 1)) a) = D.naturalActor a := by
      simp [NaturalSeedMarking.fullQuotientEquiv,NaturalSeedMarking.naturalActor]
      rfl
    have ha' : QuotientGroup.mk' (pCore 2 (F.Li L 1)) (F.localConjugation L J hJK j k) =
        (D.fullQuotientEquiv hn3).symm g * QuotientGroup.mk' (pCore 2 (F.Li L 1)) k *
          ((D.fullQuotientEquiv hn3).symm g)⁻¹ := by
      apply (D.fullQuotientEquiv hn3).injective
      rw [map_mul,map_mul,map_inv,MulEquiv.apply_symm_apply,hfull,hfull]
      exact ha.symm
    have hh₀ := congrArg e ha'
    rw [e.map_mul,e.map_mul,e.map_inv] at hh₀
    have hh := congrArg (fun a : N => (a : J ⧸ pCore 2 J)) hh₀
    change (e (QuotientGroup.mk' (pCore 2 (F.Li L 1))
      (F.localConjugation L J hJK j k)) : J ⧸ pCore 2 J) =
      (z : J ⧸ pCore 2 J) * e (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k) * (z : J ⧸ pCore 2 J)⁻¹ at hh
    simp only [hem] at hh
    rw [hem]
    exact (show q j * q (inclusion (F.Li_one_le_of_mem_Hz hJ) k) * (q j)⁻¹ =
      q (inclusion (F.Li_one_le_of_mem_Hz hJ) (F.localConjugation L J hJK j k)) from
        by rw [←map_inv,←map_mul,←map_mul]; rfl).trans hh
  refine ⟨z,?_⟩
  intro y hy
  -- The two conjugations agree, so their quotient centralizes N.
  have hzinv : z.val⁻¹ * y * z.val ∈ N :=
    N.mul_mem (N.mul_mem (N.inv_mem z.property) hy) z.property
  obtain ⟨k,hk⟩ := e.surjective ⟨z.val⁻¹ * y * z.val,hzinv⟩
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) k
  have hlast := he k
  rw [congrArg Subtype.val hk] at hlast
  have hcomm : (q j * z.val⁻¹) * y * (q j * z.val⁻¹)⁻¹ = y := by
    calc
      _ = q j * (z.val⁻¹ * y * z.val) * (q j)⁻¹ := by group
      _ = z.val * (z.val⁻¹ * y * z.val) * z.val⁻¹ := hlast
      _ = y := by group
  exact (mul_inv_eq_iff_eq_mul.mp hcomm).symm

/-- Source 12.9.5(1): the original point-quotient centralizer lies in M. -/
theorem point_quotient_centralizer_le_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (C₁ : ComponentGeometry F L) :
    pointQuotientCentralizer C₁ ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨H₁,hstar,hmin,hr,hJ,hN,hU,a,ha,B,hBR,hBH,hB,hquad,hbound,hBC,hRC,
    hcore,α,hα,hker,r,hrpos,e,he,μ,hμ,heμ,hcost,hstrong,hμquad⟩ :=
      point_centralizer_escape_strong_multiplicity h hn earlier F hab C₁ hout
  let J := F.Li L 1 ⊔ H₁
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := localNaturalCentralizer F L J
  let := hN
  let := hU
  obtain ⟨π,hπ,hπker,hπfix⟩ := normal_local_centralizer_projection h hn F hJ
  let f : H₁ →* C := π.comp (q.comp (inclusion (show H₁ ≤ J from le_sup_right)))
  have hf : Function.Surjective f := by
    let φ := π.comp q
    have hφ : Function.Surjective φ := hπ.comp (QuotientGroup.mk'_surjective _)
    have hLker : (F.Li L 1).subgroupOf J ≤ φ.ker := by
      intro k hk
      change q k ∈ π.ker
      rw [hπker]
      exact mem_map_of_mem q hk
    have hm : (H₁.subgroupOf J).map φ = ⊤ := by
      have hh := congrArg (Subgroup.map φ) (codisjoint_subgroupOf_sup (F.Li L 1) H₁).eq_top
      have hz : ((F.Li L 1).subgroupOf J).map φ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hLker
      rw [Subgroup.map_sup,map_top_of_surjective φ hφ] at hh
      change ((F.Li L 1).subgroupOf J).map φ ⊔ (H₁.subgroupOf J).map φ = ⊤ at hh
      simpa only [hz,bot_sup_eq] using hh
    intro c
    obtain ⟨j,hj,hjc⟩ := (show c ∈ (H₁.subgroupOf J).map φ from hm ▸ mem_top c)
    exact ⟨⟨j,hj⟩,hjc⟩
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple H₁ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show H₁ ≤ F.H from le_sup_right.trans hJ.2.1))).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Components.Gi_twoLocal h F 1 (by decide))).subgroup _)
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple C := {
    Cover := H₁
    kernel := f.ker
    sqtk := hsqtk
    equiv := QuotientGroup.quotientKerEquivOfSurjective f hf }
  obtain ⟨M,hM,_⟩ := hmin.1.2
  have hmin' := (ChapterB.intrinsic_minimalParabolic T H₁ M hmin hM.1 hM.2).1
  have hne : f.ker ≠ ⊤ := by
    intro ht
    have hall (c : C) : c = 1 := by
      obtain ⟨g,rfl⟩ := hf c
      exact (show g ∈ f.ker from ht ▸ mem_top g)
    exact hstrong.1.1 (bot_unique (fun c _ => hall c))
  have hminC := (ChapterB.minimalParabolic_reduced_image
    (T.subtype (hM.1.trans hM.2.le)) hmin' f hf hcore hne).2
  exact (ChapterB.reduced_minimalParabolic_not_strong ⟨cover⟩ _ hminC hcore μ hμ)
    ⟨_,hstrong⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
