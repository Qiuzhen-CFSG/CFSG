module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearResidualNonnatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PairedIndexGeometry

/-!
# Reusing the original linear residual exclusion for a second critical actor

The original failure in 8.3 supplies a full residual representation with no
natural alternative. Every critical configuration ending at that same vertex
has a quadratic opposite-neighborhood actor on that representation. Corrected
5.12 therefore gives its square bound without a new failure hypothesis.
The critical-center fixed-space comparison and original core products then
give the paired estimate. The reverse configuration is first translated to
the same endpoint before this theorem is applied.

Source: DGS85, Groups and Graphs, (8.3)(2), p.136.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem index_product (U Q K : Subgroup G) (h : U ⊓ Q ≤ K) :
    K.relIndex U * Q.relIndex (U ⊓ K) = Q.relIndex U := by
  rw [Nat.mul_comm,inf_comm U K,relIndex_inf_mul_relIndex]
  rw [←inf_relIndex_right (Q ⊓ K) U,←inf_relIndex_right Q U]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,h ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩

private theorem elementary_index_of_rank (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v)
    (n : ℕ) (hr : primeRank 2 (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≤ n) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex L
    (Q (family P) v) A q (local_quotient_kernel (family P) d v (MulEquiv.refl _)) hAL
  exact hi ▸ (primeRank_le_iff_elementary_card_le _).mp hr _ inferInstance

private theorem elementary_index_at_same_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type) (n : ℕ)
    (hr : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ n)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  let e := MulAut.conj g
  let E := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEL : E ≤ d.localGroup (g • v) := by rw [d.conjugate]; exact map_mono hAL
  have hh := elementary_index_of_rank h d (g • v) E hEL n hr
  rw [Q_translate,relIndex_map_map_of_injective _ _ e.injective] at hh
  exact hh

private theorem bool_eq_of_ne (a b c : Bool) (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem reduced_counterexample_linear_uniform_paired_square
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K))
    {x gamma : Vertex (Reduction.reducedFamily J S₀)}
    (hxc : IsCriticalPair (Reduction.reducedFamily J S₀) x a')
    (hxg : (graph (Reduction.reducedFamily J S₀)).Adj x gamma)
    (hgd : (graph (Reduction.reducedFamily J S₀)).dist gamma a' + 1 = b (Reduction.reducedFamily J S₀))
    (hxcomm : ⁅Z (Reduction.reducedFamily J S₀) x,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (m : ℕ) (hm2 : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m)) :
    let F := Reduction.reducedFamily J S₀
    Nat.pow ((Q F a').relIndex (V F gamma 1)) 2 ≤ (Q F gamma).relIndex (V F a' 1) * 2^m := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  obtain ⟨hb2,hDL,eD,σ,S,T₀,heD,hact,_,_,hgen,hres,hfaith,⟨c⟩,hnatural⟩ :=
    reduced_counterexample_linear_residual_nonnatural h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2 L
  let W := FixedQuotient U (pResidual 2 L)
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDL) (inclusion_injective _)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x : V F a' 1 => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : Finite (graphLocalGroup F w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hrank : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ m := by
    change primeRank 2 (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≤ m
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e]
      exact (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le

  let π := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  let A := ((V F gamma 1).subgroupOf D).map π
  have hAD : V F gamma 1 ≤ D := source_critical_actor_le_residual_join ht
    (Reduction.reduced_borel_core_sylow h) d hxc hxg hgd hb hxcomm w R hR
  let : IsElementaryAbelian 2 (V F gamma 1) := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) hb2 gamma
  let : IsElementaryAbelian 2 ((V F gamma 1).subgroupOf D) := IsElementaryAbelian.subgroupOf hAD
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map π
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hgenT : GeneratedByFixedSpace σ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,K) T₀ T
    exact generatedByFixedSpace_of_equivariant_surjection σ σ
      (MulAut.conj g).toMonoidHom (σ g)
      (fun z => ⟨σ g⁻¹ z,σ.self_inv_apply g z⟩)
      (by intro x z; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,σ.inv_self_apply]) T₀ hgen

  have hker : π.ker = (Q F a').subgroupOf D := by
    ext g
    change π g = 1 ↔ (g : Reduction.G₀ J S₀) ∈ Q F a'
    change eD (QuotientGroup.mk' (pCore 2 D) g) = 1 ↔ _
    rw [heD g,e.map_eq_one_iff]
    change inclusion hDL g ∈ (QuotientGroup.mk' (pCore 2 L)).ker ↔ _
    rw [QuotientGroup.ker_mk']
    have hQL : (pCore 2 L).map L.subtype = Q F a' := graphLocalGroup_core ht a'
    rw [←hQL]
    exact ⟨fun hg => mem_map_of_mem L.subtype hg,fun hg => by
      obtain ⟨l,hl,he⟩ := hg
      exact (show l = inclusion hDL g from Subtype.ext he) ▸ hl⟩
  have hcard : Nat.card A = (Q F a').relIndex (V F gamma 1) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex D (Q F a') (V F gamma 1) π hker hAD
  let a₁ := (Q F a').relIndex (V F gamma 1)
  let a₂ := (Q F gamma).relIndex (V F a' 1)
  have ha₂ : 0 < a₂ := Nat.pos_of_ne_zero (((Q F gamma).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  by_cases hsmall : a₁ ≤ 2
  · have hq4 : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm2
    change a₁^2 ≤ a₂ * 2^m
    nlinarith
  obtain ⟨_,_,_,_,hquad,_,_⟩ := reduced_ending_residual_actor h hob models hxc hxg hgd hb hxcomm w
  have hquadA : IsQuadratic σ A := by
    rintro x ⟨g,hg,rfl⟩ y ⟨k,hk,rfl⟩ z
    change σ (π g) (σ (π k) z - z) = σ (π k) z - z
    rw [hact g,hact k]
    exact hquad (inclusion hDL g) hg (inclusion hDL k) hk z
  have hfix : fixedSpace σ ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone σ le_top).trans hres.le)
  have hlower : a₁^2 ≤ Nat.card (W ⧸ fixedSpace σ A) := by
    by_contra! hs
    change Nat.card (W ⧸ fixedSpace σ A) < ((Q F a').relIndex (V F gamma 1))^2 at hs
    rw [←hcard] at hs
    exact hnatural T (sl2_strict_actor_natural σ hfaith T A hAT hquadA hgenT hfix hK hs)
  let A₀ := ((Z F x).subgroupOf D).map π
  have hZV : Z F x ≤ V F gamma 1 := Z_neighbor_le_V F hxg.symm
  have hZD : Z F x ≤ D := hZV.trans hAD
  have hA₀A : A₀ ≤ A := map_mono (comap_mono hZV)
  have hA4 : 4 ≤ Nat.card A := by
    obtain ⟨r,hr⟩ := (T.isPGroup'.to_le hAT).exists_card_eq
    change Nat.card A = 2^r at hr
    have hbig : 2 < Nat.card A := by
      rw [hcard]
      exact Nat.lt_of_not_ge hsmall
    have hr2 : 2 ≤ r := by
      by_contra! hh
      have hh' : r = 0 ∨ r = 1 := by omega
      rcases hh' with rfl | rfl <;> simp only [pow_zero,pow_one] at hr <;> omega
    rw [hr]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hr2
  have hA₀ : A₀ ≠ ⊥ := by
    intro hz
    have hk := (Subgroup.map_eq_bot_iff _).mp hz
    apply hxc.2
    apply le_trans ?_ (source_Z_Q_U ht a').2
    intro z hz
    have hzero : (⟨z,hZD hz⟩ : D) ∈ π.ker := hk hz
    rw [hker] at hzero
    exact hzero
  obtain ⟨t,ht₀,ht1⟩ := A₀.bot_or_exists_ne_one.resolve_left hA₀
  have hgenA : GeneratedByFixedSpace σ A := by
    apply top_unique
    rw [←hgenT]
    apply iSup_mono
    intro g
    exact Submodule.map_mono (fixedSpace_antitone σ hAT)
  have hfixed : fixedSpace σ A = fixedSpace σ A₀ := by
    apply le_antisymm (fixedSpace_antitone σ hA₀A)
    exact (fixedSpace_antitone σ (zpowers_le.mpr ht₀)).trans_eq
      (sl2_quadratic_fixedSpace_eq σ (by omega : 0 < n) hK T A hAT hA4 hquadA hgenA t (hA₀A ht₀) ht1).symm
  have hcentral := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index σ π c (Z F x)
  change Nat.card (W ⧸ fixedSpace σ A₀) ≤ _ at hcentral
  have hQx : Q F x ≤ centralizer (Z F x : Set (Reduction.G₀ J S₀)) :=
    le_centralizer_iff.mp (Z_centralizes_Q F x (source_Z_Q_U ht x).1)
  have hind := relIndex_le_of_le_left hQx (((Q F x).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  have htot : a₁^2 ≤ (Q F x).relIndex (V F a' 1) := by
    rw [hfixed] at hlower
    exact hlower.trans (hcentral.trans hind)
  let A₂ := V F a' 1 ⊓ Q F gamma
  let : IsElementaryAbelian 2 (V F a' 1) := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow hb2 a'
  let : IsElementaryAbelian 2 A₂ := IsElementaryAbelian.of_le inf_le_left
  have hAL : A₂ ≤ d.localGroup x := pGroup_le_localGroup F d x A₂
    (IsElementaryAbelian.isPGroup 2 A₂)
    (inf_le_right.trans ((source_Z_Q_U ht gamma).2.trans
      ((ballKernel_one_le_edge F hxg.symm).trans inf_le_right)))
  have hxtype : x.type = w.val.type := by
    have hodd := (source_critical_geometry ht d hxc hxg hgd hb hxcomm).1
    have hne : x.type ≠ a'.type := by
      intro he
      have heven := (even_dist_iff F ht.generate x a').mpr he
      rw [hxc.1] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    exact bool_eq_of_ne x.type w.val.type a'.type hne w.property.1.symm
  have hsecondary := elementary_index_at_same_type ht d hxtype m hrank A₂ hAL
  have hprod := index_product (V F a' 1) (Q F x) (Q F gamma)
    (source_reverse_core_intersection ht (Reduction.reduced_borel_core_sylow h) d hxc hxg hgd hb hxcomm (models gamma))
  rw [←hprod] at htot
  exact htot.trans (Nat.mul_le_mul_left _ hsecondary)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
