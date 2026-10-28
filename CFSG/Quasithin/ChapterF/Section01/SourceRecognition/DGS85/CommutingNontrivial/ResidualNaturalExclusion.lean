module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualTorusKernel
public import Theory.Representation.BinaryConjugationSection.CyclicCentralizerExclusion
public import Theory.SpecificGroups.SL2.OddFixedVectors

/-!
# Excluding the natural residual alternative in DGS 8.3

On the large-field linear ending branch, corrected 5.12 turns a strict
square inequality for the full residual quotient into natural coordinates.
The unitary moving seed then gives q_lambda² ≤ q_alpha'. The cyclic torus
of order q_alpha'−1 has a nonidentity element centralizing the actual
quotient omega-center. Its displacement on that preimage lies in Q_lambda,
which centralizes Z_lambda. The torus also centralizes the residual fixed
denominator. The three-subgroup lemma and coprime fixed/moved decomposition
force the whole moving seed to centralize the omega-preimage, contradicting
the original nonzero intersection commutator.

The main export retains the literal residual quotient action, both quotient
maps and a bound on its fixed-space quotient. The second export applies
that bound to the original centralizer index. The argument works with an
arbitrary critical orientation of the reduced F1.11 graph. The nonlinear
ending rows and the paired upper estimates are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (8.3), p.136, the natural-module exclusion before inequality (2).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The full original residual section satisfies the square lower bound.
Its natural alternative is excluded using the actual residual torus action;
no naturality or torus-kernel premise is required from source assembly. -/
theorem reduced_counterexample_linear_residual_fixed_square
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
 :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F a'
    let U := (V F a' 1).subgroupOf L
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q F w.val
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F a' L (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 L
      ∃ (hDL : D ≤ L) (eD : (D ⧸ pCore 2 D) ≃* SL(2,K))
        (σ : Representation (ZMod 2) SL(2,K) (FixedQuotient U (pResidual 2 L))),
        let π := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
        let A := ((V F beta 1).subgroupOf D).map π
        (∀ g : D, eD (QuotientGroup.mk' (pCore 2 D) g) =
          e (QuotientGroup.mk' (pCore 2 L) (inclusion hDL g))) ∧
        (∀ g : D, σ (π g) = fixedQuotientAction U (pResidual 2 L) (inclusion hDL g)) ∧
        Nonempty (BinaryConjugationSection D (V F a' 1)
          (V F a' 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀))) (σ.comp π)) ∧
        Nat.pow ((Q F a').relIndex (V F beta 1)) 2 ≤
          Nat.card (FixedQuotient U (pResidual 2 L) ⧸ fixedSpace σ A) ∧
        Nat.card (FixedQuotient U (pResidual 2 L) ⧸ fixedSpace σ A) ≤
          (centralizer (V F beta 1 : Set (Reduction.G₀ J S₀))).relIndex (V F a' 1) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  obtain ⟨hb2,_,hDL,eD,σ,S,T,heD,hact,hS,hT,hgen,hres,_,⟨c⟩⟩ :=
    reduced_counterexample_linear_residual_prepared h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2 L
  let W := FixedQuotient U (pResidual 2 L)
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDL) (inclusion_injective _)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x : V F a' 1 => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨_,hDL',eD',τ,T',heD',hact',_,_,_,_,_,_,_,hupper,hnat⟩ :=
    reduced_counterexample_linear_residual_recognition h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  have heq : eD = eD' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) x
    exact (heD g).trans (heD' g).symm
  have hσ : σ = τ := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro z
    obtain ⟨g,rfl⟩ := (eD.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 D))) x
    change σ (eD (QuotientGroup.mk' (pCore 2 D) g)) z = τ (eD (QuotientGroup.mk' (pCore 2 D) g)) z
    rw [hact,heq]
    exact (congrArg (fun f => f z) (hact' g)).symm
  rw [←heq,←hσ] at hupper hnat
  refine ⟨hb2,hDL,eD,σ,heD,hact,⟨c⟩,?_,hupper⟩
  by_contra! hstrict
  obtain ⟨hnatural,C,hCnat⟩ := hnat hstrict
  have hq : IsQuadratic σ T := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,K) T' T
    rw [←hg]
    exact SL2SylowFixedRecognition.quadratic_conjugate σ hnatural.2.2 g
  have hfix : fixedSpace σ ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone σ le_top).trans hres.le)
  have hnatural (g : SL(2,K)) (z : W) : C (σ g z) = Matrix.mulVec g.val (C z) := by
    exact hCnat g z
  have hescape := core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm)
  obtain ⟨m,hm2,hu⟩ := (source_moving_omega_commutator_or_large_unitary ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm R hR).resolve_left hbad
  have hbound := (source_natural_residual_seed_bound ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm hescape R hR eD σ c S T hS hT hq hgen hfix C).2 m hm2 hu
  let : Finite (graphLocalGroup F w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (d.localGroup w.val) :=
    Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  have hrank : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ m := by
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
  obtain ⟨C₀,hC₀D,hC₀e,hC₀Y,hcy,hcard,hodd,hdis⟩ :=
    reduced_counterexample_linear_edge_torus h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  have hlarge : 2^m < Nat.card C₀ := by
    rw [hcard]
    rw [hK] at hbound
    have hs := Nat.sub_add_cancel (Nat.one_le_two_pow (n := n))
    have hm1 : 1 < 2^m := Nat.one_lt_pow (by omega) (by decide)
    nlinarith
  let := hcy
  obtain ⟨k,hk,hk1,hkY⟩ := source_cyclic_omega_kernel ht d w.val R C₀
    (hC₀e.trans inf_le_right) hC₀Y m hrank hlarge
  let : IsCyclic C₀ := hcy
  let : Finite C₀ := Finite.of_injective (inclusion hC₀D) (inclusion_injective _)
  let Y := quotientSylowOmegaPreimage (graphLocalGroup F w.val) R
  let ZW := Z F w.val
  let N := V F a' 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀))
  let A := V F beta 1 ⊓ Q F a'
  let Bk := zpowers k
  have hBkC : Bk ≤ C₀ := zpowers_le.mpr hk
  have hBkD : Bk ≤ D := hBkC.trans hC₀D
  let : Finite Bk := Finite.of_injective (inclusion hBkC) (inclusion_injective _)
  let : IsElementaryAbelian 2 ZW := CommutingOneProfile.source_center_elementary ht w.val
  let : Finite ZW := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  have hYeq := source_counterexample_residual_edge_eq_omega ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm hescape R hR hbad
  change (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype ⊓ D = Y at hYeq
  have hYD : Y ≤ D := hYeq ▸ (show (R : Subgroup (graphLocalGroup F w.val)).map
    (graphLocalGroup F w.val).subtype ⊓ D ≤ D from inf_le_right)
  have hZN : ZW ⊓ N ≤ centralizer (D : Set (Reduction.G₀ J S₀)) := by
    apply le_centralizer_iff.mpr
    exact sup_le
      (le_centralizer_iff.mp (inf_le_right.trans inf_le_right))
      ((le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U ht w.val).1)).trans
        (centralizer_le inf_le_left))
  have hYZ : ⁅Y,ZW⁆ ≤ ZW ⊓ N := by
    have he := source_omega_displacement_residual_fixed ht (Reduction.reduced_borel_core_sylow h)
      d hc hab hd hb hcomm models w hm hescape R hR
    exact le_inf (he.trans inf_le_left)
      (le_inf ((he.trans inf_le_left).trans (Z_neighbor_le_V F w.property)) (he.trans inf_le_right))
  have hQZ : Q F w.val ≤ centralizer (ZW : Set (Reduction.G₀ J S₀)) :=
    le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U ht w.val).1)
  let π := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  let kD : D := ⟨k,hC₀D hk⟩
  have hπ1 : π kD ≠ 1 := by
    intro he
    have he' := (heD kD).symm.trans he
    have hkq : inclusion hDL kD ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he')
    have hkQ : k ∈ Q F a' := by
      have hcore : (pCore 2 L).map L.subtype = Q F a' := graphLocalGroup_core ht a'
      rw [←hcore]
      exact mem_map_of_mem L.subtype hkq
    exact hk1 (disjoint_def.mp hdis hk hkQ)
  have hkpow : k^Nat.card C₀ = 1 :=
    congrArg (fun x : C₀ => (x : Reduction.G₀ J S₀)) (pow_card_eq_one' (x := (⟨k,hk⟩ : C₀)))
  have hπpow : π kD ^ Nat.card C₀ = 1 := by
    rw [←map_pow]
    have he : kD ^ Nat.card C₀ = 1 := Subtype.ext hkpow
    rw [he,map_one]
  have hfree (z : W) : σ (π kD) z = z → z = 0 := by
    intro hz
    have hf := Matrix.SL2.odd_power_fixed_eq_zero (π kD) (Nat.card C₀) hodd hπpow hπ1 (C z)
      ((hnatural _ _).symm.trans (congrArg C hz))
    exact C.injective (hf.trans (map_zero C).symm)
  have hBkodd : Odd (Nat.card Bk) :=
    hodd.of_dvd_nat ((card_dvd_of_le hBkC))
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 ZW).exists_card_eq
  have hcop : Nat.Coprime (Nat.card Bk) (Nat.card ZW) := by
    rw [hr]
    exact hBkodd.coprime_two_right.pow_right r
  have hzero : ⁅Y,ZW⁆ = ⊥ := c.commutator_eq_bot_of_coprime_fixedFree_section ZW Y Bk
    (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop
    (Z_neighbor_le_V F w.property)
    ((hBkC.trans (hC₀e.trans inf_le_right)).trans (stabilizer_normalizes_Z F w.val))
    (hZN.trans (centralizer_le hBkD)) (hZN.trans (centralizer_le hYD)) hYZ
    (hkY.trans hQZ) kD (mem_zpowers k) hfree
  have hAD : A ≤ D := inf_le_left.trans
    (source_critical_actor_le_residual_join ht (Reduction.reduced_borel_core_sylow h)
      d hc hab hd hb hcomm w R hR)
  have hAT : A ≤ (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype := by
    rw [hR]
    have he : Q F a' ≤ (stabilizer F a' ⊓ stabilizer F w.val).pCoreIn 2 :=
      Noncommuting.graph_Q_le_edgeCore ht w.property
    rw [inf_comm] at he
    exact inf_le_right.trans he
  have hAY : A ≤ Y := (le_inf hAT hAD).trans_eq hYeq
  exact hm (bot_unique ((commutator_mono hAY le_rfl).trans hzero.le))

/-- The exact residual-section estimate also bounds the original
centralizer index, through the proved quotient-to-original inequality. -/
theorem reduced_counterexample_linear_residual_square
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
 :
    Nat.pow ((Q (Reduction.reducedFamily J S₀) a').relIndex (V (Reduction.reducedFamily J S₀) beta 1)) 2 ≤
      (centralizer (V (Reduction.reducedFamily J S₀) beta 1 : Set (Reduction.G₀ J S₀))).relIndex
        (V (Reduction.reducedFamily J S₀) a' 1) := by
  obtain ⟨_,_,_,_,_,_,_,hl,hu⟩ :=
    reduced_counterexample_linear_residual_fixed_square h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  exact hl.trans hu

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
