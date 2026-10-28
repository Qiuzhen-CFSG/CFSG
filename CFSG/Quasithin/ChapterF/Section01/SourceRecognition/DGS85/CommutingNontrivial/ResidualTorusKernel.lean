module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualTorus
public import Theory.Representation.CyclicRegularVector
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.ElementaryPerfectSplit

/-!
# A nonidentity torus element centralizes the quotient omega-center

The actual cyclic residual torus acts on the moving omega-preimage modulo
the original moving core. This quotient is identified with the original
quotient Sylow omega-center, so its cardinality is bounded by the unitary
binary rank. A cyclic linear group has a vector detecting its entire
kernel, hence its faithful order cannot exceed the module's cardinality.
The proved field-square inequality makes the torus too large to act
faithfully. Its nonidentity kernel element therefore has displacement in
the original core, which centralizes the moving seed.

The reduced F1.11 application constructs every order and action premise
from the strict residual comparison. It retains the full edge and both
original core maps. No extra torus-action assumption is imposed.
Source: DGS, *Groups and Graphs* (1985), proof of (8.3), p.136.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The torus acts on the literal quotient omega-center, and an order
larger than that section forces a nontrivial kernel element. -/
theorem source_cyclic_omega_kernel (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (w : Vertex (family P))
    (R : Sylow 2 (d.localGroup w)) (C : Subgroup G) [IsCyclic C]
    (hC : C ≤ stabilizer (family P) w)
    (hCY : C ≤ normalizer (quotientSylowOmegaPreimage (d.localGroup w) R : Set G))
    (m : ℕ) (hr : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ m)
    (hlarge : 2^m < Nat.card C) :
    ∃ c ∈ C, c ≠ 1 ∧ ⁅zpowers c,quotientSylowOmegaPreimage (d.localGroup w) R⁆ ≤ Q (family P) w := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w
  let Y := quotientSylowOmegaPreimage L R
  let N := (Q F w).subgroupOf Y
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Finite L := Finite.of_injective (inclusion (d.local_le w)) (inclusion_injective _)
  let S := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let O := omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L))
  have hYL : Y ≤ L := map_subtype_le _
  let : Finite Y := Finite.of_injective (inclusion hYL) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion hC) (inclusion_injective _)
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((hYL.trans (d.local_le w)).trans (stabilizer_normalizes_Q F w))
  let f := q.comp (inclusion hYL)
  have hker : f.ker = N := by
    ext y
    change inclusion hYL y ∈ (QuotientGroup.mk' (pCore 2 L)).ker ↔ (y : G) ∈ Q F w
    rw [QuotientGroup.ker_mk',←localGroup_core_eq F d w]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hrange : f.range = O := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact quotientSylowOmegaPreimage_image L R
  let e : (Y ⧸ N) ≃* O :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  let : IsElementaryAbelian 2 (Y ⧸ N) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action C Y (Q F w) hCY
    (hC.trans (stabilizer_normalizes_Q F w)) inferInstance
  let τ := elementaryRepresentation (p := 2) ρ
  have hcard : Nat.card (Additive (Y ⧸ N)) ≤ 2^m := by
    rw [Nat.card_congr (Additive.toMul : Additive (Y ⧸ N) ≃ (Y ⧸ N)),Nat.card_congr e.toEquiv]
    exact (primeRank_le_iff_elementary_card_le _).mp hr O inferInstance
  obtain ⟨c,hc,htriv⟩ := exists_cyclic_kernel_of_card_lt τ (hcard.trans_lt hlarge)
  refine ⟨c,c.property,fun he => hc (Subtype.ext he),?_⟩
  have hcρ : ρ c = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (DFunLike.congr_fun htriv (Additive.ofMul x))
  have hcy : zpowers (c : G) ≤ ρ.ker.map C.subtype :=
    zpowers_le.mpr (mem_map_of_mem C.subtype (show c ∈ ρ.ker from hcρ))
  apply (commutator_mono hcy le_rfl).trans
  apply commutator_le.mpr
  rintro _ ⟨k,hk,rfl⟩ y hy
  change ⁅(k : G),y⁆ ∈ Q F w
  have he := hρ k ⟨y,hy⟩
  rw [show ρ k = 1 from hk] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he.symm
  change (k : G) * y * (k : G)⁻¹ / y ∈ Q F w at hh
  simpa only [commutatorElement_def,div_eq_mul_inv] using hh

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- On the original strict-comparison branch, a nonidentity element of the
actual residual torus centralizes the moving quotient omega-center. -/
theorem reduced_strict_linear_residual_torus_kernel
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
    (hstrict : (centralizer (V (Reduction.reducedFamily J S₀) beta 1 : Set (Reduction.G₀ J S₀))).relIndex
      (V (Reduction.reducedFamily J S₀) a' 1) <
      Nat.pow ((Q (Reduction.reducedFamily J S₀) a').relIndex (V (Reduction.reducedFamily J S₀) beta 1)) 2)
    (m : ℕ) (hm2 : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F a'
    let D := (pResidual 2 L).map L.subtype ⊔ Q F w.val
    ∃ C : Subgroup (Reduction.G₀ J S₀), C ≤ D ∧
      C ≤ stabilizer F a' ⊓ stabilizer F w.val ∧
      IsCyclic C ∧ Nat.card C = 2^n - 1 ∧ Odd (Nat.card C) ∧ Disjoint C (Q F a') ∧
      ∃ c ∈ C, c ≠ 1 ∧
        ⁅zpowers c,quotientSylowOmegaPreimage (graphLocalGroup F w.val) R⁆ ≤ Q F w.val := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite (d.localGroup w.val) :=
    Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite (graphLocalGroup F w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hr : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ m := by
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
  obtain ⟨C,hCD,hCe,hCY,hcy,hcard,hodd,hdis⟩ :=
    reduced_counterexample_linear_edge_torus h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  let := hcy
  have hbound := reduced_strict_linear_residual_unitary_field_bound h hob models
    hc hab hd hb hcomm w hm R hR hbad hn hK e hstrict m hm2 hu
  have hq : 1 < 2^m := Nat.one_lt_pow (by omega) (by decide)
  have hlarge : 2^m < Nat.card C := by
    rw [hcard]
    have hs := Nat.sub_add_cancel (Nat.one_le_two_pow (n := n))
    nlinarith
  obtain ⟨c,hcC,hc1,hcY⟩ := source_cyclic_omega_kernel ht d w.val R C
    (hCe.trans inf_le_right) hCY m hr hlarge
  exact ⟨C,hCD,hCe,hcy,hcard,hodd,hdis,c,hcC,hc1,hcY⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
