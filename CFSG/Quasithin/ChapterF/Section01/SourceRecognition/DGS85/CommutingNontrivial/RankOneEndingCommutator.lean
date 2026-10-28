module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryComparisonApplication

/-!
# DGS 8.3 for the binary ending models

The two opposite neighborhood actors are elementary and lie in their
respective original local groups. Parity places the two ending vertices
in the same orbit. Conjugating the literal quotient maps therefore bounds
both actor indices by the binary rank of the ending local quotient.

At rank one both indices are at most two. A counterexample to 8.3 forces
a moving unitary field of order at least four, so both paired square
inequalities follow immediately. The proved terminal comparison rules out
that counterexample. The reduced application supplies the actual moving
neighbor and full-edge Sylow, as well as reciprocal escape.

The final export discharges the rank premise for the actual PSL₂(2),
Sz(2), PSU₃(2), and SU₃(2) carriers. PSL₂(2) is transported to SL₂(2);
the small Suzuki Sylow is cyclic, and the special-unitary rank calculation
retains its odd scalar kernel. The original earlier-source obstruction and
full quotient catalogue remain explicit, with arbitrary critical orientation.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (8.3), pp.135--137, the paired comparisons and terminal argument.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem elementary_index_same_orbit (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type) (n : ℕ)
    (hr : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ n)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  let f := MulAut.conj g
  let E := A.map f.toMonoidHom
  let L := d.localGroup (g • v)
  let : Finite L := Finite.of_injective (inclusion (d.local_le (g • v))) (inclusion_injective _)
  have hEL : E ≤ L := by
    change E ≤ d.localGroup (g • v)
    rw [d.conjugate]
    exact map_mono hAL
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (E.subgroupOf L) := IsElementaryAbelian.subgroupOf hEL
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsElementaryAbelian 2 ((E.subgroupOf L).map q) := IsElementaryAbelian.map _
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q (family P) (g • v))
    E q (local_quotient_kernel (family P) d (g • v) (MulEquiv.refl _)) hEL
  have hh : (Q (family P) (g • v)).relIndex E ≤ 2^n :=
    hi ▸ (primeRank_le_iff_elementary_card_le _).mp hr _ inferInstance
  rw [Q_translate,relIndex_map_map_of_injective _ _ f.injective] at hh
  exact hh

/-- Both original opposite-span indices are bounded by the rank of the
ending quotient; the second bound uses actual orbit conjugation. -/
theorem source_ending_rank_actor_bounds (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (n : ℕ) (hr : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ n) :
    let F := family P
    (Q F a').relIndex (V F beta 1) ≤ 2^n ∧
      (Q F beta).relIndex (V F a' 1) ≤ 2^n := by
  let := finite_endpoints h
  let F := family P
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  let : IsElementaryAbelian 2 (V F a' 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  have hbt : beta.type = a'.type := by
    apply (even_dist_iff F h.generate beta a').mp
    obtain ⟨k,hk⟩ := (source_critical_geometry h d hc hab hd hb hcomm).1
    exact ⟨k,by change (graph (family P)).dist beta a' = k+k; omega⟩
  constructor
  · apply elementary_index_same_orbit h d (v := a') rfl n hr
    apply pGroup_le_localGroup F d a' _ (IsElementaryAbelian.isPGroup 2 _)
    exact V_le_stabilizer_of_dist_add_le_b F h.generate beta a' 1 hd.le
  · apply elementary_index_same_orbit h d hbt n hr
    apply pGroup_le_localGroup F d beta _ (IsElementaryAbelian.isPGroup 2 _)
    apply V_le_stabilizer_of_dist_add_le_b F h.generate a' beta 1
    rw [SimpleGraph.dist_comm]
    exact hd.le

/-- The complete quotient-omega commutator conclusion of 8.3 when the
ending quotient has binary rank at most one. Both paired inequalities are proved. -/
theorem source_ending_two_rank_one_omega_commutator (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hr : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ 1) :
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ := by
  let := finite_endpoints h
  let F := family P
  have hVP (v : Vertex F) : V F v 1 ≤ stabilizer F v :=
    V_le_stabilizer_of_dist_add_le_b F h.generate v v 1 (by
      simp only [SimpleGraph.dist_self,zero_add]; exact hb.le)
  let : Finite (V F beta 1) := Finite.of_injective (inclusion (hVP beta)) (inclusion_injective _)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion (hVP a')) (inclusion_injective _)
  obtain ⟨hx,hy⟩ := source_ending_rank_actor_bounds h d hc hab hd hb hcomm 1 hr
  simp only [pow_one] at hx hy
  have hxpos : 0 < (Q F a').relIndex (V F beta 1) :=
    Nat.pos_of_ne_zero (((Q F a').subgroupOf (V F beta 1)).index_ne_zero_of_finite)
  have hypos : 0 < (Q F beta).relIndex (V F a' 1) :=
    Nat.pos_of_ne_zero (((Q F beta).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  apply source_omega_commutator_of_paired_indices h hB d hc hab hd hb hcomm models w hm R hR
  intro n hn _
  have hfour : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  constructor <;> nlinarith

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Literal F1.11 application, constructing the moving neighbor and its
full-edge Sylow and retaining the original quotient-omega preimage. -/
theorem reduced_ending_two_rank_one_omega_commutator
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
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≤ 1) :
    let F := Reduction.reducedFamily J S₀
    ¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have he := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  exact ⟨he,w,hm,R,hR,source_ending_two_rank_one_omega_commutator ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm R hR hr⟩


/-- All four binary ending models supply their actual rank bound, so the
source application has no remaining rank or paired-comparison premise. -/
theorem reduced_ending_binary_models_omega_commutator
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
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hsmall :
      let D := graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')
      ClassicalGroup.IsPSL D 2 2 ∨ Nonempty (D ≃* SuzukiMatrixGroup 0) ∨
        ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) :
    let F := Reduction.reducedFamily J S₀
    ¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  let F := Reduction.reducedFamily J S₀
  let D := graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup F a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hr : primeRank 2 D ≤ 1 := by
    rcases hsmall with hlin | hsuz | hpsu | hsu
    · obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hlin
      let := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
        (by simpa only [pow_one,Nat.card_eq_fintype_card] using hK)
      let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
      rw [primeRank_congr 2 e]
      let T : Sylow 2 SL(2,K) := default
      rw [T.primeRank_eq]
      apply (primeRank_le_iff_elementary_card_le T).mpr
      intro E _
      have hc : Nat.card T = Nat.card K :=
        (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 T).toEquiv).symm
      exact (Subgroup.card_le_card_group E).trans (by simpa only [pow_one,hK] using hc.le)
    · obtain ⟨e⟩ := hsuz
      rw [primeRank_congr 2 e]
      let R := zpowers suzukiZeroRootGenerator
      have hc : Nat.card R = 2^2 := by
        rw [Nat.card_zpowers,suzukiZeroRootGenerator_order]
        rfl
      have hp : IsPGroup 2 R := IsPGroup.of_card hc
      have hi : ¬ 2 ∣ R.index := by
        have he := R.card_mul_index
        rw [show Nat.card R = 4 from hc,suzukiZero_card] at he
        have hx : R.index = 5 := by omega
        simp only [hx]
        decide
      apply (hp.toSylow hi).primeRank_le_one_of_isCyclic
      change IsCyclic R
      infer_instance
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hpsu
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e]
      exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hsu
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
  exact reduced_ending_two_rank_one_omega_commutator h hob models hc hab hd hb hcomm hne hr

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
