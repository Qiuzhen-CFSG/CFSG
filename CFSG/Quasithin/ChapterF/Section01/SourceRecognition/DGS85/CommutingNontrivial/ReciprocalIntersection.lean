module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalLinear
public import Theory.SpecificGroups.Suzuki.RootCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalSuzuki

/-!
# The moving-intersection comparison in DGS 8.2

Assume the reverse containment V_alpha' ≤ Q_beta. If
A = Z_alpha intersect Q_alpha' moves a neighboring center Z_lambda, the
linear or Suzuki field-square estimate gives [Z_lambda:C_(Z_lambda)(A)]
≥ q². Reverse containment puts Z_lambda in the local group at alpha.
Its elementary image there has order at most q, and Q_alpha centralizes A,
so the same centralizer index is at most q, a contradiction.

The local quotient at lambda is transported from alpha through actual
conjugation and the intrinsic two-core quotient. Odd critical distance
proves these vertices have the same type. Taking all neighboring centers,
including the separate center seed of the closed ball, proves
[Z_alpha intersect Q_alpha',V_alpha'] = 1. Every binary linear parameter
and every Suzuki parameter, including the small groups, is retained.

Source: DGS, *Groups and Graphs* (1985), the second subcase in the proof
of (8.2), p.135. `ReciprocalIntersectionApplication` applies the result to
the literal reduced F1.11 graph. The first subcase, its suitable factor
module, and the unitary rows are still required for full (8.2).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private def quotient_at_same_type (F : Bool → Subgroup G) (d : EarlierLocalTheorems F)
    {v w : Vertex F} (ht : v.type = w.type)
    {D : Type*} [Group D] (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≃* D := by
  let g := Classical.choose ((same_orbit_iff F v w).mpr ht)
  have hg := Classical.choose_spec ((same_orbit_iff F v w).mpr ht)
  have he : d.localGroup w = (d.localGroup v).map (MulAut.conj g).toMonoidHom := by
    rw [←hg,d.conjugate]
  let f := (MulEquiv.subgroupCongr he).trans
    ((d.localGroup v).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  exact (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e

private theorem linear_elementary_card {K : Type*} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup SL(2,K)) [IsElementaryAbelian 2 A] : Nat.card A ≤ Nat.card K := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  exact (card_le_of_le hAS).trans_eq
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 S).symm.toEquiv)

private theorem suzuki_elementary_card (m : ℕ) (A : Subgroup (SuzukiMatrixGroup m))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 2^(2*m+1) := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · let T : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
      rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
      rw [show (20 : ℕ) = 2^2 * 5 from rfl,
        Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
      norm_num [Nat.Prime.factorization Nat.prime_two,
        Nat.Prime.factorization (by decide : Nat.Prime 5)])
    let : IsCyclic T := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
    let : IsCyclic S := (Sylow.equiv T S).isCyclic.mp inferInstance
    let : IsCyclic A := Subgroup.isCyclic_of_le hAS
    change Nat.card A ≤ 2
    apply Nat.le_of_dvd (by decide)
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  · have hcent : A ≤ (center S).map (S : Subgroup (SuzukiMatrixGroup m)).subtype := by
      intro x hx
      let s : S := ⟨x,hAS hx⟩
      have hs : s ∈ center S := binary_rank_one_sylow_square_central
        (.suzuki m (MulEquiv.refl _)) S s
        (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))
      exact ⟨s,hs,rfl⟩
    have hcm : Nat.card ((center S).map (S : Subgroup (SuzukiMatrixGroup m)).subtype) = Nat.card (center S) :=
      card_map_of_injective (K := center S) (S : Subgroup (SuzukiMatrixGroup m)).subtype_injective
    exact (card_le_of_le hcent).trans_eq (hcm.trans
      (suzukiSylow_borel_structure hm (MulEquiv.refl _) S).1)

private theorem center_core_index_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (a w : Vertex (family P))
    (hZL : Z (family P) w ≤ d.localGroup a)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    (c : ℕ) (hcard : ∀ A : Subgroup D, IsElementaryAbelian 2 A → Nat.card A ≤ c) :
    (Q (family P) a).relIndex (Z (family P) w) ≤ c := by
  let := CommutingOneProfile.source_center_elementary h w
  let L := d.localGroup a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsElementaryAbelian 2 ((Z (family P) w).subgroupOf L) := IsElementaryAbelian.subgroupOf hZL
  let : IsElementaryAbelian 2 (((Z (family P) w).subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q (family P) a)
    (Z (family P) w) q (local_quotient_kernel (family P) d a e) hZL
  exact hi ▸ hcard _ inferInstance

private theorem reverse_intersection_centralizes (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (c : ℕ) (hc1 : 1 < c)
    (hupper : ∀ w : (graph (family P)).neighborSet a',
      Z (family P) w.val ≤ d.localGroup a → (Q (family P) a).relIndex (Z (family P) w.val) ≤ c)
    (hlower : ∀ w : (graph (family P)).neighborSet a',
      ⁅Z (family P) a ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ →
      c^2 ≤ (centralizer ((Z (family P) a ⊓ Q (family P) a' : Subgroup G) : Set G)).relIndex
        (Z (family P) w.val)) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  let := finite_endpoints h
  let F := family P
  let A := Z F a ⊓ Q F a'
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  rw [V_one_eq_sup_neighbors]
  apply sup_le
  · exact (Z_centralizes_Q F a' (source_Z_Q_U h a').1).trans (centralizer_le inf_le_right)
  · apply iSup_le
    intro w
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    by_contra hm
    have hq : Z F w.val ≤ Q F beta := (Z_neighbor_le_V F w.property).trans hreverse
    have hZP : Z F w.val ≤ stabilizer F a := hq.trans
      ((source_Z_Q_U h beta).2.trans ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))
    have hZL : Z F w.val ≤ d.localGroup a := pGroup_le_localGroup F d a _
      ((isPGroup_pCoreIn 2 (stabilizer F w.val)).to_le ((source_Z_Q_U h w.val).1.trans (map_subtype_le _))) hZP
    let : Finite (Z F w.val) := Finite.of_injective (inclusion (Z_le_stabilizer F w.val))
      (inclusion_injective _)
    have hcen : Q F a ≤ centralizer (A : Set G) :=
      (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1)).trans
        (centralizer_le inf_le_left)
    have hnonzero : (Q F a).relIndex (Z F w.val) ≠ 0 :=
      ((Q F a).subgroupOf (Z F w.val)).index_ne_zero_of_finite
    have hu : (centralizer (A : Set G)).relIndex (Z F w.val) ≤ c :=
      (relIndex_le_of_le_left hcen hnonzero).trans (hupper w hZL)
    have hl : c^2 ≤ (centralizer (A : Set G)).relIndex (Z F w.val) := hlower w hm
    nlinarith

private theorem critical_neighbor_same_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a') : a.type = w.val.type := by
  have hodd := (source_critical_geometry h d hc hab hd hb hcomm).1
  have hne : a.type ≠ a'.type := by
    intro ht
    have he := (even_dist_iff (family P) h.generate a a').mpr ht
    rw [hc.1] at he
    exact (Nat.not_even_iff_odd.mpr hodd) he
  have hn := w.property.1
  cases hat : a.type <;> cases hwt : w.val.type <;> cases het : a'.type <;> simp_all

/-- In the linear row, reverse core containment forces the second subcase
of DGS 8.2 to vanish on the entire original radius-one span. -/
theorem source_reverse_linear_intersection_centralizes (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,K)) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  apply reverse_intersection_centralizes h d hab hreverse (Nat.card K) (by
    rw [hK]; exact Nat.one_lt_pow hn.ne' (by decide))
  · intro w hZL
    exact center_core_index_bound h d a w.val hZL e _ (fun A hA =>
      @linear_elementary_card K _ _ _ A hA)
  · intro w hm
    let A := Z (family P) a ⊓ Q (family P) a'
    have hAV : A ≤ V (family P) beta 1 ⊓ Q (family P) a' :=
      inf_le_inf (Z_neighbor_le_V (family P) hab.symm) le_rfl
    have hm' : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ := by
      intro he
      exact hm (bot_unique ((commutator_mono hAV le_rfl).trans he.le))
    let ew := quotient_at_same_type (family P) d
      (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
    apply source_moving_linear_field_square_bound h hB d hc hab hd hb hcomm models hreverse
      w hm' hn hK ew A
    · exact inf_le_right.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property)
    · intro hAQ
      exact hm (commutator_eq_bot_iff_le_centralizer.mpr (hAQ.trans
        (le_centralizer_iff.mp (Z_centralizes_Q (family P) w.val (source_Z_Q_U h w.val).1))))

/-- The Suzuki comparison, including Sz(2), excludes movement by the
intersection of the starting center and the ending core under reverse
containment. No whole-action faithfulness or numerical premise is added. -/
theorem source_reverse_suzuki_intersection_centralizes (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (m : ℕ) (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SuzukiMatrixGroup m) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  apply reverse_intersection_centralizes h d hab hreverse (2^(2*m+1)) (by
    exact Nat.one_lt_pow (by omega) (by decide))
  · intro w hZL
    exact center_core_index_bound h d a w.val hZL e _ (fun A hA =>
      @suzuki_elementary_card m A hA)
  · intro w hm
    let := CommutingOneProfile.source_center_elementary h a
    let A := Z (family P) a ⊓ Q (family P) a'
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
    have hAV : A ≤ V (family P) beta 1 ⊓ Q (family P) a' :=
      inf_le_inf (Z_neighbor_le_V (family P) hab.symm) le_rfl
    have hm' : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ := by
      intro he
      exact hm (bot_unique ((commutator_mono hAV le_rfl).trans he.le))
    let ew := quotient_at_same_type (family P) d
      (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
    apply source_moving_suzuki_field_square_bound h d hc hab hd hb hcomm w hm' m ew A
    · exact hAV.trans (source_moving_actor h d hc hab hd hb hcomm w hm').2.1
    · intro hAQ
      exact hm (commutator_eq_bot_iff_le_centralizer.mpr (hAQ.trans
        (le_centralizer_iff.mp (Z_centralizes_Q (family P) w.val (source_Z_Q_U h w.val).1))))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
