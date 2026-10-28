module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryInvolutions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalSmallUnitary

/-!
# Vanishing of the reciprocal moving intersection for the full catalogue

Assume V_alpha' ≤ Q_beta. The previous catalogue comparison reduces a
nonzero action of A = Z_alpha intersect Q_alpha' on V_alpha' to a unitary
quotient with field order q ≥ 4 and a neighboring center Z_lambda moved
by A. The full quotient omega-center at lambda is quadratic, so the
unitary involution estimate gives [Z_lambda:C_(Z_lambda)(A)] ≥ q².

Reverse containment puts Z_lambda in the local group at alpha. Its
quotient image is elementary, hence has order at most q by the actual
unitary two-rank. Since Q_alpha centralizes A, the same displacement
index is at most q. Actual orbit conjugation identifies the two quotient
models; no unmarked group-family tag is used. The contradiction closes
the moving-intersection subcase across every source catalogue entry.

The zero-intersection factor-module argument is still required for full
reciprocal escape. `ReciprocalVanishingApplication` gives the literal
reduced F1.11 application, in either critical orientation.

Source: DGS, *Groups and Graphs* (1985), the second subcase of 8.2,
printed p.135, using 5.10(b) and 8.1(h).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
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


private theorem reverse_moving_index_upper (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (w : (graph (family P)).neighborSet a')
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    (n : ℕ) (hr : primeRank 2 D ≤ n) :
    (centralizer ((Z (family P) a ⊓ Q (family P) a' : Subgroup G) : Set G)).relIndex
      (Z (family P) w.val) ≤ 2^n := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let F := family P
  let L := d.localGroup a
  let A := Z F a ⊓ Q F a'
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Z F w.val ≤ Q F beta := (Z_neighbor_le_V F w.property).trans hreverse
  have hZP : Z F w.val ≤ stabilizer F a := hq.trans
    ((source_Z_Q_U h beta).2.trans ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))
  have hZL : Z F w.val ≤ L := pGroup_le_localGroup F d a _
    (IsElementaryAbelian.isPGroup 2 _) hZP
  let : Finite (Z F w.val) := Finite.of_injective (inclusion (Z_le_stabilizer F w.val))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 ((Z F w.val).subgroupOf L) := IsElementaryAbelian.subgroupOf hZL
  let : IsElementaryAbelian 2 (((Z F w.val).subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F a)
    (Z F w.val) q (local_quotient_kernel F d a e) hZL
  have hu : (Q F a).relIndex (Z F w.val) ≤ 2^n :=
    hi ▸ (primeRank_le_iff_elementary_card_le D).mp hr _ inferInstance
  have hcen : Q F a ≤ centralizer (A : Set G) :=
    (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1)).trans
      (centralizer_le inf_le_left)
  have hnonzero : (Q F a).relIndex (Z F w.val) ≠ 0 :=
    ((Q F a).subgroupOf (Z F w.val)).index_ne_zero_of_finite
  exact (relIndex_le_of_le_left hcen hnonzero).trans hu

/-- The complete moving-intersection subcase in the proof of 8.2.
Under reverse containment, Z_alpha intersect Q_alpha' centralizes the
whole original V_alpha'. This includes every source model and both
unitary scalar conventions; the zero-intersection factor-module case is
still needed to deduce unconditional reciprocal escape. -/
theorem source_reverse_intersection_centralizes (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  by_contra hmove
  obtain ⟨n,hn,hmodel,_,w,hw,_⟩ := source_reverse_moving_intersection_large_unitary_witness
    h hB d hc hab hd hb hcomm models hreverse hmove
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  let A := Z F a ⊓ Q F a'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAV : A ≤ V F beta 1 ⊓ Q F a' := inf_le_inf (Z_neighbor_le_V F hab.symm) le_rfl
  have hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ := by
    intro he
    exact hw (bot_unique ((commutator_mono hAV le_rfl).trans he.le))
  have hAE : A ≤ (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 :=
    inf_le_right.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property)
  have hAQ : ¬ A ≤ Q F w.val := by
    intro hAQ
    exact hw (commutator_eq_bot_iff_le_centralizer.mpr (hAQ.trans
      (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1))))
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  rcases hmodel with hi | hi
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    let ew := quotient_at_same_type F d (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
    have hu := reverse_moving_index_upper h d hab hreverse w e n
      (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
    have hl := source_moving_projective_unitary_involution_field_square_bound h hB d hc hab hd hb hcomm
      models w hm J hn hK hconj ew A hAE hAQ
    have hle : (2^n)^2 ≤ 2^n := hl.trans hu
    nlinarith only [hq,hle]
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    let ew := quotient_at_same_type F d (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
    have hr : primeRank 2 J.specialSubgroup ≤ n := by
      rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
    have hu := reverse_moving_index_upper h d hab hreverse w e n hr
    have hl := source_moving_special_unitary_involution_field_square_bound h hB d hc hab hd hb hcomm
      models w hm J hn hK hconj ew A hAE hAQ
    have hle : (2^n)^2 ≤ 2^n := hl.trans hu
    nlinarith only [hq,hle]

/-- Reciprocal escape for the nonzero-intersection subcase, with no
restriction on the original rank-one quotient catalogue or orientation. -/
theorem source_reciprocal_escape_of_moving_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hmove : ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta :=
  fun hreverse => hmove (source_reverse_intersection_centralizes h hB d hc hab hd hb hcomm models hreverse)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
