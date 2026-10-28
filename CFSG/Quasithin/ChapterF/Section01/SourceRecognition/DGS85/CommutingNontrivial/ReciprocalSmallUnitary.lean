module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneSquare
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalCatalogue
public import Theory.SpecificGroups.SU3.BinarySylowOrder

/-!
# Removing the field-two unitary reciprocal cases

Under V_alpha' ≤ Q_beta, the image of any neighboring center in the
rank-one quotient at alpha is elementary and has order at most two for
SU₃(2) and PSU₃(2). Since Q_alpha centralizes Z_alpha intersect Q_alpha',
that same bound controls the neighboring center's displacement by this
intersection. The Sylow-faithful rank-one argument gives index at least
four whenever the intersection moves that center, a contradiction.

Actual orbit conjugation transports the prescribed quotient from alpha
to each neighbor. The closed-ball center seed is handled separately, so
the conclusion centralizes the entire original V_alpha'. For SU₃(2), the
odd scalar quotient supplies the two-rank and Sylow-order estimates without
asserting faithfulness of the full special-unitary center action.

Combining this with the existing complete catalogue leaves only unitary
field order at least four in the nonzero moving-intersection subcase.
`ReciprocalSmallUnitaryApplication` supplies the literal reduced F1.11
application for arbitrary critical orientation. The large-unitary and
factor-module arguments of full reciprocal escape remain open.

Source: DGS, *Groups and Graphs* (1985), (8.2), pp.134--135.
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

private theorem reverse_rank_one_intersection_centralizes (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    (hr : primeRank 2 D ≤ 1) (hSc : ∀ S : Sylow 2 D, 2 < Nat.card S) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  apply reverse_intersection_centralizes h d hab hreverse 2 (by decide)
  · intro w hZL
    exact center_core_index_bound h d a w.val hZL e 2 (fun A hA => by
      simpa only [pow_one] using (primeRank_le_iff_elementary_card_le D).mp hr A hA)
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
    apply source_moving_rank_one_square_bound h d hc hab hd hb hcomm w hm' ew hr hSc A
    · exact hAV.trans (source_moving_actor h d hc hab hd hb hcomm w hm').2.1
    · intro hAQ
      exact hm (commutator_eq_bot_iff_le_centralizer.mpr (hAQ.trans
        (le_centralizer_iff.mp (Z_centralizes_Q (family P) w.val (source_Z_Q_U h w.val).1))))

/-- Both field-two unitary rows satisfy the moving-intersection conclusion
of 8.2. The original action may have an odd scalar kernel; only its Sylow
restriction is used faithfully, with fixed-space generation proved on the
unchanged center. -/
theorem source_reverse_small_unitary_intersection_centralizes
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (hmodel : ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 2 ∨
      IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 2) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  rcases hmodel with hm | hm
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply reverse_rank_one_intersection_centralizes h d hc hab hd hb hcomm hreverse e
    · exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
    · intro S
      have hh := HermitianForm.BinarySylowOrder.cube_le_sylow_card J (n := 1) (by decide) hK hconj S
      norm_num at hh
      omega
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply reverse_rank_one_intersection_centralizes h d hc hab hd hb hcomm hreverse e
    · rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
    · intro S
      let T := S.mapSurjective (f := J.specialToProjective) J.specialToProjective_surjective
      have hh := HermitianForm.BinarySylowOrder.cube_le_sylow_card J (n := 1) (by decide) hK hconj T
      have hle : Nat.card T ≤ Nat.card S := Nat.card_le_card_of_surjective
        (fun s : S => (⟨J.specialToProjective s,mem_map_of_mem _ s.property⟩ : T)) (by
          rintro ⟨_,s,hs,rfl⟩
          exact ⟨⟨s,hs⟩,rfl⟩)
      norm_num at hh
      omega

/-- The complete catalogue reduces a nonzero moving intersection under
reverse containment to field order at least four. The actual unitary model
and every literal neighboring-core index are retained. -/
theorem source_reverse_moving_intersection_large_unitary_witness
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (hmove : ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥) :
    ∃ n : ℕ, 2 ≤ n ∧
      (ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n) ∨
        IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n)) ∧
      (∀ w : (graph (family P)).neighborSet a',
        (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') ≤ 2) ∧
      ∃ w : (graph (family P)).neighborSet a',
        ⁅Z (family P) a ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ ∧
        (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') = 2 := by
  obtain ⟨n,hn,hm,hi,hw⟩ := source_reverse_moving_intersection_unitary_witness
    h hB d hc hab hd hb hcomm models hreverse hmove
  refine ⟨n,?_,hm,hi,hw⟩
  by_contra! hn2
  have hn1 : n = 1 := by omega
  have hm2 : ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 2 ∨
      IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 2 := by
    simpa only [hn1,pow_one] using hm
  exact hmove (source_reverse_small_unitary_intersection_centralizes h d hc hab hd hb hcomm hreverse hm2)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
