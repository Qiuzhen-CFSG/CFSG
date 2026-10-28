module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalUnitary

/-!
# The remaining unitary intersection in the reciprocal argument

Under V_alpha' ≤ Q_beta, the action of A = Z_alpha intersect Q_alpha'
on each neighboring center has centralizer index at most q: the original
center image in L_alpha/Q_alpha is elementary of order at most q, and
Q_alpha centralizes A. The field-square estimate excludes every moving
image of A of order at least four. The elementary image is therefore of
order two. A vanishing commutator puts A in the original core, by the
Sylow-centralizer alternative. This gives the index bound for all neighbors.

The actual quotient marking is transported through the vertex orbit.
Both SU₃ and PSU₃ and field order two are retained. The unitary involution
case of 5.10(b) and the factor-module subcase are still needed for 8.2.
`ReciprocalCatalogueApplication` supplies the literal reduced-source consumer.

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


private theorem reverse_center_index_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    {n : ℕ} (hr : primeRank 2 D ≤ n) (w : (graph (family P)).neighborSet a') :
    (centralizer ((Z (family P) a ⊓ Q (family P) a' : Subgroup G) : Set G)).relIndex
      (Z (family P) w.val) ≤ 2^n := by
  let := finite_endpoints h
  let F := family P
  let A := Z F a ⊓ Q F a'
  let L := d.localGroup a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let := CommutingOneProfile.source_center_elementary h w.val
  have hq : Z F w.val ≤ Q F beta := (Z_neighbor_le_V F w.property).trans hreverse
  have hZP : Z F w.val ≤ stabilizer F a := hq.trans
    ((source_Z_Q_U h beta).2.trans ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))
  have hZL : Z F w.val ≤ L := pGroup_le_localGroup F d a _
    (IsElementaryAbelian.isPGroup 2 _) hZP
  let : IsElementaryAbelian 2 ((Z F w.val).subgroupOf L) :=
    IsElementaryAbelian.subgroupOf hZL
  let : IsElementaryAbelian 2 (((Z F w.val).subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F a)
    (Z F w.val) q (local_quotient_kernel F d a e) hZL
  have hu : (Q F a).relIndex (Z F w.val) ≤ 2^n := hi ▸
    (primeRank_le_iff_elementary_card_le D).mp hr _ inferInstance
  let : Finite (Z F w.val) := Finite.of_injective
    (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  have hcen : Q F a ≤ centralizer (A : Set G) :=
    (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1)).trans
      (centralizer_le inf_le_left)
  exact (relIndex_le_of_le_left hcen
    ((Q F a).subgroupOf (Z F w.val)).index_ne_zero_of_finite).trans hu

private theorem intersection_index_eq_two_of_lt_four (h : LocallyRankOneTriple P B)
    {a a' : Vertex (family P)} (w : (graph (family P)).neighborSet a')
    (hm : ⁅Z (family P) a ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hsmall : (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') < 4) :
    (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') = 2 := by
  let := finite_endpoints h
  let F := family P
  let A := Z F a ⊓ Q F a'
  let := CommutingOneProfile.source_center_elementary h a
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  let : Finite (Z F a) := Finite.of_injective (inclusion (Z_le_stabilizer F a))
    (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion (show A ≤ Z F a from inf_le_left))
    (inclusion_injective _)
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).index ((Q F w.val).subgroupOf A)
  change (Q F w.val).relIndex A = 2^k at hk
  have hne : (Q F w.val).relIndex A ≠ 1 := by
    intro he
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr ((relIndex_eq_one.mp he).trans
      (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1))))
  have hk1 : k = 1 := by
    have hlo : k < 2 := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      simpa only [←hk] using hsmall
    have hk0 : k ≠ 0 := by intro he; apply hne; simpa only [he,pow_zero] using hk
    omega
  simpa only [hk1,pow_one] using hk

/-- Under the reverse containment in 8.2, any moving intersection in
this unitary row has quotient image of order exactly two. Every larger
image is excluded by the field-square bound on the same original action. -/
theorem source_reverse_special_unitary_moving_intersection_index
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* J.specialSubgroup)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅Z (family P) a ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥) :
    (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') = 2 := by
  let := CommutingOneProfile.source_center_elementary h a
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let A := Z (family P) a ⊓ Q (family P) a'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hr : primeRank 2 (J.specialSubgroup) ≤ n := by
    rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  apply intersection_index_eq_two_of_lt_four h w hm
  by_contra! hlarge
  have hu := reverse_center_index_bound h d hab hreverse e hr w
  have hAV : A ≤ V (family P) beta 1 ⊓ Q (family P) a' :=
    inf_le_inf (Z_neighbor_le_V (family P) hab.symm) le_rfl
  have hm' : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ := by
    intro he
    exact hm (bot_unique ((commutator_mono hAV le_rfl).trans he.le))
  let ew := quotient_at_same_type (family P) d
    (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
  have hl := source_moving_special_unitary_field_square_bound h d hc hab hd hb hcomm
    w hm' J hn hK hconj ew A
    (hAV.trans (source_moving_actor h d hc hab hd hb hcomm w hm').2.1) hlarge
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hle : (2^n)^2 ≤ 2^n := hl.trans hu
  nlinarith only [hle,hq]

/-- Under the reverse containment in 8.2, any moving intersection in
this unitary row has quotient image of order exactly two. Every larger
image is excluded by the field-square bound on the same original action. -/
theorem source_reverse_projective_unitary_moving_intersection_index
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅Z (family P) a ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥) :
    (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') = 2 := by
  let := CommutingOneProfile.source_center_elementary h a
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let A := Z (family P) a ⊓ Q (family P) a'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hr : primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ n := by
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  apply intersection_index_eq_two_of_lt_four h w hm
  by_contra! hlarge
  have hu := reverse_center_index_bound h d hab hreverse e hr w
  have hAV : A ≤ V (family P) beta 1 ⊓ Q (family P) a' :=
    inf_le_inf (Z_neighbor_le_V (family P) hab.symm) le_rfl
  have hm' : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ := by
    intro he
    exact hm (bot_unique ((commutator_mono hAV le_rfl).trans he.le))
  let ew := quotient_at_same_type (family P) d
    (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
  have hl := source_moving_projective_unitary_field_square_bound h d hc hab hd hb hcomm
    w hm' J hn hK hconj ew A
    (hAV.trans (source_moving_actor h d hc hab hd hb hcomm w hm').2.1) hlarge
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hle : (2^n)^2 ≤ 2^n := hl.trans hu
  nlinarith only [hle,hq]


private theorem elementary_core_index_bound (_h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D)
    {n : ℕ} (hr : primeRank 2 D ≤ n)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAP : A ≤ stabilizer (family P) v) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let L := d.localGroup v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hAL : A ≤ L := pGroup_le_localGroup (family P) d v A
    (IsElementaryAbelian.isPGroup 2 A) hAP
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q (family P) v)
    A q (local_quotient_kernel (family P) d v e) hAL
  exact hi ▸ (primeRank_le_iff_elementary_card_le D).mp hr _ inferInstance

/-- The complete unitary reduction of the moving-intersection subcase of
8.2. If reverse containment holds, every neighbor image of Z_alpha intersect
Q_alpha' has order at most two. Both SU and PSU and the field-two endpoints
are retained, and the actual quotient is transported through its vertex orbit. -/
theorem source_reverse_unitary_intersection_indices (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n) ∨
      IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n)) :
    ∀ w : (graph (family P)).neighborSet a',
      (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') ≤ 2 := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  let A := Z F a ⊓ Q F a'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  intro w
  have hAP : A ≤ stabilizer F w.val := inf_le_right.trans
    ((source_Z_Q_U h a').2.trans ((ballKernel_one_le_edge F w.property).trans inf_le_right))
  by_cases hm : ⁅A,Z F w.val⁆ = ⊥
  · have hend := critical_end_center_of_commuting F h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup a') (d.sylow_or_center a')
    have hz := local_center_eq_bot_of_neighbor_central h d w.property.symm hend
    have hk := source_centerless_actor_kernel h d w.val hz A
      (IsElementaryAbelian.isPGroup 2 A) hAP
    have hAQ : A ≤ Q F w.val := fun x hx => (hk.le
      ⟨hx,commutator_eq_bot_iff_le_centralizer.mp hm hx⟩).2
    have hi := relIndex_eq_one.mpr hAQ
    change (Q F w.val).relIndex A ≤ 2
    rw [hi]
    decide
  · rcases hmodel with hmodel | hmodel
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hmodel
      by_cases hn2 : 2 ≤ n
      · exact (source_reverse_projective_unitary_moving_intersection_index h d hc hab hd hb hcomm
          hreverse J hn2 hK hconj e w hm).le
      · have hn1 : n = 1 := by omega
        let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
          Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
        let ew := quotient_at_same_type F d
          (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
        have hr : primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ n := by
          exact (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
        have hi := elementary_core_index_bound h d w.val ew hr A hAP
        simpa only [hn1,pow_one] using hi
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hmodel
      by_cases hn2 : 2 ≤ n
      · exact (source_reverse_special_unitary_moving_intersection_index h d hc hab hd hb hcomm
          hreverse J hn2 hK hconj e w hm).le
      · have hn1 : n = 1 := by omega
        let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
          Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
        let ew := quotient_at_same_type F d
          (critical_neighbor_same_type h d hc hab hd hb hcomm w) e
        have hr : primeRank 2 (J.specialSubgroup) ≤ n := by
          rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
            J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
          exact (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
        have hi := elementary_core_index_bound h d w.val ew hr A hAP
        simpa only [hn1,pow_one] using hi

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
