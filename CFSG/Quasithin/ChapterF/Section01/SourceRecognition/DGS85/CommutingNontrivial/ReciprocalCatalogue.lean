module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalUnitaryIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalDihedral

/-!
# Exhaustive catalogue reduction of the reciprocal moving intersection

The linear and Suzuki comparisons already force A = Z_alpha intersect
Q_alpha' to centralize the whole radius-one span under V_alpha' ≤ Q_beta.
The separate dihedral estimate gives the same contradiction in D₁₀: its
moving-center index is at least four and at most two. The unitary comparison
bounds every neighbor image of A by two, including both field-two models.

The complete source-model split therefore reduces a nonzero moving
intersection to an actual unitary model and constructs a neighbor whose
literal core has index exactly two in A. The separate center seed in the
closed radius-one ball is accounted for in choosing this neighbor.
`ReciprocalCatalogueApplication` applies the result to the original F1.11
reduction. The unitary involution and zero-intersection factor-module
arguments remain required for full reciprocal escape.

Source: DGS, *Groups and Graphs* (1985), (8.2), pp.134--135. This is the
second-subcase reduction, not the conclusion of (8.2) or of Chapter 8.
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


private theorem dihedral_elementary_card (A : Subgroup (DihedralGroup 5))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 2 := by
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn : ¬ 5 ∣ Nat.card A := by
    rw [hk]
    exact fun h => (by decide : ¬ 5 ∣ 2) (Nat.prime_five.dvd_of_dvd_pow h)
  have hc : Nat.card A ∣ 2 :=
    ((Nat.prime_five.coprime_iff_not_dvd.mpr hn).symm).dvd_of_dvd_mul_right
      (by simpa only [DihedralGroup.nat_card] using A.card_subgroup_dvd_card)
  exact Nat.le_of_dvd (by decide) hc

/-- D₁₀ is excluded from the moving-intersection subcase without treating
it as an entry in the Chapter 5 quadratic-module catalogue. -/
theorem source_reverse_dihedral_intersection_centralizes (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* DihedralGroup 5) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ := by
  apply reverse_intersection_centralizes h d hab hreverse 2 (by decide)
  · intro w hZL
    exact center_core_index_bound h d a w.val hZL e 2
      (fun A hA => @dihedral_elementary_card A hA)
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
    apply source_moving_dihedral_field_square_bound h d hc hab hd hb hcomm w hm' ew A
    · exact hAV.trans (source_moving_actor h d hc hab hd hb hcomm w hm').2.1
    · intro hAQ
      exact hm (commutator_eq_bot_iff_le_centralizer.mpr (hAQ.trans
        (le_centralizer_iff.mp (Z_centralizes_Q (family P) w.val (source_Z_Q_U h w.val).1))))

private def linear_field_lift (K : Type) [Field K] : SL(2,K) ≃* SL(2,ULift.{u} K) where
  toFun := Matrix.SpecialLinearGroup.map ULift.ringEquiv.symm.toRingHom
  invFun := Matrix.SpecialLinearGroup.map ULift.ringEquiv.toRingHom
  left_inv x := by ext i j; rfl
  right_inv x := by ext i j; rfl
  map_mul' x y := (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (ULift.ringEquiv.symm : K ≃+* ULift.{u} K).toRingHom).map_mul x y

/-- Exhaustive source-model reduction of the second subcase of 8.2.
Under reverse containment, either the intersection centralizes the whole
radius-one span, or the starting quotient is actually unitary and every
neighbor image of the original intersection has order at most two. -/
theorem source_reverse_intersection_centralizes_or_unitary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta) :
    ⁅Z (family P) a ⊓ Q (family P) a',V (family P) a' 1⁆ = ⊥ ∨
      ∃ n : ℕ, 0 < n ∧
        (ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n) ∨
          IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n)) ∧
        ∀ w : (graph (family P)).neighborSet a',
          (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') ≤ 2 := by
  cases models a with
  | linear n hn hi =>
    left
    obtain ⟨K,_,_,hK,⟨e⟩⟩ := hi
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hK)
    let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact source_reverse_linear_intersection_centralizes h hB d hc hab hd hb hcomm models hreverse
      hn (by simpa only [Nat.card_ulift] using hK) (f.trans (linear_field_lift K))
  | suzuki m hi =>
    exact Or.inl (source_reverse_suzuki_intersection_centralizes h d hc hab hd hb hcomm hreverse m hi.some)
  | projective_unitary n hn hi =>
    exact Or.inr ⟨n,hn,Or.inl hi,source_reverse_unitary_intersection_indices h d hc hab hd hb hcomm
      hreverse hn (Or.inl hi)⟩
  | special_unitary n hn hi =>
    exact Or.inr ⟨n,hn,Or.inr hi,source_reverse_unitary_intersection_indices h d hc hab hd hb hcomm
      hreverse hn (Or.inr hi)⟩
  | dihedral hi =>
    exact Or.inl (source_reverse_dihedral_intersection_centralizes h d hc hab hd hb hcomm hreverse hi.some)


/-- A nonzero moving-intersection countercase to 8.2 has an actual unitary
model and a literal neighboring core of index two in that intersection.
The zero-intersection branch is kept distinct from reciprocal escape. -/
theorem source_reverse_moving_intersection_unitary_witness
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
    ∃ n : ℕ, 0 < n ∧
      (ClassicalGroup.IsPSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n) ∨
        IsSU (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 3 (2^n)) ∧
      (∀ w : (graph (family P)).neighborSet a',
        (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') ≤ 2) ∧
      ∃ w : (graph (family P)).neighborSet a',
        ⁅Z (family P) a ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥ ∧
        (Q (family P) w.val).relIndex (Z (family P) a ⊓ Q (family P) a') = 2 := by
  let := finite_endpoints h
  let F := family P
  let A := Z F a ⊓ Q F a'
  obtain ⟨n,hn,hi,hall⟩ :=
    (source_reverse_intersection_centralizes_or_unitary h hB d hc hab hd hb hcomm models hreverse).resolve_left hmove
  have hw : ∃ w : (graph F).neighborSet a', ⁅A,Z F w.val⁆ ≠ ⊥ := by
    by_contra! hz
    apply hmove
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rw [V_one_eq_sup_neighbors]
    apply sup_le
    · exact (Z_centralizes_Q F a' (source_Z_Q_U h a').1).trans (centralizer_le inf_le_right)
    · exact iSup_le fun w => le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hz w))
  obtain ⟨w,hw⟩ := hw
  refine ⟨n,hn,hi,hall,w,hw,?_⟩
  let : Finite (Z F a) := Finite.of_injective (inclusion (Z_le_stabilizer F a))
    (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion (show A ≤ Z F a from inf_le_left))
    (inclusion_injective _)
  have hnz : (Q F w.val).relIndex A ≠ 0 := ((Q F w.val).subgroupOf A).index_ne_zero_of_finite
  have hn1 : (Q F w.val).relIndex A ≠ 1 := by
    intro he
    exact hw (commutator_eq_bot_iff_le_centralizer.mpr ((relIndex_eq_one.mp he).trans
      (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1))))
  have hu := hall w
  change (Q F w.val).relIndex A ≤ 2 at hu
  change (Q F w.val).relIndex A = 2
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
