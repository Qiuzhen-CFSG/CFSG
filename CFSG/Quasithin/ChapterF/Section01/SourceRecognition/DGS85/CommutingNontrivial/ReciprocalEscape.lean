module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EndingRankOne

/-!
# Reciprocal escape for the complete Chapter 8 catalogue

The ending bound is compared with the faithful original starting-center
indices. Linear recognition gives the natural-center contradiction. Suzuki,
dihedral and field-two unitary displacement bounds transport from a moving
neighbor in the same vertex orbit. For larger unitary groups the elementary
square bound applies directly to the original center action, with its scalar
kernel retained. Every actor placement, conjugation and numerical premise is
constructed on the source graph. The reduced application supplies the full
ending catalogue, completing DGS 8.2 in either critical orientation.

Source: DGS, Groups and Graphs (1985), 8.2, printed pp.134–135.
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


private def linear_field_lift (K : Type) [Field K] : SL(2,K) ≃* SL(2,ULift.{u} K) where
  toFun := Matrix.SpecialLinearGroup.map ULift.ringEquiv.symm.toRingHom
  invFun := Matrix.SpecialLinearGroup.map ULift.ringEquiv.toRingHom
  left_inv x := by ext i j; rfl
  right_inv x := by ext i j; rfl
  map_mul' x y := (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (ULift.ringEquiv.symm : K ≃+* ULift.{u} K).toRingHom).map_mul x y


private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)


private theorem elementary_core_index (_h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D)
    (c : ℕ) (hcard : ∀ E : Subgroup D, IsElementaryAbelian 2 E → Nat.card E ≤ c) :
    (Q (family P) v).relIndex A ≤ c := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup v)))
  let : IsElementaryAbelian 2 (A.subgroupOf (d.localGroup v)) :=
    IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf (d.localGroup v)).map q) :=
    IsElementaryAbelian.map q
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex _ _ A q
    (local_quotient_kernel (family P) d v e) hAL
  exact hi ▸ hcard _ inferInstance

private theorem transport_center_lower (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {a w : Vertex (family P)}
    (ht : a.type = w.type) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ d.localGroup a) (hAQ : ¬ A ≤ Q (family P) a) (c : ℕ)
    (hlower : ∀ (E : Subgroup G), IsElementaryAbelian 2 E →
      E ≤ d.localGroup w → ¬ E ≤ Q (family P) w →
      c ≤ (centralizer (E : Set G)).relIndex (Z (family P) w)) :
    c ≤ (centralizer (A : Set G)).relIndex (Z (family P) a) := by
  let := finite_endpoints h
  obtain ⟨g, rfl⟩ := (same_orbit_iff (family P) a w).mpr ht
  let E := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEL : E ≤ d.localGroup (g • a) := by
    rw [d.conjugate]
    exact map_mono hAL
  have hEQ : ¬ E ≤ Q (family P) (g • a) := by
    rw [Q_translate]
    exact fun he => hAQ ((map_le_map_iff_of_injective (MulAut.conj g).injective).mp he)
  have hl := hlower E inferInstance hEL hEQ
  rw [Z_translate, ← centralizer_map_equiv A (MulAut.conj g),
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hl
  exact hl

private theorem center_elementary_square (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (hz : center (d.localGroup v) = ⊥)
    [IsElementaryAbelian 2 (Z (family P) v)]
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D)
    (hbound : ∀ ρ : Representation (ZMod 2) D (Additive (Z (family P) v)),
      (∃ g, ρ g ≠ 1) → fixedSpace ρ ⊤ = ⊥ →
      ∀ E : Subgroup D, IsElementaryAbelian 2 E →
        Nat.card E ^ 2 ≤ Nat.card (Additive (Z (family P) v) ⧸ fixedSpace ρ E))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v) :
    (Q (family P) v).relIndex A ^ 2 ≤
      (centralizer (A : Set G)).relIndex (Z (family P) v) := by
  let := finite_endpoints h
  let := source_center_nontrivial h v
  let F := family P
  let L := d.localGroup v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let Aq := (A.subgroupOf L).map q
  let : Finite (Z F v) := Finite.of_injective (inclusion (Z_le_stabilizer F v))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 Aq := IsElementaryAbelian.map q
  obtain ⟨ρ,hact⟩ := source_exists_center_quotient_action h d v e
  obtain ⟨S,_,_,hres⟩ := source_center_module_prepared_of_center_eq_bot h d v hz default e ρ hact
  have hfix : fixedSpace ρ ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone ρ le_top).trans hres.le)
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! hh
    obtain ⟨z,hz⟩ := exists_ne (0 : Additive (Z F v))
    have hfixed : z ∈ fixedSpace ρ ⊤ := by
      intro g
      change ρ g z = z
      rw [hh]
      rfl
    exact hz (hfix.le hfixed)
  have hlo := hbound ρ hnt hfix Aq inferInstance
  have hZL : Z F v ≤ L := pGroup_le_localGroup F d v _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F v)
  have hi := center_action_fixed_index L (Z F v) A hZL
    ((d.local_le v).trans (stabilizer_normalizes_Z F v)) hAL q ρ hact
  have hc := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F v) A q
    (local_quotient_kernel F d v e) hAL
  rwa [hi,hc] at hlo

/-- The ending bound completes DGS 8.2 across the entire actual source
catalogue. The reduced consumer below constructs that bound. -/
theorem source_reciprocal_escape_of_factor_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥)
    (hfactor : (Q (family P) a').relIndex (Z (family P) a) ≤
      (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  intro hreverse
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  let L := d.localGroup a
  let Z₀ := Z F a
  let A := V F a' 1
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  have hAP : A ≤ stabilizer F a := hreverse.trans ((source_Z_Q_U h beta).2.trans
    ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))
  have hAL : A ≤ L := pGroup_le_localGroup F d a A
    (IsElementaryAbelian.isPGroup 2 A) hAP
  let : Finite A := Finite.of_injective (inclusion hAP) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion (Z_le_stabilizer F a)) (inclusion_injective _)
  have hz := local_center_eq_bot_of_neighbor_central h d hab
    (source_critical_geometry h d hc hab hd hb hcomm).2.2.1
  have he := source_reverse_center_centralizer h hB d hc hab hd hb hcomm models hreverse
  have hcidx : (centralizer (A : Set G)).relIndex Z₀ = (Q F a').relIndex Z₀ := by
    rw [← inf_relIndex_left Z₀ (centralizer (A : Set G)), he, inf_relIndex_left]
  have hupper : (centralizer (Z₀ : Set G)).relIndex A ≤ (Q F a).relIndex A :=
    relIndex_le_of_le_left
      (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1))
      (((Q F a).subgroupOf A).index_ne_zero_of_finite)
  have hx : 1 < (centralizer (A : Set G)).relIndex Z₀ := by
    rw [hcidx]
    have hnz : (Q F a').relIndex Z₀ ≠ 0 := ((Q F a').subgroupOf Z₀).index_ne_zero_of_finite
    have hno : (Q F a').relIndex Z₀ ≠ 1 := by
      intro heq
      exact hc.2 ((relIndex_eq_one.mp heq).trans (source_Z_Q_U h a').2)
    omega
  have hxy : (centralizer (A : Set G)).relIndex Z₀ ≤ (Q F a).relIndex A :=
    hcidx.trans_le (hfactor.trans hupper)
  have hAQ : ¬ A ≤ Q F a := by
    intro ha
    have hcen : Z₀ ≤ centralizer (A : Set G) :=
      (Z_centralizes_Q F a (source_Z_Q_U h a).1).trans (centralizer_le ha)
    have hi := relIndex_eq_one.mpr hcen
    omega
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U h v).1) beta a' hne
  have ht := critical_neighbor_same_type h d hc hab hd hb hcomm w
  have square_contradiction (hl : (Q F a).relIndex A ^ 2 ≤
      (centralizer (A : Set G)).relIndex Z₀) : False := by nlinarith
  have small_contradiction {D : Type} [Group D] [Finite D]
      (e : (L ⧸ pCore 2 L) ≃* D) (hr : primeRank 2 D ≤ 1)
      (hSc : ∀ S : Sylow 2 D, 2 < Nat.card S) : False := by
    have hu : (Q F a).relIndex A ≤ 2 := elementary_core_index h d a A hAL e 2 (fun E hE => by
      simpa only [pow_one] using (primeRank_le_iff_elementary_card_le D).mp hr E hE)
    have hl : 4 ≤ (centralizer (A : Set G)).relIndex Z₀ := by
      apply transport_center_lower h d ht A hAL hAQ
      intro E hE hEL hEQ
      let := hE
      exact source_moving_rank_one_square_bound h d hc hab hd hb hcomm w hm
        (quotient_at_same_type F d ht e) hr hSc E hEL hEQ
    omega
  cases models a with
  | linear n hn hi =>
    obtain ⟨K,_,_,hK,⟨e⟩⟩ := hi
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hK)
    let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact source_reciprocal_linear_escape_of_factor_bound h hB d hc hab hd hb hcomm
      models hne hn (show Nat.card (ULift.{u} K) = 2^n by simpa using hK)
      (f.trans (linear_field_lift K)) hfactor hreverse
  | suzuki m hi =>
    let e := hi.some
    have hu : (Q F a).relIndex A ≤ 2^(2*m+1) :=
      elementary_core_index h d a A hAL e (2^(2*m+1))
      (fun E hE => @suzuki_elementary_card m E hE)
    have hl : (2^(2*m+1))^2 ≤ (centralizer (A : Set G)).relIndex Z₀ := by
      apply transport_center_lower h d ht A hAL hAQ
      intro E hE hEL hEQ
      let := hE
      exact source_moving_suzuki_field_square_bound h d hc hab hd hb hcomm w hm m
        (quotient_at_same_type F d ht e) E hEL hEQ
    have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
    nlinarith
  | projective_unitary n hn hi =>
    obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    by_cases hn2 : 2 ≤ n
    · apply square_contradiction
      apply center_elementary_square h d a hz e
      · intro ρ hnt hfix E hE
        let := hE
        exact psu3_elementary_square_bound J hn2 hK hconj ρ hnt hfix E
      · exact hAL
    · have hn1 : n = 1 := by omega
      apply small_contradiction e
      · simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
      · intro S
        have hh := HermitianForm.BinarySylowOrder.cube_le_sylow_card J (by omega) hK hconj S
        norm_num [hn1] at hh
        omega
  | special_unitary n hn hi =>
    obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    by_cases hn2 : 2 ≤ n
    · apply square_contradiction
      apply center_elementary_square h d a hz e
      · intro ρ hnt hfix E hE
        let := hE
        exact su3_elementary_square_bound J hn2 hK hconj ρ hnt hfix E
      · exact hAL
    · have hn1 : n = 1 := by omega
      apply small_contradiction e
      · rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
          J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
        simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
      · intro S
        let T := S.mapSurjective (f := J.specialToProjective) J.specialToProjective_surjective
        have hh := HermitianForm.BinarySylowOrder.cube_le_sylow_card J (by omega) hK hconj T
        have hle : Nat.card T ≤ Nat.card S := Nat.card_le_card_of_surjective
          (fun s : S => (⟨J.specialToProjective s,mem_map_of_mem _ s.property⟩ : T)) (by
            rintro ⟨_,s,hs,rfl⟩
            exact ⟨⟨s,hs⟩,rfl⟩)
        norm_num [hn1] at hh
        omega
  | dihedral hi =>
    let e := hi.some
    have hu : (Q F a).relIndex A ≤ 2 := elementary_core_index h d a A hAL e 2
      (fun E hE => @dihedral_elementary_card E hE)
    have hl : 4 ≤ (centralizer (A : Set G)).relIndex Z₀ := by
      apply transport_center_lower h d ht A hAL hAQ
      intro E hE hEL hEQ
      let := hE
      exact source_moving_dihedral_field_square_bound h d hc hab hd hb hcomm w hm
        (quotient_at_same_type F d ht e) E hEL hEQ
    omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
