module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedBinary
public import Theory.SpecificGroups.SL2.ExchangedPairBorel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualOrbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel

/-!
# The actual exchanged PSL₂ Borel and its even field parameter

In the surviving exchanged component case, the cubic residual theorem
identifies O^{3′}(H) with the literal Sylow orbit K₀. The original E₉
quotient and two-perfectness put L₁ in K₀, so H=K₀T. The paired rank-one
calculation makes every proper overgroup of T in H solvable.

Choose the Borel through the actual (T ∩ K₀)-star. Solvability of L₁T
puts L₁ in its lift B, and 12.6.29 puts B in M. The original E₉ survives
the entire O₂(H) kernel; the Borel order then forces an even field
exponent and gives three-rank two. Conversely the solvable H ∩ M has
its orbit intersection in this same Borel, proving B=K₀ ∩ M and
H ∩ M=BT. Product coordinates retain the actual moving conjugation.

The final application keeps the escaping component and reduced actor
J=K₀L₁T in the same Hz, along with both component quotient carriers.
Earlier geometry remains explicit. Field order four, the normal-component
restrictions, module identifications and the terminal exclusions remain
obligations of the universal NaturalReduction assembly.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, using 1.2.2(a),
p.504, and 12.6.29, p.835. The paired Borel and cubic-residual calculations
are reused through their existing proved interfaces.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The literal T-orbit is O^{3′}(H) in the exchanged PSL₂ case.
This identity is proved inside the original H before changing any actor. -/
theorem SourceHypothesis.original_abelian_exchanged_threeResidual
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    (primeToResidual 3 H).map H.subtype = conjugateSpanBy K (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans
      (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn).1
  let eK := subgroupOfEquivOfLe hKH
  let e := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  have hmi : ClassicalGroup.IsPSL ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H))
      2 (2 ^ n) := hm.of_mulEquiv e
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  have hs : IsSimpleGroup ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) := by
    obtain ⟨F,_,_,hF,⟨f⟩⟩ := hmi
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [hF]; exact Nat.pow_le_pow_right (n := 2) (by decide) hn2)
    exact f.isSimpleGroup
  let := hs
  have hd : 3 ∣ Nat.card ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) := by
    obtain ⟨F,_,_,_,⟨f⟩⟩ := hmi
    rw [Nat.card_congr f.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 le_rfl
  have hr : primeRank 3 H ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup]
    exact S.original_star_three_rank D hZ z hz hH
  have he := Chapter1.Section02.nonnormal_component_threeResidual hK hi hd hr
    (.linear_even n hn2 hmi)
  have he' := congrArg (map H.subtype) he
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hKH,←MonoidHom.range_eq_map,range_subtype] at he'
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := fun heq =>
    hn (normal_of_sylow_span_eq H K T hKH hTH (Or.inr hi) heq)
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  rw [he',orbit_eq_two_conjugates H K H hKH le_rfl hi (hTH ht) htn,
    orbit_eq_two_conjugates H K T hKH hTH hi ht htn]

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Every proper overgroup of the original T inside the exchanged actor
is solvable, including the full two-core kernel. -/
theorem SourceHypothesis.original_abelian_exchanged_proper_overgroup_solvable
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n))
    {J : Subgroup G} (hTJ : (T : Subgroup G) ≤ J) (hJH : J < H) :
    Group.IsSolvable J := by
  let E := D.fullSetup hZ T z
  let O := conjugateSpanBy K (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hres := S.original_abelian_exchanged_threeResidual D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn hn2 hm
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans
      (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn).1
  obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hq : IsPGroup 3 (E.L₁ ⧸ pCore 2 E.L₁) :=
    (IsElementaryAbelian.isPGroup 3 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9).of_equiv e9.symm
  have hLO : E.L₁ ≤ O := marked_le_orbit H O E.L₁ hLH
    (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)) hq hres
  have hOT : O ⊔ (T : Subgroup G) = H := by
    rw [←hgen,sup_eq_left.mpr hLO]
  have hKT : K ⊔ (T : Subgroup G) = H := by
    apply le_antisymm (sup_le hKH hTH)
    rw [←hOT]
    exact sup_le (conjugateSpanBy_le le_sup_left
      (le_sup_right.trans (K ⊔ (T : Subgroup G)).le_normalizer)) le_sup_right
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let eqv : ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) ≃* SL(2,F) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).trans
      (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let : IsQuasisimple SL(2,F) := IsQuasisimple.of_mulEquiv
    (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  have hgeni : K.subgroupOf H ⊔ (T.subtype hTH : Subgroup H) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hKH hTH,hKT,subgroupOf_self]
  let : Group.IsSolvable (J.subgroupOf H) :=
    Matrix.SpecialLinearGroup.ExchangedPair.component_pair_proper_overgroup_solvable
      (T.subtype hTH) (K.subgroupOf H) hK eqv hi hgeni (J.subgroupOf H)
      (subgroupOf_mono H hTJ) (fun he => hJH.not_ge (subgroupOf_eq_top.mp he))
  exact Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hJH.le).toMonoidHom)
    (subgroupOfEquivOfLe hJH.le).surjective

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Construct the marked Borel on the actual quotient, identify its lift
with K₀ ∩ M and H ∩ M with BT, and force an even field exponent. -/
theorem SourceHypothesis.original_abelian_exchanged_borel
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    ∃ (t : G) (ht : t ∈ T) (hTH : (T : Subgroup G) ≤ H),
      t ∉ normalizer (K : Set G) ∧
      ∃ (hOH : conjugateSpanBy K (T : Subgroup G) ≤ H)
        (e : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
          actorImage H K × actorImage H K)
        (P : Sylow 2 (actorImage H (conjugateSpanBy K (T : Subgroup G)))),
        let O := conjugateSpanBy K (T : Subgroup G)
        let Bstar := SylowBorel.relativeBorel (actorImage H O) P
        let B := borelLift H O hOH Bstar
        (∀ a b, (e.symm (a,b) : H ⧸ pCore 2 H) = (a : H ⧸ pCore 2 H) *
          (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩ * b *
            (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩)⁻¹)) ∧
        (P : Subgroup (actorImage H O)).map (actorImage H O).subtype =
          actorImage H ((T : Subgroup G) ⊓ O) ∧
        actorImage H B = Bstar ∧ Group.IsSolvable B ∧
        (D.fullSetup hZ T z).L₁ ≤ B ∧ B ≤ M L ∧
        (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
        Even n ∧ primeRank 3 B = 2 ∧
        O ⊔ (T : Subgroup G) = H ∧ B = O ⊓ M L ∧
        H ⊓ M L = B ⊔ (T : Subgroup G) := by
  let E := D.fullSetup hZ T z
  let O := conjugateSpanBy K (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hOH : O ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have hres := S.original_abelian_exchanged_threeResidual D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn hn2 hm
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans
      (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn).1
  have hmoving : O ≠ K := fun heq =>
    hn (normal_of_sylow_span_eq H K T hKH hTH (Or.inr hi) heq)
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  have ho := orbit_eq_two_conjugates H K T hKH hTH hi ht htn
  have hmstar := hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  have hqs : IsQuasisimple (actorImage H K) :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  obtain ⟨e₀,he₀⟩ := exists_moving_star_coordinates H K hKH hK hqs (hTH ht) htn hmstar
  have hcoords : ∃ e : actorImage H O ≃* actorImage H K × actorImage H K,
      ∀ a b, (e.symm (a,b) : H ⧸ pCore 2 H) = (a : H ⧸ pCore 2 H) *
        (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩ * b *
          (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩)⁻¹) := by
    let e' : actorImage H O ≃* actorImage H K × actorImage H K :=
      (MulEquiv.subgroupCongr (congrArg (actorImage H) ho)).trans e₀.symm
    exact ⟨e',fun a b => he₀ a b⟩
  obtain ⟨e,he⟩ := hcoords
  have hOn : (O.subgroupOf H).Normal := by
    dsimp only [O]
    rw [←hres]
    change (((primeToResidual 3 H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  let := hOn
  have hp : IsPPerfect 2 E.L₁ := isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)
  obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hq : IsPGroup 3 (E.L₁ ⧸ pCore 2 E.L₁) :=
    (IsElementaryAbelian.isPGroup 3 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9).of_equiv e9.symm
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  let : Group.IsNilpotent (pCore 2 E.L₁) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (E.L₁ ⧸ pCore 2 E.L₁) := hq.isNilpotent
  let : Group.IsSolvable E.L₁ :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 E.L₁)).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (E.L₁ ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes E.L₁ T hTL
  have hTs : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨P,hP,hstar,hsol,hLB,hBM,hnB⟩ := exists_source_borel H O E.L₁ T H (M L)
    hOH hLH hTs e hn2 hmstar hp hq hres hOH (sup_le hLH hTH) (by
      intro J hJ _ hs
      let := hs
      exact S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns
        (le_sup_right.trans hJ))
  let Bstar := SylowBorel.relativeBorel (actorImage H O) P
  let B := borelLift H O hOH Bstar
  have hthree : 3 ∣ Nat.card Bstar := by
    let R : Sylow 3 E.L₁ := Classical.choice inferInstance
    let R₀ := (R : Subgroup E.L₁).map E.L₁.subtype
    have hRB : actorImage H R₀ ≤ Bstar := by
      have hh : actorImage H R₀ ≤ actorImage H B :=
        map_mono (comap_mono ((map_subtype_le _).trans hLB))
      exact hh.trans_eq hstar
    have hc : Nat.card (actorImage H R₀) = 9 :=
      (S.original_point_sylow_star D hZ z hz hTz hH R).2.1
    exact (by decide : 3 ∣ 9).trans (hc ▸ card_dvd_of_le hRB)
  have heven := SylowBorel.even_of_three_dvd (actorImage H O) e P hn2 hmstar hthree
  have hBrank : primeRank 3 B = 2 :=
    (borelLift_threeRank H O hOH Bstar (SylowBorel.relativeBorel_le _ P)).trans
      (SylowBorel.threeRank _ e P hn2 hmstar heven)
  have hLO : E.L₁ ≤ O := hLB.trans (borelLift_le H O hOH Bstar)
  have hOH' : O ⊔ (T : Subgroup G) = H := by
    rw [←hgen,sup_eq_left.mpr hLO]
  have hTM : (T : Subgroup G) ≤ M L := S.chosen.sylow_normalizes_component
  let : Group.IsSolvable (H ⊓ M L : Subgroup G) :=
    S.original_abelian_exchanged_proper_overgroup_solvable D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hn2 hm (le_inf hTH hTM)
      (lt_of_le_of_ne inf_le_left (fun he => hH.2.2 (he ▸ inf_le_right)))
  let A := actorImage H (H ⊓ M L)
  let J := actorImage H (O ⊓ M L)
  let : Group.IsSolvable ((H ⊓ M L : Subgroup G).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe (show (H ⊓ M L : Subgroup G) ≤ H from inf_le_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show (H ⊓ M L : Subgroup G) ≤ H from inf_le_left)).injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((H ⊓ M L : Subgroup G).subgroupOf H))
  have hJA : J ⊔ actorImage H T ≤ A := sup_le
    (map_mono (comap_mono (inf_le_inf_right (M L) hOH)))
    (map_mono (comap_mono (le_inf hTH hTM)))
  let : Group.IsSolvable (J ⊔ actorImage H T : Subgroup (H ⧸ pCore 2 H)) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hJA) (inclusion_injective hJA)
  have hJB : J ≤ Bstar := SylowBorel.contains_marked (actorImage H O) J (actorImage H T)
    e P hn2 hmstar (map_mono (comap_mono inf_le_left)) (hP.le.trans inf_le_left)
  have hBeq : B = O ⊓ M L := by
    apply le_antisymm (le_inf (borelLift_le H O hOH Bstar) hBM)
    intro x hx
    apply (mem_borelLift_iff H O hOH Bstar x).mpr
    exact ⟨hx.1,hJB (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H))
      (show (⟨x,hOH hx.1⟩ : H) ∈ (O ⊓ M L : Subgroup G).subgroupOf H from hx))⟩
  have hTO : (T : Subgroup G) ≤ normalizer (O : Set G) :=
    le_normalizer_conjugateSpanBy K T
  have hMeq : H ⊓ M L = B ⊔ (T : Subgroup G) := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ O ⊔ (T : Subgroup G) := hOH'.symm ▸ hx.1
      change x ∈ ((O ⊔ (T : Subgroup G) : Subgroup G) : Set G) at hx'
      rw [coe_mul_of_right_le_normalizer_left O T hTO] at hx'
      obtain ⟨o,ho,t',ht',heq⟩ := hx'
      have hoM : o ∈ M L := by
        have hh := (M L).mul_mem hx.2 ((M L).inv_mem (hTM ht'))
        rwa [←heq,mul_inv_cancel_right] at hh
      rw [←heq]
      exact mul_mem_sup (hBeq.symm ▸ (show o ∈ O ⊓ M L from ⟨ho,hoM⟩)) ht'
    · exact sup_le (le_inf ((borelLift_le H O hOH Bstar).trans hOH) hBM) (le_inf hTH hTM)
  exact ⟨t,ht,hTH,htn,hOH,e,P,he,hP.trans (starImage_inf_sylow H O T hTs).symm,
    hstar,hsol,hLB,hBM,hnB,heven,hBrank,hOH',hBeq,hMeq⟩

include hz hTV hTz hbound hTI hns hH in
/-- Apply the Borel construction to the original reduced actor. In the
exchanged case the field exponent is even, K₀ is the cubic residual,
and its actual overlap with M is the solvable Borel lift. -/
theorem SourceHypothesis.original_abelian_reduced_even_Lie_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianLieHigherFieldModel (actorImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ∃ n : ℕ, 2 ≤ n ∧ Even n ∧
            ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
            ClassicalGroup.IsPSL (actorImage J K) 2 (2 ^ n) ∧
            (primeToResidual 3 J).map J.subtype = K₀ ∧
            (D.fullSetup hZ T z).L₁ ≤ K₀ ⊓ M L ∧
            K₀ ⊔ (T : Subgroup G) = J ∧
            J ⊓ M L = (K₀ ⊓ M L) ⊔ (T : Subgroup G) ∧
            Group.IsSolvable (K₀ ⊓ M L : Subgroup G) ∧
            primeRank 3 (K₀ ⊓ M L : Subgroup G) = 2 ∧
            (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
              normalizer ((K₀ ⊓ M L : Subgroup G) : Set G))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_Lie_component_models D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with hnormal | ⟨hn,hi,n,hn2,hm,hmstar⟩
  · exact Or.inl hnormal
  · obtain ⟨t,ht,hTJ,htn,hOJ,e,P,he,hP,hstar,hsol,hLB,hBM,hnB,heven,hBrank,hOT,hBeq,hMeq⟩ :=
      S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
        hJ hKle hKJ rfl hn hn2 hm
    exact Or.inr ⟨hn,hi,n,hn2,heven,hm,hmstar,
      S.original_abelian_exchanged_threeResidual D hZ z hz hTV hTz hbound hTI hns
        hJ hKle hKJ rfl hn hn2 hm,
      hBeq ▸ hLB,hOT,by simpa only [hBeq] using hMeq,
      hBeq ▸ hsol,hBeq ▸ hBrank,by simpa only [hBeq] using hnB⟩

end CFSG.Quasithin.Chapter12.Section06
