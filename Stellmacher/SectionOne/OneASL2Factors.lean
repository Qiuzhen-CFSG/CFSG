module
public import Stellmacher.SectionOne.SL2ProductNormalizerRigidity
public import Stellmacher.SectionOne.OneARelativeAction
public import Stellmacher.SectionOne.LemmaOneSixSmallM
public import Stellmacher.SectionOne.RankOneLocalFullCoordinate
public import Theory.GroupAction.FixedQuotientCommutator


/-!
# Local SL₂(2) factors for offender subgroups

For a nontrivial member A of the offender family, this module writes
E=[O₂′(G),A]A as a product of SL₂(2) factors. Every factor has a
four-point action module, its derived order-three subgroup is an ambient
omega factor, and it is normal in its join with the ambient odd core.

The faithful relative setup and the proved m≤1 classification supply the
same local factor family and Sylow coordinates. A coordinate has full
fixed index two. On the corresponding four-point derived-factor module
it also has fixed index two, forcing its entire action commutator into
that module; adjoining the derived factor therefore still gives exactly
four points. Injective subgroup transport preserves the product and these
cardinalities.

For normality, put W=O₂′(G). The elementary commutator inclusion
[W,[W,A]A]≤[W,A] and the local derived-factor generation imply that W
normalizes E and acts trivially on E/E′. The SL₂(2) product rigidity
theorem then shows W normalizes every factor. This retains precisely the
ambient normality required to place the factors in the global family used
in (1.7).

Source: the first paragraph of the proof of Stellmacher (1.7), journal p.19,
in `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Stellmacher.SectionOne
open RankOneThreeGroupAssembly
universe u v

private theorem factor_eq_derived_sup_coordinate
    {G : Type u} [Group G] [Finite G]
    (D Q : Subgroup G) (hD : IsSL2Two D)
    (hFcard : Nat.card ((commutator D).map D.subtype) = 3)
    (hQcard : Nat.card Q = 2) (hQD : Q ≤ D) :
    D = (commutator D).map D.subtype ⊔ Q := by
  let F := (commutator D).map D.subtype
  have hFD : F ≤ D := Subgroup.map_subtype_le _
  have hjoin : F ⊔ Q ≤ D := sup_le hFD hQD
  have hthree : 3 ∣ Nat.card (F ⊔ Q : Subgroup G) := by
    rw [← hFcard]
    exact Subgroup.card_dvd_of_le le_sup_left
  have htwo : 2 ∣ Nat.card (F ⊔ Q : Subgroup G) := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le le_sup_right
  have hsix : 6 ∣ Nat.card (F ⊔ Q : Subgroup G) := by
    exact (show Nat.Coprime 3 2 by decide).mul_dvd_of_dvd_of_dvd hthree htwo
  apply (Subgroup.eq_of_le_of_card_ge hjoin ?_).symm
  rw [isSL2Two_card hD]
  exact Nat.le_of_dvd Nat.card_pos hsix

private theorem factor_action_card_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D Q : Subgroup G) (hD : IsSL2Two D)
    (hF : oneOmega (G := G) (V := V) ((commutator D).map D.subtype))
    (hQD : Q ≤ D) (hQcard : Nat.card Q = 2)
    (hcomm : ⁅(commutator D).map D.subtype, Q⁆ =
      (commutator D).map D.subtype)
    (hfull : (Nat.card V : ℚ) / Nat.card (FixedPoints.subgroup Q V) = 2) :
    Nat.card (commutatorAction D V) = 4 := by
  let F := (commutator D).map D.subtype
  let U : Subgroup V := commutatorAction F V
  have hnorm : Q ≤ Subgroup.normalizer F :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm.le
  let hUinv : IsInvariant Q V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor Q F hnorm
  let _ : IsInvariant Q V U := hUinv
  let _ : IsElementaryAbelian 2 U := isElementaryAbelian_subgroup U
  have hne : commutatorAction Q U ≠ ⊥ := by
    intro hbot
    apply oneOmega_full_commutator_nontrivial F Q hF hcomm
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact congrArg Subtype.val
      (actsTrivially_of_commutatorAction_eq_bot hbot (⟨q, hq⟩ : Q) (⟨v, hv⟩ : U))
  have hfixU : Nat.card (FixedPoints.subgroup Q U) = 2 :=
    (cardTwo_action_fixed_card_two hQcard hF.2.2 hne).1
  have hfixIntersection : Nat.card (U ⊓ FixedPoints.subgroup Q V : Subgroup V) = 2 := by
    rw [← fixedPoints_subgroup_map_subtype_eq_inf U,
      Subgroup.card_map_of_injective U.subtype_injective]
    exact hfixU
  have hfullNat : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Q V) := by
    have hpos : (Nat.card (FixedPoints.subgroup Q V) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup Q V)).ne'
    exact_mod_cast (div_eq_iff hpos).mp hfull
  have hQcomm : commutatorAction Q V ≤ U := by
    apply (commutatorAction_le_of_fixed_card_product_eq U ?_).2
    rw [hfixIntersection, show Nat.card U = 4 from hF.2.2, hfullNat]
    omega
  have hDjoin : D = F ⊔ Q :=
    factor_eq_derived_sup_coordinate D Q hD hF.2.1 hQcard hQD
  have hsup : commutatorAction (F ⊔ Q : Subgroup G) V =
      commutatorAction F V ⊔ commutatorAction Q V := by
    simpa [iSup_bool_eq] using (commutatorAction_eq_iSup_of_eq_iSup
      (A := F ⊔ Q) (fun b : Bool => if b then F else Q) (by simp [iSup_bool_eq]))
  rw [hDjoin, hsup, sup_eq_left.mpr hQcomm]
  exact hF.2.2


private theorem internalDirectProduct_map_injective
    {G : Type u} {H : Type v} [Group G] [Group H] [DecidableEq (Subgroup H)]
    (f : G →* H) (hf : Function.Injective f)
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F) :
    IsInternalDirectProduct (E.map f) (F.image (Subgroup.map f)) := by
  classical
  have hDE (D : Subgroup G) (hD : D ∈ F) : D ≤ E := by
    rw [hprod.1]
    exact le_iSup (fun K : {K // K ∈ F} => (K : Subgroup G)) ⟨D,hD⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprod.1, Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le ?_
      intro D
      exact le_iSup (fun K : {K // K ∈ F.image (Subgroup.map f)} =>
        (K : Subgroup H)) ⟨D.val.map f, Finset.mem_image.mpr ⟨D,D.property,rfl⟩⟩
    · refine iSup_le ?_
      intro D
      obtain ⟨K,hK,hKD⟩ := Finset.mem_image.mp D.property
      rw [← hKD]
      exact le_iSup (fun K : {K // K ∈ F} => K.val.map f) ⟨K,hK⟩
  · intro D hD
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hD
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_mono (hDE K hK))).mpr
    apply Subgroup.le_normalizer_iff.mpr
    rintro e ⟨x,hx,rfl⟩ d ⟨y,hy,rfl⟩
    have hnorm : E ≤ Subgroup.normalizer K :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hDE K hK)).mp (hprod.2.1 K hK)
    refine ⟨x*y*x⁻¹, (Subgroup.mem_normalizer_iff.mp (hnorm hx) y).mp hy, ?_⟩
    simp
  · intro D hD K hK hne
    obtain ⟨D₀,hD₀,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨K₀,hK₀,rfl⟩ := Finset.mem_image.mp hK
    apply Subgroup.disjoint_map hf
    exact hprod.2.2.1 D₀ hD₀ K₀ hK₀ (fun he => hne (congrArg (Subgroup.map f) he))
  · intro D hD K hK hne x hx y hy
    obtain ⟨D₀,hD₀,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨K₀,hK₀,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨x₀,hx₀,rfl⟩ := hx
    obtain ⟨y₀,hy₀,rfl⟩ := hy
    simpa using congrArg f (hprod.2.2.2 D₀ hD₀ K₀ hK₀
      (fun he => hne (congrArg (Subgroup.map f) he)) x₀ hx₀ y₀ hy₀)

private theorem commutatorAction_map_subtype
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (E : Subgroup G) (D : Subgroup E) :
    commutatorAction (D.map E.subtype) V = commutatorAction D V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨d,v,rfl⟩
    obtain ⟨d₀,hd₀,heq⟩ := d.property
    refine ⟨⟨d₀,hd₀⟩,v,?_⟩
    change v⁻¹ * (d : G) • v = v⁻¹ * (d₀ : G) • v
    change (d₀ : G) = (d : G) at heq
    rw [heq]
  · rintro ⟨d,v,rfl⟩
    exact ⟨⟨((d : E) : G), Subgroup.mem_map_of_mem E.subtype d.property⟩,v,rfl⟩

private theorem derived_map_subtype
    {G : Type u} [Group G] (E : Subgroup G) (D : Subgroup E) :
    (commutator (D.map E.subtype)).map (D.map E.subtype).subtype =
      ((commutator D).map D.subtype).map E.subtype := by
  simp only [Subgroup.map_subtype_commutator, Subgroup.map_commutator]


private theorem commutator_local_join_le
    {G : Type u} [Group G] (W A : Subgroup G) :
    ⁅W, ⁅W,A⁆ ⊔ A⁆ ≤ ⁅W,A⁆ := by
  let H : Subgroup G := W ⊔ A
  let C : Subgroup G := ⁅W,A⁆
  let E : Subgroup G := C ⊔ A
  have hCH : C ≤ H := Subgroup.commutator_le_sup W A
  have hEH : E ≤ H := sup_le hCH le_sup_right
  let CH := C.subgroupOf H
  let WH := W.subgroupOf H
  let AH := A.subgroupOf H
  let EH := E.subgroupOf H
  let _ : CH.Normal := Subgroup.normal_subgroupOf_commutator_sup W A
  have hcomm : ⁅WH, AH⁆ = CH := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right,
      Subgroup.map_subgroupOf_eq_of_le hCH]
  have hsup : EH = CH ⊔ AH :=
    Subgroup.subgroupOf_sup hCH le_sup_right
  let q := QuotientGroup.mk' CH
  have hmapC : CH.map q = ⊥ := by
    exact (Subgroup.map_eq_bot_iff (f := q) (H := CH)).mpr (by simp [q])
  have hmapE : EH.map q = AH.map q := by rw [hsup, Subgroup.map_sup, hmapC, bot_sup_eq]
  have hcommbot : ⁅WH, EH⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator, hmapE, ← Subgroup.map_commutator, hcomm, hmapC]
  have hle : ⁅WH, EH⁆ ≤ CH := by
    simpa [q] using (Subgroup.map_eq_bot_iff (f := q) (H := ⁅WH, EH⁆)).mp hcommbot
  have hmaple := Subgroup.map_mono (f := H.subtype) hle
  rw [commutator_subgroupOf_map_eq H E W hEH le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le hCH] at hmaple
  exact hmaple



private theorem oneA_sl2_factors_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hA : oneA (G := G) (V := V) (S : Subgroup G) A) (hAne : A ≠ ⊥) :
    let E := ⁅oddCore G,A⁆ ⊔ A
    (∃ F : Finset (Subgroup G),
      IsInternalDirectProduct E F ∧
      ∀ D : Subgroup G, D ∈ F →
        IsSL2Two D ∧ oneOmega (G := G) (V := V) ((commutator D).map D.subtype) ∧
        Nat.card (commutatorAction D V) = 4) ∧
    oddCore G ≤ Subgroup.normalizer (E : Set G) ∧
    ⁅oddCore G,E⁆ ≤ (commutator E).map E.subtype := by
  classical
  let E : Subgroup G := ⁅oddCore G,A⁆ ⊔ A
  obtain ⟨T,hTA,hE,hT,hW,hm,hmin⟩ := oneA_relative_rank_one_setup h S A hA hAne
  have hdata := lemma_one_six_sl2_of_m_le_one hE T hT hW hmin hm.le
  obtain ⟨F,hEF,hprod,hodd,hcoord⟩ := rankOneLocalSL2Data_full_coordinates T hdata hm
  have hCoreMap : (oddCore E).map E.subtype = ⁅oddCore G,A⁆ :=
    oneA_relative_oddCore_map h S A hA hAne
  have hactorMap : (oddCore E ⊔ (T : Subgroup E)).map E.subtype = E := by
    rw [Subgroup.map_sup,hCoreMap,hTA,Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  have hFle : oddCore E ≤ commutator E := by
    rw [hodd]
    refine iSup_le ?_
    intro D
    rw [Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hderived : ⁅oddCore G,A⁆ ≤ (commutator E).map E.subtype := by
    rw [← hCoreMap]
    exact Subgroup.map_mono hFle
  have hcomm : ⁅oddCore G,E⁆ ≤ ⁅oddCore G,A⁆ := commutator_local_join_le (oddCore G) A
  refine ⟨?_, Subgroup.le_normalizer_iff_commutator_le_right.mpr
    (hcomm.trans le_sup_left), hcomm.trans hderived⟩
  refine ⟨F.image (Subgroup.map E.subtype), ?_, ?_⟩
  · have hp := internalDirectProduct_map_injective E.subtype E.subtype_injective
      (oddCore E ⊔ (T : Subgroup E)) F hprod
    rwa [hactorMap] at hp
  · intro D hD
    obtain ⟨D₀,hD₀,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hSL,hOmega⟩ := hEF D₀ hD₀
    have hSLMap : IsSL2Two (D₀.map E.subtype) := by
      obtain ⟨eSL⟩ := hSL
      exact ⟨(Subgroup.equivMapOfInjective D₀ E.subtype E.subtype_injective).symm.trans eSL⟩
    refine ⟨hSLMap, ?_, ?_⟩
    · rw [derived_map_subtype]
      refine ⟨?_, ?_, ?_⟩
      · have hle := Subgroup.map_mono (f := E.subtype) hOmega.1
        rw [hCoreMap] at hle
        let _ : (oddCore G).Normal := pPrimeCore_normal
        exact hle.trans (Subgroup.commutator_le_left (oddCore G) A)
      · rw [Subgroup.card_map_of_injective E.subtype_injective]
        exact hOmega.2.1
      · rw [commutatorAction_map_subtype]
        exact hOmega.2.2
    · rw [commutatorAction_map_subtype]
      obtain ⟨hQcard,hcommQ,_hindex,hfull⟩ := hcoord D₀ hD₀
      exact factor_action_card_four D₀ ((T : Subgroup E) ⊓ D₀)
        hSL hOmega inf_le_right hQcard hcommQ hfull



public theorem oneA_sl2_factors
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hA : oneA (G := G) (V := V) (S : Subgroup G) A) (hAne : A ≠ ⊥) :
    ∃ F : Finset (Subgroup G),
      IsInternalDirectProduct (⁅oddCore G,A⁆ ⊔ A) F ∧
      ∀ D : Subgroup G, D ∈ F →
        IsSL2Two D ∧
        oneOmega (G := G) (V := V) ((commutator D).map D.subtype) ∧
        Nat.card (commutatorAction D V) = 4 ∧
        (D.subgroupOf (oddCore G ⊔ D)).Normal := by
  obtain ⟨⟨F,hprod,hF⟩,hnorm,hquot⟩ := oneA_sl2_factors_data h S A hA hAne
  have hnormal := sl2_product_normalized_of_trivial_derived_quotient_action
    (⁅oddCore G,A⁆ ⊔ A) (oddCore G) F hprod
    (fun D hD => (hF D hD).1) hnorm hquot
  refine ⟨F,hprod,?_⟩
  intro D hD
  obtain ⟨hSL,hOmega,hcard⟩ := hF D hD
  refine ⟨hSL,hOmega,hcard,?_⟩
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
  exact sup_le (hnormal D hD) D.le_normalizer

end Stellmacher.SectionOne
