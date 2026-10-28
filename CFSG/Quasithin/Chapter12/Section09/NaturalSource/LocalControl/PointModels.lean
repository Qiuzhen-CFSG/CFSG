module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.SevenCore
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourFinite
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Models
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.Mathieu.M22.Properties.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.QuadraticActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction

/-!
# The three surviving point quotients in the abelian natural branch

F.9.16 supplies a quadratic actor in the image of the original R₁ inside
J/O₂(J), for J = K₁T. The image of K₁ is normal, and L₁T supplements it.
Since the two-core of the quotient is trivial, the R₁ image has trivial
intersection with the component centralizer. Thus the quadratic actor acts
faithfully on that component. The proved F.9.18 group-model theorem applies
to this literal action and transports through K₁/O₂(K₁) ≃ K₁*.

In degree four the earlier seven-core argument gives quasisimplicity;
A.3.6 identifies the central covers. The original component comparisons
force equality with L₁ in every unwanted classical row, contrary to
K₁T escaping the original normalizer. The finite-cover comparisons exclude
3.A₆ and both Mathieu rows. In degree five the original normalized local
A₈ section survives the quotient and the restriction to a component Sylow.
It excludes the Bender, rank-two, alternating-seven and Mathieu rows and
all central three-covers. Consequently both degrees leave exactly A₇,
PSL₄(2), or PSL₅(2), with actual group isomorphisms.

This proves the model clause 12.9.5(2) assuming the preceding K₁T ∈ Hz
clause. LocalControl applies it to the original local-control record.
The point and plane centralizer bounds and preceding membership clause
remain source obligations; no classification input is assumed here.

Source: Aschbacher--Smith, 12.9.5(2), printed pp.860--861;
F.9.18(4), pp.325--326; and A.3.6, pp.43--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter13.Section08.SolvableExclusion.Three
open Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The complete F.9.18 group-model clause on the original point component,
with the quadratic actor in R₁ and its faithful conjugation action proved. -/
theorem point_quotient_f918_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (hJ : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G))) :
    Chapter13.Section08.Components.Models.F918Models (C.K1 ⧸ pCore 2 C.K1) := by
  have hqs : IsQuasisimple (C.K1 ⧸ pCore 2 C.K1) := by
    rcases hn with rfl | rfl
    · exact four_point_quasisimple_of_abelian_join h earlier F hab C hJ
    · exact Components.five_endpoint_component_quasisimple h earlier F 1 (Or.inl rfl)
        C.K1 ⟨C.point_le,C.component⟩ C.contains
  let J := C.K1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le C.point_le (F.invariant 1)
  let N := C.K1.subgroupOf J
  have hN : N.IsCComponent := C.component.subgroupOf_of_le le_sup_left hJH
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal))
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := N.map q
  let : D.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  let e₀ : N ≃* C.K1 := subgroupOfEquivOfLe le_sup_left
  let e : (C.K1 ⧸ pCore 2 C.K1) ≃* D :=
    (QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)).symm.trans
      (cComponentTwoCoreQuotientEquiv hN)
  let : IsQuasisimple D := hqs.of_mulEquiv e
  have hsJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Components.Gi_twoLocal h F 1 (by decide))).subgroup _)
  have hsQ := ChapterE.Structure.sqtk_two_quotient hsJ (pCore 2 J) pCore_isPGroup
  have hcenter : Nat.card (center D) = 1 ∨ Nat.card (center D) = 3 := by
    rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
        hsQ (pCore_quotient_pCore_eq_bot 2) (hN.map_quotient _) with ⟨hs,_⟩ | ⟨⟨e⟩,_⟩
    · let := hs
      exact Or.inl (Subgroup.card_eq_one.mpr
        Chapter13.Section08.Components.CoverModels.center_eq_bot_of_simple)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3))
  obtain ⟨hU,a,_,B,hBR,hA,hquad,hbound⟩ := abelian_local_quadratic_actor h earlier F hab J hJ
  let := hU
  let E := F.Li L 1 ⊔ (T : Subgroup G)
  let R := Chapter13.Section08.Source.starImage J E
  let R₂ := Chapter13.Section08.Source.starImage J (F.Ri L 1)
  have hEJ : E ≤ J := sup_le (C.contains.trans le_sup_left) le_sup_right
  have hcover : C.K1 ⊔ E = J := by
    apply le_antisymm (sup_le le_sup_left hEJ)
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hgen : D ⊔ R = ⊤ := by
    change (C.K1.subgroupOf J).map q ⊔ (E.subgroupOf J).map q = ⊤
    rw [←Subgroup.map_sup,←subgroupOf_sup (show C.K1 ≤ J from le_sup_left) hEJ,
      hcover,subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hRtwo : IsPGroup 2 R₂ := starImage_isPGroup J _ (isPGroup_pCoreIn 2 E)
  have hnorm : R ≤ normalizer (R₂ : Set (J ⧸ pCore 2 J)) :=
    starImage_normalizes J (le_normalizer_pCoreIn 2 E)
  have hfaith : R₂ ⊓ centralizer (D : Set (J ⧸ pCore 2 J)) = ⊥ :=
    centralizer_inf_eq_bot_of_supplement D R R₂ hgen hRtwo hnorm
      (pCore_quotient_pCore_eq_bot 2)
  have hBfaith : B.map q ⊓ centralizer (D : Set (J ⧸ pCore 2 J)) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (map_mono hBR)).trans hfaith.le)
  exact Chapter13.Section08.Components.SourceModels.f918Models_transport e
    (Chapter13.Section08.Components.SourceModels.f918Models_of_quadratic_actor
      a.representation D (B.map q) a.faithful hcenter hsQ hA hquad hbound hBfaith)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource


namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter1.Section02.LocalModels
open Chapter13.Section08.Components.Models
open Chapter13.Section08.Components.CoverModels
universe u

private theorem symplectic_derived_models {X : Type*} [Group X]
    {k : ℕ} (hk : 1 ≤ k) (hm : IsSp4DerivedAt X (2 ^ k)) :
    (2 ≤ k ∧ ClassicalGroup.IsPSp X 2 (2 ^ k)) ∨
      Nonempty (X ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases h1 : k = 1
  · right
    exact ⟨(e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (by simpa [h1] using hF))).trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩
  · have hk2 : 2 ≤ k := by omega
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact Or.inl ⟨hk2,F,inferInstance,inferInstance,hF,
      ⟨(e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hk2)).trans
        Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩

private theorem g2_derived_models {X : Type*} [Group X]
    {k : ℕ} (hk : 1 ≤ k) (hm : IsG2DerivedAt X (2 ^ k)) :
    (2 ≤ k ∧ ClassificationModels.IsG2At X (2 ^ k)) ∨
      Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases h1 : k = 1
  · right
    exact ⟨e.trans (Atlas.G2.DerivedEvenOrder.derivedFieldEquiv
      (Atlas.G2.binaryFieldEquiv (by simpa [h1] using hF)))⟩
  · exact Or.inl ⟨by omega,F,inferInstance,inferInstance,hF,
      ⟨e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hF)⟩⟩

private theorem threeCover_transport {X Y : Type*} {S : Type}
    [Group X] [Group Y] [Group S] (e : X ≃* Y) (h : IsThreeCover Y S) :
    IsThreeCover X S := by
  let : IsQuasisimple Y := h.1
  exact ⟨IsQuasisimple.of_mulEquiv e.symm,
    h.2.1.map ((centerCongr e).trans ·),
    h.2.2.map ((Chapter13.Section08.Components.SourceModels.centralQuotientEquiv e).trans ·)⟩

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem four_point_models_of_catalogue
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (C : ComponentGeometry F L)
    (hlt : F.Li L 1 < C.K1)
    (hm : ComponentModelOrSuzuki (C.K1 ⧸ pCore 2 C.K1)) :
    IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
  have hK : C.K1 ∈ Chapter1.cComponentsIn F.H := ⟨C.point_le,C.component⟩
  have hne : F.Li L 1 ≠ C.K1 := hlt.ne
  rcases hm with hm | ⟨m,hm,he⟩
  · cases hm with
    | linear_two k hk hm =>
      exact (hne (Components.four_point_component_eq_of_bender h earlier F hK C.contains
        (.linear k hk hm))).elim
    | projective_three un k hk hm =>
      cases un
      · exact (hne (Components.four_point_component_eq_of_even_linear_three h earlier F
          hK C.contains hk hm)).elim
      · exact (hne (Components.four_point_component_eq_of_bender h earlier F hK C.contains
          (.unitary k hk hm))).elim
    | special_three un k hk _ hm =>
      exact (hne (Components.four_point_component_eq_of_even_classical_cover h earlier F
        hK C.contains (by cases un <;> exact Nat.zero_lt_of_lt hk) un hm)).elim
    | symplectic k hk hm =>
      rcases symplectic_derived_models hk hm with ⟨hk,hm⟩ | hm
      · exact (hne (Components.four_point_component_eq_of_even_symplectic h earlier F
          hK C.contains hk hm)).elim
      · exact (hne (Components.four_point_component_eq_of_even_rank_two h earlier F
          hK C.contains (.symplectic_derived hm))).elim
    | g2 k hk hm =>
      rcases g2_derived_models hk hm with ⟨hk,hm⟩ | hm
      · exact (hne (Components.four_point_component_eq_of_even_g2 h earlier F
          hK C.contains hk hm)).elim
      · exact (hne (Components.four_point_component_eq_of_binary_g2_derived h earlier F
          hK C.contains hm.some)).elim
    | linear_four hm => exact Or.inr (Or.inl hm)
    | linear_five hm => exact Or.inr (Or.inr hm)
    | alternating_seven hm => exact Or.inl hm
    | alternating_six_cover he =>
      exact (Components.four_point_component_not_alternating_six_cover h F C.contains
        (threeCover_transport he.some a6Triple_isThreeCover)).elim
    | mathieu he =>
      exact (Components.four_point_component_not_mathieuTwentyTwo h earlier F hK
        C.contains he.some).elim
    | mathieu_cover he =>
      let : IsSimpleGroup Sporadic.Mathieu.M22 := Sporadic.Mathieu.m22_isSimpleGroup
      exact (Components.four_point_component_not_mathieu_cover h earlier F hK C.contains
        (threeCover_transport he.some m22Triple_isThreeCover)).elim
  · exact (hne (Components.four_point_component_eq_of_bender h earlier F hK C.contains
      (.suzuki m hm he))).elim

/-- On the original abelian degree-four point span, the F.9.18 actor leaves
exactly the three source quotients. The preceding K₁T membership is explicit. -/
theorem four_point_models_of_abelian_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (hJ : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G))) :
    IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
  have hlt : F.Li L 1 < C.K1 := by
    refine lt_of_le_of_ne C.contains ?_
    intro he
    apply hJ.2.2
    rw [←he]
    exact sup_le (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer)
      (h.sylow_normalizes earlier.structural)
  let D := (C.K1.subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : Group.IsNilpotent (pCore 2 F.H) := pCore_isNilpotent
  let e₀ := subgroupOfEquivOfLe C.point_le
  let e : (C.K1 ⧸ pCore 2 C.K1) ≃* D :=
    (QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)).symm.trans
      (cComponentTwoCoreQuotientEquiv C.component)
  let : IsQuasisimple D := (four_point_quasisimple_of_abelian_join h earlier F hab C hJ).of_mulEquiv e
  have hsH : IsSQTK KnownSimple.IsKnownSimple F.H :=
    h.source.simpleQTKE.twoLocal_sqtk (Components.Gi_twoLocal h F 1 (by decide))
  have hs := ChapterE.Structure.sqtk_two_quotient hsH (pCore 2 F.H) pCore_isPGroup
  have ha := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    hs (pCore_quotient_pCore_eq_bot 2) (C.component.map_quotient _)
  have hf := Chapter13.Section08.Components.SourceModels.f918Models_transport e.symm
    (point_quotient_f918_models h (Or.inl rfl) earlier F hab C hJ)
  have hm := SourceApplication.classified_of_source hf (ha.elim (fun hs => Or.inl hs.1) Or.inr)
  apply four_point_models_of_catalogue h earlier F C hlt
  exact hm.elim (fun h => Or.inl (h.of_mulEquiv e))
    (fun ⟨m,hm,he⟩ => Or.inr ⟨m,hm,he.map (e.trans ·)⟩)


private theorem five_section_f918_models
    {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] [Group.IsPerfect X]
    (S : Sylow 2 X) (B : Subgroup X)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup X) ≤ normalizer (B : Set X))
    (hsec : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hm : F918Models X) : ClassicalGroup.IsPSL X 4 2 ∨ ClassicalGroup.IsPSL X 5 2 := by
  let e := centerQuotientEquiv (G := X) center_eq_bot_of_simple
  rcases hm with ⟨hm,_⟩ | he | hc
  · cases hm with
    | bender hm =>
      exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_linearFourTwo_section_of_bender_model
        S B hB hn hsec (hm.of_mulEquiv e)).elim
    | linear_three k hk hm =>
      exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_rankTwo S hB hn hsec
        (.linear hk (hm.of_mulEquiv e))).elim
    | symplectic k hk hm =>
      rcases symplectic_derived_models hk (hm.of_mulEquiv e) with ⟨hk,hm⟩ | hm
      · exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_rankTwo S hB hn hsec
          (.symplectic hk hm)).elim
      · exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_rankTwo S hB hn hsec
          (.symplectic_derived rfl hm)).elim
    | g2 k hk hm =>
      rcases g2_derived_models hk (hm.of_mulEquiv e) with ⟨hk,hm⟩ | hm
      · exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_rankTwo S hB hn hsec
          (.g2 hk hm)).elim
      · exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_rankTwo S hB hn hsec
          (.g2_derived rfl hm)).elim
    | linear_four hm => exact Or.inl (hm.of_mulEquiv e)
    | linear_five hm => exact Or.inr (hm.of_mulEquiv e)
    | alternating_seven he =>
      have hd := ChapterA.Section03.SourceEmbeddings.AlternatingEight.ambient_card_dvd hsec
      rw [Nat.card_congr (e.trans he.some).toEquiv,nat_card_alternatingGroup] at hd
      norm_num at hd
  · exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_mathieu_twentyTwo hsec he.some).elim
  · have hc := threeCover_center_card hc
    rw [center_eq_bot_of_simple,card_bot] at hc
    omega

/-- The actual normalized A₈ section in degree five eliminates all the other
F.9.18 rows, including the central three-covers, using its original Sylow. -/
theorem five_point_models_of_abelian_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (hJ : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G))) :
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
  let H := F.H
  let B := (F.Li L 1).subgroupOf H
  let N := pCore 2 H
  let q := QuotientGroup.mk' N
  let D := (C.K1.subgroupOf H).map q
  have hT : (T : Subgroup G) ≤ H := F.invariant 1
  have hL : F.Li L 1 ≤ H := (F.Li_le L 1).trans inf_le_right
  have hl : B ∈ Chapter1.L H (T.subtype hT) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT hL).mp
        ⟨hL,Components.Li_mem_local h earlier F 1 (Or.inl ⟨rfl,by decide,by decide⟩)⟩
  have hn : (T.subtype hT : Subgroup H) ≤ normalizer (B : Set H) := by
    intro t ht b
    exact Components.sylow_normalizes_Li h earlier F 1 ht (b : G)
  have hm : ClassicalGroup.IsPSL (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) 4 2 :=
    Components.Li_core_model h F 1 (Or.inl ⟨rfl,by decide,by decide⟩)
  let eB := subgroupOfEquivOfLe hL
  have hb := hm.of_mulEquiv (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB))
  let : Group.IsNilpotent N := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  let S := (T.subtype hT).mapSurjective (QuotientGroup.mk'_surjective N)
  obtain ⟨hl',hn',hb'⟩ := ChapterA.Section03.SourceEmbeddings.AlternatingEight.local_section_map
    hl.1 hn hb q
  have hBD : B.map q ≤ D := map_mono (comap_mono C.contains)
  have hDC : D.IsCComponent := C.component.map_quotient N
  obtain ⟨SD,_,hlD,hnD⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_normalizing
    S hl' hDC.subnormal hBD hn'
  let eB' := subgroupOfEquivOfLe hBD
  have hbD := hb'.of_mulEquiv (QuotientGroup.congr _ _ eB' (pCore_map_iso 2 eB'))
  let e₀ := subgroupOfEquivOfLe C.point_le
  let e : (C.K1 ⧸ pCore 2 C.K1) ≃* D :=
    (QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)).symm.trans
      (cComponentTwoCoreQuotientEquiv C.component)
  let : IsQuasisimple D := (Components.five_endpoint_component_quasisimple h earlier F
    1 (Or.inl rfl) C.K1 ⟨C.point_le,C.component⟩ C.contains).of_mulEquiv e
  have hsH : IsSQTK KnownSimple.IsKnownSimple H :=
    h.source.simpleQTKE.twoLocal_sqtk (Components.Gi_twoLocal h F 1 (by decide))
  have hs := ChapterE.Structure.sqtk_two_quotient hsH N pCore_isPGroup
  have ha := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    hs (pCore_quotient_pCore_eq_bot 2) hDC
  have hf := Chapter13.Section08.Components.SourceModels.f918Models_transport e.symm
    (point_quotient_f918_models h (Or.inr rfl) earlier F hab C hJ)
  rcases ha with ⟨hs,_⟩ | ⟨_,hc⟩
  · let := hs
    exact (five_section_f918_models SD _ hlD hnD hbD hf).elim
      (fun hm => Or.inl (hm.of_mulEquiv e)) (fun hm => Or.inr (hm.of_mulEquiv e))
  · exact (ChapterA.Section03.SourceEmbeddings.AlternatingEight.not_threeCover SD hlD hnD hbD hc).elim

/-- Source 12.9.5(2) for both natural degrees, conditional on the preceding
membership clause (1). The original flag and point component are unchanged. -/
theorem point_models_of_abelian_join {n : ℕ}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (hJ : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G))) :
    IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
  rcases hn with rfl | rfl
  · exact four_point_models_of_abelian_join h earlier F hab C hJ
  · exact Or.inr (five_point_models_of_abelian_join h earlier F hab C hJ)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
