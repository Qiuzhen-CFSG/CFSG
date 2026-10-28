module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Normality
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.MarkedSylow
public import Theory.SpecificGroups.PSL3.CentralCoverBorelGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The ordinary PSL₃(4) central-cover exclusion

The original faithful central involution is a nontrivial pointwise fixer of
S_L. The actual PSL₃(4) cover geometry therefore forces the covering center
to be elementary. Involution lifting gives the full elementary preimages
needed by the Thompson product, so the literal Borel normalizes J(S).
Two-perfectness and the Sylow centralizer comparison then apply original
Thompson control to contradict movement of V₂ on the same component.

No splitting, exchanged-source witness or later catalogue selection is used.
Source: Aschbacher--Smith 15.1.21(i), pp.1097--1098, and I.2.2(3).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original central involution forces the retained linear cover's center elementary. -/
theorem PreExclusionSource.linear_four_center_frattini
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ center d.L) ≃* Matrix.PSL3Four.PSL) : frattini (center d.L) = ⊥ := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  obtain ⟨P,_,α,hα,hαne,hfix⟩ := s.exists_nontrivial_sylow_fixer (h := h) hG hM hu hL
  exact Matrix.PSL3.OrdinaryBorel.four_cover_center_frattini e
    (s.ordinary hL).center_two P α hα hαne hfix


private noncomputable def centerQuotientCongr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) : (X ⧸ center X) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem four_cover_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ center d.L) ≃* Matrix.PSL3Four.PSL) :
    (d.L.subgroupOf d.G1).Normal := by
  apply s.higherField_normal (h := h) hG hL
  exact Or.inr ⟨Matrix.PSL3Four.F,inferInstance,inferInstance,Matrix.PSL3Four.card_F,
    ⟨(QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).symm.trans e⟩⟩

/-- Thompson normalization on the original nonsplit cover, with its center premise discharged. -/
theorem PreExclusionSource.linear_four_cover_borel_normalizes_thompson
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ center d.L) ≃* Matrix.PSL3Four.PSL) :
    d.ordinaryBorel ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  let : (d.L.subgroupOf d.G1).Normal := four_cover_normal (h := h) s hG hL e
  let K := d.L.subgroupOf d.G1
  let ek : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let eQ := (centerQuotientCongr ek).trans e
  let : IsQuasisimple K := hL.2
  have hZK : IsPGroup 2 (center K) := (s.ordinary hL).center_two.of_equiv (centerCongr ek).symm
  let : Fact (IsPGroup 2 (center d.L)) := ⟨(s.ordinary hL).center_two⟩
  let : IsElementaryAbelian 2 (center d.L) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp
      (s.linear_four_center_frattini (h := h) hG hM hu hL e)
  let : IsElementaryAbelian 2 (center K) := IsElementaryAbelian.of_surjective
    (centerCongr ek).symm.toMonoidHom (centerCongr ek).symm.surjective
  have hlift (W : Subgroup Matrix.PSL3Four.PSL) (hw : IsElementaryAbelian 2 W) :
      IsElementaryAbelian 2 (W.comap (Matrix.PSL3Even.ThompsonCentralCover.projection K eQ)) := by
    let := hw
    apply Matrix.PSL3Four.ElementaryParabolic.elementary_comap _
      (Matrix.PSL3Even.ThompsonCentralCover.projection_surjective K eQ)
    · rw [Matrix.PSL3Even.ThompsonCentralCover.projection_ker]
    · intro z hz
      rw [Matrix.PSL3Even.ThompsonCentralCover.projection_ker] at hz
      exact elemPow_eq_one_of_isElementaryAbelian z hz
  obtain ⟨S,hS⟩ := s.centralizer_sylow
  have hS' : (S : Subgroup d.G1) = d.S.subgroupOf d.G1 := by
    apply map_injective d.G1.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le d.S_le_G1]
  have hPK : ((S : Subgroup d.G1).subgroupOf K).map ek.toMonoidHom = d.SL.subgroupOf d.L := by
    ext x
    rw [mem_map_equiv,hS']
    change (x:G) ∈ d.S ↔ (x:G) ∈ d.S ⊓ d.L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hN := Matrix.PSL3.OrdinaryBorel.cover_normalizer_thompson K eQ hZK hlift
    (n:=2) (by decide) (by simpa using Matrix.PSL3Four.card_F) S
  have hBN : ((normalizer ((S : Subgroup d.G1).subgroupOf K : Set K)).map K.subtype).map
      d.G1.subtype = d.ordinaryBorel := by
    have hcomp : d.G1.subtype.comp K.subtype = d.L.subtype.comp ek.toMonoidHom := rfl
    rw [map_map,hcomp,← map_map,map_equiv_normalizer_eq,hPK]
    rfl
  have hJ : (elementaryAbelianMaxJ (S : Subgroup d.G1)).map d.G1.subtype =
      elementaryAbelianMaxJ d.S := by
    rw [← elementaryAbelianMaxJ_map_injective d.G1.subtype d.G1.subtype_injective,hS]
  have hh := (map_mono (f:=d.G1.subtype) hN).trans
    (le_normalizer_map (H := elementaryAbelianMaxJ (S : Subgroup d.G1)) d.G1.subtype)
  rwa [hBN,hJ] at hh

/-- The literal Borel remains two-perfect without splitting the central two-cover. -/
theorem PreExclusionSource.linear_four_cover_borel_twoPerfect
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ center d.L) ≃* Matrix.PSL3Four.PSL) : IsPPerfect 2 d.ordinaryBorel := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hb := Matrix.PSL3.OrdinaryBorel.cover_normalizer_twoPerfect (n:=2) (by decide)
    (by simpa using Matrix.PSL3Four.card_F) e (s.ordinary hL).center_two P
  have hh := hb.of_surjective (d.L.subtype.subgroupMap (normalizer (P : Set d.L)))
    (d.L.subtype.subgroupMap_surjective _)
  change IsPPerfect 2 ((normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype) at hh
  rw [hP'] at hh
  exact hh

/-- The Sylow centralizer comparison is on the original covering component. -/
theorem PreExclusionSource.linear_four_cover_borel_centralizers
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ center d.L) ≃* Matrix.PSL3Four.PSL) :
    d.S ⊓ centralizer (d.ordinaryBorel : Set G) ≤ d.S ⊓ centralizer (d.L : Set G) := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  have hSL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp (four_cover_normal (h := h) s hG hL e))
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hBG : (normalizer (P : Set d.L)).map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map _ = _
    rw [hP']
    rfl
  rintro x ⟨hxS,hxB⟩
  refine ⟨hxS,?_⟩
  let α := d.L.normalizerMonoidHom ⟨x,hSL hxS⟩
  have hα : α=1 := Matrix.PSL3.OrdinaryBorel.cover_normalizer_fixer (n:=2) (by decide)
    (by simpa using Matrix.PSL3Four.card_F) e P α (by
      intro y hy
      apply Subtype.ext
      change x*(y:G)*x⁻¹=y
      exact mul_inv_eq_iff_eq_mul.mpr (hxB y (hBG ▸ mem_map_of_mem d.L.subtype hy)).symm)
  intro y hy
  have hh := congrArg Subtype.val (DFunLike.congr_fun hα (⟨y,hy⟩:d.L))
  change x*y*x⁻¹=y at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The PSL₃(4) central-cover constructor is excluded with all model geometry discharged. -/
theorem PreExclusionSource.false_of_linear_four_cover
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4)
    (hpar : d.OrdinaryParabolic d.ML) : False := by
  obtain ⟨F,_,_,hF,⟨ef⟩⟩ := hm
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let e : (d.L ⧸ center d.L) ≃* Matrix.PSL3Four.PSL :=
    ((QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans ef).trans
      (Atlas.fieldEquivPSL 3 eF)
  exact s.no_thompson_borel (h := h) hG hM hJ
    (s.linear_four_cover_borel_twoPerfect (h := h) hL e) (hpar.2.trans d.ML_le_MZ)
    (s.linear_four_cover_borel_normalizes_thompson (h := h) hG hM hu hL e)
    (s.linear_four_cover_borel_centralizers (h := h) hG hL e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
