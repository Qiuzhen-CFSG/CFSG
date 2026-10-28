module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Normality
public import Theory.SpecificGroups.PSL3.HigherFieldBorelGeometry

/-!
# The ordinary higher-field linear exclusion

The actual PSL₃ model supplies component normality, Borel two-perfectness,
Thompson normalization, and the Sylow centralizer comparison. These facts
transport through the component inclusion and the specified Sylow subgroup.
Original Thompson control and the residual-intersection identity then
contradict the noncentral moving module. Only the Borel containment of the
proper-parabolic row is used; no bare-model exclusion is substituted.

Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098.
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
variable {F : Type} [Field F] [Finite F] {n : ℕ}

/-- The literal component Borel normalizes the original Thompson subgroup. -/
theorem PreExclusionSource.linear_borel_normalizes_thompson
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 1<n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(3,F)) :
    d.ordinaryBorel ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  let : (d.L.subgroupOf d.G1).Normal := s.higherField_normal (h := h) hG hL
    (Or.inl ⟨n,hn,Or.inl ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩⟩)
  let K := d.L.subgroupOf d.G1
  let ek : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  obtain ⟨S,hS⟩ := s.centralizer_sylow
  have hS' : (S : Subgroup d.G1) = d.S.subgroupOf d.G1 := by
    apply map_injective d.G1.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le d.S_le_G1]
  have hPK : ((S : Subgroup d.G1).subgroupOf K).map ek.toMonoidHom = d.SL.subgroupOf d.L := by
    ext x
    rw [mem_map_equiv,hS']
    change (x:G) ∈ d.S ↔ (x:G) ∈ d.S ⊓ d.L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hN := Matrix.PSL3.OrdinaryBorel.normalizer_thompson K (ek.trans e) hn hF S
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

/-- Two-perfectness of the literal higher-field linear Borel. -/
theorem PreExclusionSource.linear_borel_twoPerfect
    (s : d.PreExclusionSource h.normalized p)
    (hn : 1<n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(3,F)) :
    IsPPerfect 2 d.ordinaryBorel := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let B := normalizer (P : Set d.L)
  have hBQ : B.map e.toMonoidHom = normalizer (Q : Set PSL(3,F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup d.L) e
  let eB : B ≃* normalizer (Q : Set PSL(3,F)) :=
    (e.subgroupMap B).trans (MulEquiv.subgroupCongr hBQ)
  have hb : IsPPerfect 2 B := (Matrix.PSL3.OrdinaryBorel.normalizer_twoPerfect hn hF Q).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBG : B.map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map _ = _
    rw [hP']
    rfl
  rw [← hBG]
  exact hb.of_surjective (d.L.subtype.subgroupMap B) (d.L.subtype.subgroupMap_surjective B)

/-- The required Sylow centralizer comparison uses the full Borel. -/
theorem PreExclusionSource.linear_borel_centralizers
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 1<n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(3,F)) :
    d.S ⊓ centralizer (d.ordinaryBorel : Set G) ≤ d.S ⊓ centralizer (d.L : Set G) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hnormal := s.higherField_normal (h := h) hG hL
    (Or.inl ⟨n,hn,Or.inl ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩⟩)
  have hSL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp hnormal)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let B := normalizer (P : Set d.L)
  have hBQ : B.map e.toMonoidHom = normalizer (Q : Set PSL(3,F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup d.L) e
  have hBG : B.map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map _ = _
    rw [hP']
    rfl
  rintro x ⟨hxS,hxB⟩
  refine ⟨hxS,?_⟩
  let α := d.L.normalizerMonoidHom ⟨x,hSL hxS⟩
  have hfix : ∀ y ∈ normalizer (Q : Set PSL(3,F)), (MulAut.congr e α) y = y := by
    intro y hy
    rw [← hBQ] at hy
    obtain ⟨l,hl,rfl⟩ := hy
    change e (α (e.symm (e l))) = e l
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change x * (l:G) * x⁻¹ = l
    exact mul_inv_eq_iff_eq_mul.mpr (hxB l (hBG ▸ mem_map_of_mem d.L.subtype hl)).symm
  have hα : α=1 := (MulAut.congr e).injective
    ((Matrix.PSL3.OrdinaryBorel.normalizer_fixer hn hF Q _ hfix).trans (map_one _).symm)
  intro y hy
  have hh := congrArg Subtype.val (DFunLike.congr_fun hα (⟨y,hy⟩:d.L))
  change x*y*x⁻¹=y at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The full simple PSL₃ part of the higher-field row is impossible. -/
theorem PreExclusionSource.false_of_linear_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 1<n) (hm : ClassicalGroup.IsPSL d.L 3 (2^n))
    (hpar : d.OrdinaryParabolic d.ML) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact s.no_thompson_borel (h := h) hG hM hJ
    (PreExclusionSource.linear_borel_twoPerfect (h := h) s hn hF e) (hpar.2.trans d.ML_le_MZ)
    (PreExclusionSource.linear_borel_normalizes_thompson (h := h) s hG hL hn hF e)
    (PreExclusionSource.linear_borel_centralizers (h := h) s hG hL hn hF e)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
