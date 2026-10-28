module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionFF
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearEquality.Borel
public import Theory.SpecificGroups.Suzuki.BorelElementary

/-!
# The center marking for the selected Hermitian family

TI and the nontrivial two-conjugate intersection identify the relative
normalizer of V with M intersect I. Its quotient is the full Borel. On each
nonsymplectic quotient, a nontrivial elementary subgroup invariant under
this Borel is exactly the center of the prescribed Sylow: use the binary
SL2 root action, Suzuki central transitivity, or the odd-dihedral normalizer.

Selection excludes the symplectic branch before using this marking, so it
no longer needs the general E.2.14(2) center clause. Witness existence and
E.2.13(6) remain explicit in `SelectionWitnessSources`. The E.2.14 rank and
torus clauses and the field-four endgame are still required for exclusion.

Source: Aschbacher--Smith E.2.14(1--2), printed pp.226--227, and 8.2.2,
printed pp.714--715 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse
/-- A nontrivial elementary subgroup invariant under the rank-one Borel is
the center of the specified Sylow. All three models are actual quotients. -/
theorem rank_one_elementary_eq_center
    {X : Type*} [Group X] [Finite X] {N : Subgroup X} {k : ℕ}
    (hr : RankOneAlternative X N k) (S : Sylow 2 X)
    (E : Subgroup X) [IsElementaryAbelian 2 E]
    (hES : E ≤ S) (hne : E ≠ ⊥)
    (hN : normalizer (S : Set X) ≤ normalizer (E : Set X)) :
    E = embeddedCenter (S : Subgroup X) := by
  rcases hr with ⟨hk,e,_⟩ | ⟨m,hm,_,e,_⟩ | ⟨_,p,a,_,ho,_,⟨e⟩⟩
  · let f := e.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
    let R := S.mapSurjective (f := f.toMonoidHom) f.surjective
    have hn := map_mono (f := f.toMonoidHom) hN
    change (normalizer ((S : Subgroup X) : Set X)).map f.toMonoidHom ≤
      (normalizer (E : Set X)).map f.toMonoidHom at hn
    rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq] at hn
    have hne' : E.map f.toMonoidHom ≠ ⊥ := by
      intro hh
      exact hne ((map_eq_bot_iff_of_injective (f := f.toMonoidHom) E f.injective).mp hh)
    have he := Matrix.SpecialLinearGroup.eq_sylow_of_borel_normalized R
      (E.map f.toMonoidHom) (map_mono hES) hne' hn
    have hE : E = S := map_injective f.injective he
    rw [←hE,embeddedCenter,center_eq_top,←MonoidHom.range_eq_map,range_subtype]
  · exact suzuki_elementary_eq_center_of_borel_normalized hm e S E hES hne hN
  · have he := odd_dihedral_two_subgroup_normalizer (p^a) ho.pow e E
      (IsElementaryAbelian.isPGroup 2 E) hne
    have hSE : (S : Subgroup X) ≤ E := by
      rw [←he]
      exact (S : Subgroup X).le_normalizer.trans hN
    have hE := le_antisymm hES hSE
    rw [←hE,embeddedCenter,center_eq_top,←MonoidHom.range_eq_map,range_subtype]
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

/-- E.2.14(2)'s center marking on the nonsymplectic family used by selection.
TI supplies relative normalization of the original generator. -/
theorem family_rank_one_center {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (f : Family H T M V I k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hZ : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥) :
    starImage M I V = embeddedCenter (starImage M I T) := by
  obtain ⟨S,hS⟩ := f.sylow
  have hp := Family.twoConjugate h f S hS i hgen
  let := hp.elementary
  let q := QuotientGroup.mk' (localCore M I)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hR : (R : Subgroup (Star M I)) = starImage M I T := by
    change (S : Subgroup I).map q = _
    rw [hS]
    rfl
  have hRM : (R : Subgroup (Star M I)) ≤ starImage M I M :=
    map_mono (hp.sylow_le_normalizer.trans hp.normalizer_le)
  have hMN := family_borel_normalizes h f hr i hgen hTI hNV hZ
  rw [←hR] at hMN
  have hmark := (RankOneAlternative.sylow_marking selectionModelSources hr R hRM hMN).1
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hn := relative_normalizer I M V i.val hgen hTI hNV hZ
  have hMV : M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hVI]
    intro x hx
    exact (hn.le ⟨hx,x.property⟩).2
  have hEV : starImage M I M ≤ normalizer (starImage M I V : Set (Star M I)) :=
    (map_mono (f := q) hMV).trans ((V.subgroupOf I).le_normalizer_map q)
  have hproper := (family_actor_dimension h f hfit S hS i hgen).1
  have hne : starImage M I V ≠ ⊥ := by
    intro he
    have hv : V.subgroupOf I ≤ localCore M I := by
      simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
    exact hp.V_not_le_twoCore hproper
      (hp.le_twoCore_of_le_J _ (IsElementaryAbelian.isPGroup 2 _) hv)
  let : IsElementaryAbelian 2 (starImage M I V) := IsElementaryAbelian.map q
  rw [←hR]
  exact rank_one_elementary_eq_center hr R (starImage M I V)
    (map_mono hp.le_sylow) hne (hmark ▸ hEV)
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open Theory.SpecificGroups.SymplecticFour BenderSuzuki.PFAppendixIII
variable {G : Type*} [Group G] [Finite G]

/-- Only witness existence and the symplectic exclusion remain in selection.
The center marking is proved after the symplectic branch is excluded. -/
structure SelectionWitnessSources (K : GroupClass) : Prop where
  e29 : ∀ H T M V : Subgroup G, HypothesisE28 K H T M V →
    ∃ I k, Family H T M V I k
  e2136 : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    generalizedFitting H = pCore 2 H → Family H T M V I k →
    (∀ i : I, (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ T.subgroupOf I →
      (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ centralizer (V.subgroupOf I : Set I)) →
    ∀ n : ℕ, 0 < n → ¬ Nonempty (Star M I ≃* Sp (BinaryGaloisField n))

open Representation.BinaryOffender
/-- The literal selected pair with the center premise discharged. -/
theorem exists_selected_of_witness_sources {K : GroupClass}
    (earlier : SelectionWitnessSources (G := G) K)
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (hw : 0 < globalW V T)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I), Selected H T M V I k i S := by
  obtain ⟨I,k,f⟩ := earlier.e29 H T M V h
  obtain ⟨x,hx,hgen⟩ := f.generate
  let i : I := ⟨x,hx⟩
  obtain ⟨S,hS⟩ := f.sylow
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hqH := selected_quadraticRatio_gt_one M H V h.normalizer_le hq
  have hZ := family_intersection_ne_bot_of_quadraticRatio_gt_one h hchar f i hgen hqH
  have hsp : ¬ SymplecticAlternative (Star M H) (Star M I)
      (starImage M I M) (starImage M I T) (starImage M I V) k := by
    intro hs
    obtain ⟨e,_⟩ := hs.2.2
    exact earlier.e2136 h hchar f (local_conjugates_centralize I T V hVI hw)
      k hs.1 ⟨e⟩
  have hr := f.classified.resolve_right hsp
  have hc := family_rank_one_core h f hr
  obtain ⟨hk,hdvd,hmodel⟩ := selected_quotient f hc hsp
  have hz := family_rank_one_center h hchar f hr i hgen hTI hNV hZ
  obtain ⟨hzcore,hncore⟩ := core_markings_of_star M I T V hc hz
    (family_borel_normalizes h f hr i hgen hTI hNV hZ)
  have hTM : T ≤ M := by
    obtain ⟨R,hR,hP,hM⟩ := h.minimal
    intro t ht
    have htm := (ChapterB.minimalParabolicMax_spec R hP).2
    rw [hR,←hM] at htm
    exact htm (show (⟨t,h.le_ambient ht⟩ : H) ∈ T.subgroupOf H from ht)
  obtain ⟨hnorm,hrank⟩ := selected_model_markings selectionModelSources M I T V k S hS hTM hmodel hzcore hncore
  refine ⟨I,k,i,S,f,hgen,hS,Family.twoConjugate h f S hS i hgen,hc,
    family_characteristic_two h f hchar,hZ,?_,hNI,?_,hk,hdvd,hmodel,hzcore,hnorm,hrank,
    selected_quadraticRatio_gt_one M I V hNI hq⟩
  · exact intersection_central I V i.val hgen
  · exact relative_normalizer I M V i.val hgen hTI hNV hZ
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
