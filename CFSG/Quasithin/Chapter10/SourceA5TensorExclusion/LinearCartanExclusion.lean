module
public import Theory.SpecificGroups.PSL3.LinearThreeCubicCartan
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TorusPropagation
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The chosen cubic Cartan in the linear tensor exclusion

In the SL₃(4) branch, a cubic centralizing the original A₅ local quotient
has central image in the degree-three model. The point/line placement is
obtained from the local A₅ marking, so there is no coordinate choice or
model-centralization premise. Its central image centralizes the old
component modulo its two-core, and the original Cartan orbit gives the
source contradiction.

The model map may be defined only on the containing source subgroup.
All subgroup restrictions retain that map, the original Cartan, and the
original old component. Construction of the Cartan and its normalizer
orbit remains an earlier source input.

Source: Aschbacher–Smith 9.3.8, printed p.734.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter4 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {G X : Type*} [Group G] [Group X]

private theorem core_image_le (f : G →* X) (L : Subgroup G) :
    (L.pCoreIn 2).map f ≤ (L.map f).pCoreIn 2 := by
  have hn : ((pCore 2 L).map (f.subgroupMap L)).Normal :=
    Normal.map inferInstance _ (f.subgroupMap_surjective L)
  have hp : IsPGroup 2 ((pCore 2 L).map (f.subgroupMap L)) :=
    pCore_isPGroup.map _
  have hle : (pCore 2 L).map (f.subgroupMap L) ≤ pCore 2 (L.map f) :=
    le_sSup ⟨hn,hp⟩
  have hh := map_mono (f := (L.map f).subtype) hle
  have he : (L.map f).subtype.comp (f.subgroupMap L) = f.comp L.subtype := by
    ext x
    rfl
  rw [map_map,he] at hh
  simpa only [pCoreIn,map_map] using hh

private theorem cubic_section_transfer
    [Finite G] [Finite X]
    (f : G →* X) (L K E : Subgroup G)
    (hEC : E ≤ sectionCentralizer L)
    (hEK : E ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 (f.subgroupMap K).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (hcentral : ∀ x : X, x ^ 3 = 1 →
      ⁅zpowers x,L.map f⁆ ≤ (L.map f).pCoreIn 2 → x ∈ center X) :
    E ≤ sectionCentralizer K := by
  apply (le_sectionCentralizer_iff E K).mpr
  refine ⟨hEK,commutator_le.mpr ?_⟩
  intro x hx k hkK
  have hxcomm : ⁅zpowers (f x),L.map f⁆ ≤ (L.map f).pCoreIn 2 := by
    rw [←MonoidHom.map_zpowers,←map_commutator]
    apply (map_mono (commutator_mono (zpowers_le.mpr hx) le_rfl)).trans
    exact (map_mono ((le_sectionCentralizer_iff E L).mp hEC).2).trans (core_image_le f L)
  have hxZ := hcentral (f x) (by rw [←map_pow,h3 x hx,map_one]) hxcomm
  apply mem_pCoreIn_of_map_mem f K hk
  · exact le_normalizer_iff_commutator_le_right.mp hEK (commutator_mem_commutator hx hkK)
  · rw [map_commutatorElement]
    have he : ⁅f x,f k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp hxZ (f k)).symm
    rw [he]
    exact one_mem _


variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem cubic_conjugate_section_central
    (hF : Nat.card F = 4) (B : Subgroup SL(3,F)) (g : SL(3,F))
    (hg : B.map (MulAut.conj g).toMonoidHom = pointLocalSL F ∨
      B.map (MulAut.conj g).toMonoidHom = lineLocalSL F)
    (x : SL(3,F)) (hx : x ^ 3 = 1) (hc : ⁅zpowers x,B⁆ ≤ B.pCoreIn 2) :
    x ∈ center SL(3,F) := by
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hc
  rw [map_commutator,MonoidHom.map_zpowers,
    map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective] at hm
  have hp : (MulAut.conj g x)^3 = 1 := by rw [←map_pow,hx,map_one]
  have hz : MulAut.conj g x ∈ center SL(3,F) := by
    rcases hg with hg | hg
    · rw [hg] at hm
      exact cubic_point_section_central hF _ hm hp
    · rw [hg] at hm
      exact cubic_line_section_central hF _ hm hp
  rw [mem_center_iff] at hz ⊢
  intro y
  apply (MulAut.conj g).injective
  simpa only [map_mul] using hz (MulAut.conj g y)

/-- A cubic section centralizer of the actual local A₅ image centralizes
any other normalized component modulo its two-core. -/
theorem source_tensor_linear_chosen_factor
    [Finite G] (hF : Nat.card F = 4)
    (f : G →* SL(3,F)) (L K E : Subgroup G)
    (S : Sylow 2 SL(3,F))
    (hL : L.map f ∈ localCComponents S) (hproper : L.map f ≠ ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hkL : IsPGroup 2 (f.subgroupMap L).ker)
    (hEC : E ≤ sectionCentralizer L)
    (hEK : E ≤ normalizer (K : Set G))
    (hkK : IsPGroup 2 (f.subgroupMap K).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer K := by
  let eImage := ((f.subgroupMap L).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective L) hkL).symm.trans eL
  obtain ⟨_,g,hg⟩ := special_linear_three_five_section_placement_all
    (n := 2) (by simpa using hF) S (L.map f) hL hproper eImage
  apply cubic_section_transfer f L K E hEC hEK hkK h3
  intro x hx hc
  exact cubic_conjugate_section_central hF (L.map f) g hg x hx hc

/-- Keep the actual overgroup as domain of the model map, and return the
section-centralizer conclusion in the original ambient group. -/
theorem source_tensor_linear_original_chosen_factor
    [Finite G] (hF : Nat.card F = 4)
    (I L K E : Subgroup G) (hLI : L ≤ I) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* SL(3,F)) (S : Sylow 2 SL(3,F))
    (hL : (L.subgroupOf I).map f ∈ localCComponents S)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hkL : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hEC : E ≤ sectionCentralizer L)
    (hEK : E ≤ normalizer (K : Set G))
    (hkK : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer K := by
  let eL' := subgroupOfEquivOfLe hLI
  let eQ : (L.subgroupOf I ⧸ pCore 2 (L.subgroupOf I)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eL' (pCore_map_iso 2 eL')).trans eL
  have hEC' : E.subgroupOf I ≤ sectionCentralizer (L.subgroupOf I) := by
    apply (le_sectionCentralizer_iff _ _).mpr
    have hc := (le_sectionCentralizer_iff E L).mp hEC
    constructor
    · rw [←subgroupOf_normalizer_eq hLI]
      exact comap_mono hc.1
    · apply (Subgroup.map_le_map_iff_of_injective I.subtype_injective).mp
      rw [map_commutator,map_subgroupOf_eq_of_le hEI,map_subgroupOf_eq_of_le hLI,
        map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
        map_subgroupOf_eq_of_le hLI]
      exact hc.2
  have hEK' : E.subgroupOf I ≤ normalizer (K.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hKI]
    exact comap_mono hEK
  have hc := source_tensor_linear_chosen_factor hF f (L.subgroupOf I)
    (K.subgroupOf I) (E.subgroupOf I) S hL hproper eQ hkL hEC' hEK' hkK
    (fun x hx => Subtype.ext (h3 x hx))
  have hm := map_mono (f := I.subtype) ((le_sectionCentralizer_iff _ _).mp hc).2
  apply (le_sectionCentralizer_iff E K).mpr
  refine ⟨hEK,?_⟩
  rwa [map_commutator,map_subgroupOf_eq_of_le hEI,map_subgroupOf_eq_of_le hKI,
    map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
    map_subgroupOf_eq_of_le hKI] at hm

/-- The linear model supplies the centralizing Cartan factor in source9.3.8;
the original normalizer orbit and cubic in the old component finish the exclusion. -/
theorem source_tensor_linear_original_cartan_contradiction
    [Finite G] (hF : Nat.card F = 4)
    (I L K D E N : Subgroup G) (hLI : L ≤ I) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* SL(3,F)) (S : Sylow 2 SL(3,F))
    (hL : (L.subgroupOf I).map f ∈ localCComponents S)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hkL : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hEC : E ≤ sectionCentralizer L)
    (hEK : E ≤ normalizer (K : Set G))
    (hkK : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hNK : N ≤ normalizer (K : Set G)) (hgen : componentOrbit E N = D)
    (b : G) (hbD : b ∈ D) (hbK : b ∈ K) (hb3 : orderOf b = 3) : False :=
  source_tensor_torus_cubic_contradiction K D E N eK hNK
    (source_tensor_linear_original_chosen_factor hF I L K E hLI hKI hEI f S
      hL hproper eL hkL hEC hEK hkK h3) hgen b hbD hbK hb3

end CFSG.Quasithin.Chapter10
