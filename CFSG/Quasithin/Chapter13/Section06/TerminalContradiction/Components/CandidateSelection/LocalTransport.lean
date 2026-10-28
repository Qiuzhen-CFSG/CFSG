module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.SourceSelection
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LinearDiagram
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.AlternatingSeven
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateStructure

/-!
# The selected component inside the original line centralizer

The centralizer of Ω₁(Z(T)) has nontrivial two-core and contains T.
Lemma 1.2.6 therefore puts each of its C-components in the original local
family. Faithful inclusion into C_G(V₁) preserves that family and the
exceptional candidate, including the literal parabolic-exchange equations
in the linear case. The final witness retains its original ambient image.

This is the input to the subsequent A.3.12 component lift; it does not
assert that the image is already a C-component of the larger centralizer.
Source: Aschbacher–Smith, 1.2.6 and the component lift in 13.6.27,
printed pp.505 and 934.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
variable {H X : Type*} [Group H] [Group X] {S K : Subgroup H}

/-- Every candidate alternative transports through the same injective map;
the linear branch retains the actual diagram action. -/
theorem candidate_map (f : H →* X) (hf : Function.Injective f)
    (hc : Candidate S K) : Candidate (S.map f) (K.map f) := by
  let e := K.equivMapOfInjective f hf
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rcases hc with hJ | hM | ⟨eL, hd⟩
  · exact Or.inl (hJ.map (fun eJ => q.symm.trans eJ))
  · exact Or.inr (Or.inl (hM.map (fun eM => q.symm.trans eM)))
  · exact Or.inr (Or.inr (nontrivialDynkinAction_map f hf K S eL hd))

variable {G : Type*} [Group G]

/-- A C-component of an original local overgroup becomes a local component
in any larger overgroup of the same Sylow subgroup. -/
theorem local_component_map_of_HOver (T : Sylow 2 G) {C D : Subgroup G}
    (hC : C ∈ Chapter1.HOver G (T : Set G)) (hCD : C ≤ D)
    (K : Subgroup C) (hK : K.IsCComponent) :
    K.map (inclusion hCD) ∈ Chapter1.L D ((T : Subgroup G).subgroupOf D) := by
  have hB : K.map C.subtype ∈ Chapter1.cComponentsIn C := by
    refine ⟨map_subtype_le K, ?_⟩
    simpa only [subgroupOf, comap_map_eq_self_of_injective C.subtype_injective] using hK
  have hL := ((Chapter1.lemma_1_2_6 T hC).1 hB).2
  apply (Chapter1.mem_L_map_iff D.subtype D.subtype_injective).mp
  rw [map_subgroupOf_eq_of_le (hC.2.trans hCD), map_map]
  exact hL

variable [Finite G] {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The actual selected central-omega component and candidate are transported
to the original line centralizer, with the same ambient subgroup image. -/
theorem exists_local_candidate_in_singular_centralizer
    (KZ : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)))
    (hKZ : KZ.IsCComponent)
    (hc : Candidate ((T : Subgroup G).subgroupOf
      (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))) KZ) :
    ∃ K : Subgroup (centralizer (V₁ : Set G)),
      K ∈ Chapter1.L (centralizer (V₁ : Set G))
        ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) ∧
      Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K ∧
      K.map (centralizer (V₁ : Set G)).subtype = KZ.map
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype := by
  let C := centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let D := centralizer (V₁ : Set G)
  have hTC : (T : Subgroup G) ≤ C := sylow_le_omega_centralizer T
  have hCD : C ≤ D := omega_centralizer_le_singular_centralizer d
  have hC : C ∈ Chapter1.HOver G (T : Set G) := by
    simpa only [sup_eq_left.mpr hTC] using
      centralizer_join_mem_HOver d.hypothesis.qtke T C le_rfl
  have hS : ((T : Subgroup G).subgroupOf C).map (inclusion hCD) =
      (T : Subgroup G).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (hTC.trans hCD)]
    exact map_subgroupOf_eq_of_le hTC
  have hm := candidate_map (inclusion hCD) (inclusion_injective hCD) hc
  rw [hS] at hm
  exact ⟨KZ.map (inclusion hCD), local_component_map_of_HOver T hC hCD KZ hKZ,
    hm, by rw [map_map]; rfl⟩

/-- The same source witness is normalized by the original restricted Sylow.
This is the precise local input to the subsequent adequate component lift. -/
theorem exists_normalized_local_candidate_in_singular_centralizer
    (KZ : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)))
    (hKZ : KZ.IsCComponent)
    (hc : Candidate ((T : Subgroup G).subgroupOf
      (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))) KZ) :
    ∃ K : Subgroup (centralizer (V₁ : Set G)),
      K ∈ Chapter1.L (centralizer (V₁ : Set G))
        ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) ∧
      (T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)) ≤
        normalizer (K : Set (centralizer (V₁ : Set G))) ∧
      Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K ∧
      K.map (centralizer (V₁ : Set G)).subtype = KZ.map
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype := by
  let C := centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let D := centralizer (V₁ : Set G)
  have hTC : (T : Subgroup G) ≤ C := sylow_le_omega_centralizer T
  have hC : C ∈ Chapter1.HOver G (T : Set G) := by
    simpa only [sup_eq_left.mpr hTC] using
      centralizer_join_mem_HOver d.hypothesis.qtke T C le_rfl
  let := hc.normal hKZ (Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hC.1)
  have hCN : C ≤ normalizer (KZ.map C.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      KZ.le_normalizer_map C.subtype
  obtain ⟨K, hL, hm, he⟩ := exists_local_candidate_in_singular_centralizer d KZ hKZ hc
  have hTN : (T : Subgroup G) ≤ normalizer (K.map D.subtype : Set G) := by
    rw [he]
    exact hTC.trans hCN
  have hn := (comap_mono (f := D.subtype) hTN).trans (le_normalizer_comap D.subtype)
  refine ⟨K, hL, ?_, hm, he⟩
  simpa only [subgroupOf, D, comap_map_eq_self_of_injective D.subtype_injective] using hn

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
