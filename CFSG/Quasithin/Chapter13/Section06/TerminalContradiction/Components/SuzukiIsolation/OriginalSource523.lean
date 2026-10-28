module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourcePairOriginal

/-!
# The original A₅ setup satisfies the antecedent of source 5.2.3

The marked A₅ quotient gives the actual PSL₂(4) identification. The earlier
local maximality, faithful membership, maximal two-local overgroup and
reduced-module results supply the remaining hypotheses of 5.2.3. The chosen
Irr⁺ module satisfies V=[V,L]≠1, so its noncentrality is also discharged.

The literal component consumer then needs no setup, catalogue, component-orbit,
solvable-overgroup or generation-parameter callback. The genuine universal
5.2.3 classification remains explicit, and its full global alternatives are
retained. Neither theorem uses the conclusion of 13.6.27 to construct an
earlier-source input.

Source: Aschbacher–Smith, Theorem 5.2.3 and subsection 5.2.1, printed
pp.649–651; the extra-component argument in 13.6.27, printed p.934.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open SourceParameters Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- Every antecedent of source 5.2.3 independent of its selected H is
supplied by the original marked A₅ setup, with the actual field exponent two. -/
theorem original_source523_setup
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G))) :
    Source523.Setup KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) V 2 := by
  have hM : normalizer (L : Set G) ∈ maximalTwoLocalOvergroups
      (L ⊔ (T : Subgroup G)) := s.unique_overgroup.symm ▸ Set.mem_singleton _
  refine ⟨d.hypothesis.qtke,d.maximal_local,
    ((mem_faithfulLocalComponents_iff T L).mp d.hypothesis.local_component).2,
    ?_,L.le_normalizer,normal_subgroupOf_of_le_normalizer le_rfl,
    ⟨hM.1,le_sup_right.trans hM.2⟩,d.chosen.le_sylow.trans le_sup_right,d.reduced,?_⟩
  · refine ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  · intro hcomm
    exact d.chosen.ne_bot (d.chosen.eq_commutator.trans hcomm)

/-- The literal extra-component application of source 5.2.3 has all of its
antecedents discharged. Its unresolved classification and its genuine global
alternatives remain explicit; the original component uniqueness is not assumed. -/
theorem component_unique_or_global_of_original_source523
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)))
    {K : Subgroup (centralizer ({s.z.val} : Set G))}
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) K) :
    (∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K) ∨
      Source523.GlobalAlternative G := by
  have hTC : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G) :=
    le_sup_right.trans hH.1.2
  have hthree := (ThreeStructure.local_three_exclusions
    (d.hypothesis.qtke.involution_centralizer_sqtk s.marked_order)
    (T.subtype hTC) hK hc).2
  have h25 := source_13_6_25_knownSimple d.hypothesis.qtke s
  exact component_unique_or_global_alternative
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    h523 T L L₁ (normalizer (L : Set G)) V 2 (original_source523_setup d s)
    s.z.val s.marked_order (s.module_le s.z.property) hH hK hc hthree
    h25.2.1 h25.2.2.1
    (fun J hJ D hD => component_image_not_le_of_original_setup d.hypothesis.qtke s L₁ _ hJ D hD)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
