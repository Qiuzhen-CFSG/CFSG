module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.OriginalSource523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ParameterSetup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo
public import Stellmacher.OmegaOneCenterMap

/-!
# Selecting the original exceptional component of 13.6.27

Apply the full earlier 5.2.3 implication to the actual minimal outside local
subgroup furnished by 13.6.25. Its two-residual is nonsolvable: otherwise
its two-group quotient would make the whole local subgroup solvable. A
nonsolvable subgroup lies in only one C-component, so normalization of
that residual forces normalization of the component selected by 5.2.3.

The singular line lies in the central omega of the original Sylow. Thus
the selected component's centralizer embeds in the original line centralizer.
The complete global alternatives of 5.2.3 remain explicit for the final
classification. The A₇ exclusion, linear diagram action and adequate lift
are applied to this same selected witness in the following modules.

Source: Aschbacher–Smith, 13.6.27, printed pp.934–935, using Theorem 5.2.3,
printed p.649, and the proved 13.6.25.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
variable {G : Type*} [Group G] [Finite G]

theorem residual_not_solvable (H : Subgroup G) (hn : ¬ Group.IsSolvable H) :
    ¬ Group.IsSolvable (pResidual 2 H) := by
  intro hs
  let := hs
  let := (isPGroup_quotient_pResidual (G := H) 2).isNilpotent
  apply hn
  exact Group.isSolvable_of_ker_le_range (pResidual 2 H).subtype
    (QuotientGroup.mk' (pResidual 2 H)) (by simp)

theorem normalizes_component_over_residual
    (T : Sylow 2 G) (H C : Subgroup G) (hTC : (T : Subgroup G) ≤ C)
    (hn : ¬ Group.IsSolvable H)
    (hTR : (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    {K : Subgroup C} (hK : K.IsCComponent)
    (hRK : (pResidual 2 H).map H.subtype ≤ K.map C.subtype) :
    (T : Subgroup G) ≤ normalizer (K.map C.subtype : Set G) := by
  let B := ((pResidual 2 H).map H.subtype).subgroupOf C
  have hBC : (pResidual 2 H).map H.subtype ≤ C := hRK.trans (map_subtype_le K)
  have hBK : B ≤ K := by
    simpa only [B, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective] using
      comap_mono (f := C.subtype) hRK
  have hBns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    have e := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hBC).symm
    exact residual_not_solvable H hn
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hTK : (T : Subgroup G).subgroupOf C ≤ normalizer (K : Set C) := by
    apply cComponent_le_normalizer_of_unique hK hBK
      (fun D hD hBD => Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable
        hBns hD hK hBD hBK)
    exact (comap_mono hTR).trans (le_normalizer_comap C.subtype)
  have hm := (map_mono (f := C.subtype) hTK).trans (le_normalizer_map C.subtype)
  simpa only [map_subgroupOf_eq_of_le hTC] using hm

omit [Finite G] in
/-- The fixed Sylow centralizes its central omega subgroup. -/
theorem sylow_le_omega_centralizer (T : Sylow 2 G) :
    (T : Subgroup G) ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro t ht z hz
  exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm

universe u
variable {X : Type u} [Group X] [Finite X]
  {T : Sylow 2 X} {L V V₁ V₂ V₃ : Subgroup X}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)

include d in
/-- The original singular line lies in the central omega of the same Sylow. -/
theorem singular_le_omega_center :
    V₁ ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup X) := by
  let := d.elementary
  have hV : V₁ ≤ V := d.flag.one_le_two.trans d.flag.two_le_V
  have hTV : (T : Subgroup X) ≤ centralizer (V₁ : Set X) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  intro x hx
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨d.chosen.le_sylow (hV hx), elemPow_eq_one_of_isElementaryAbelian x (hV hx),
      fun t ht => (hTV ht x hx).symm⟩

include d in
/-- The actual smaller centralizer in 5.2.3 embeds in the original G₁. -/
theorem omega_centralizer_le_singular_centralizer :
    centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup X) : Set X) ≤
      centralizer (V₁ : Set X) :=
  centralizer_le (singular_le_omega_center d)

open SuzukiIsolation SourceParameters
open Section06.CentralizerReduction
open Section06.CentralizerReduction.A5Module

/-- The source component, with its actual residual and normalization, before
excluding A₇ or obtaining the linear diagram action. -/
structure SelectedSeed (T : Sylow 2 X) (M : Subgroup X) where
  H : Subgroup X
  star : H ∈ Chapter3.HStar (T : Subgroup X) M
  parameter : 1 < ChapterE.generationParameter H
  nonsolvable : ¬ Group.IsSolvable H
  K : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup X) : Set X))
  component : K.IsCComponent
  contains : (pResidual 2 H).map H.subtype ≤ K.map
    (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup X) : Set X)).subtype
  residual_generates : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup X) = H
  normalizes : (T : Subgroup X) ≤ normalizer (K.map
    (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup X) : Set X)).subtype : Set X)
  residual_outside : ¬ (pResidual 2 H).map H.subtype ≤ M
  models :
    (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      (Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∨
       Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
       Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23))) ∨
    ((pResidual 2 H).map H.subtype = K.map
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup X) : Set X)).subtype ∧
      Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four))

/-- Apply the genuine full 5.2.3 to the constructed HStar member. The local
branch has its source normalization proved; the full global alternatives
remain available to the final classification assembly. -/
theorem selected_seed_or_global
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set X) ≤ normalizer (V : Set X))
    (houtside : ¬ centralizer (V₁ : Set X) ≤ normalizer (L : Set X))
    (hcounter : IsA5Counterexample X)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    Nonempty (SelectedSeed T (normalizer (L : Set X))) ∨ Source523.GlobalAlternative X := by
  let := d.elementary
  obtain ⟨s, hs, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
  obtain ⟨H, hH, _, hn, hgen, hout, hTR⟩ :=
    source_initial_residual_of_context d hA312 hCv houtside hcounter
  rcases h523 X T L (normalizer (L : Set X)) V 2
      (original_source523_setup d s) H hH hn with hl | hg
  · obtain ⟨_, _, K, hK, hRK, hm⟩ := hl
    have hns : ¬ Group.IsSolvable H := by
      intro hsol
      exact hH.1.2 ((source_13_6_25_knownSimple d.hypothesis.qtke s).2.2.1 H hH.1.1 hsol)
    exact Or.inl ⟨{
      H := H
      star := hH
      parameter := hn
      nonsolvable := hns
      K := K
      component := hK
      contains := hRK
      residual_generates := hgen
      normalizes := normalizes_component_over_residual T H _
        (sylow_le_omega_centralizer T) hns hTR hK hRK
      residual_outside := hout
      models := hm }⟩
  · exact Or.inr hg

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
