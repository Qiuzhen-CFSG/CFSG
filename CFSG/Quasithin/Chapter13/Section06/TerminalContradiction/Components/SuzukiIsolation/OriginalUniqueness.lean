module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.OriginalSource523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SmallGlobal
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# Component uniqueness from the original ambient exclusions

Each exceptional component candidate forces both five and seven to divide
the ambient group order. The complete small-field rank-two sieve therefore
eliminates the field-two global alternatives of 5.2.3. The remaining larger
fields and M₂₃ are excluded by the actual Hypothesis 13.3.1.

Consequently the existing source application of 5.2.3 proves uniqueness of
the candidate in the original involution centralizer. Its complete earlier
classification remains an explicit input. The final theorem supplies this
uniqueness to the actual 13.6.27 extension argument, retaining the separate
candidate and earlier 13.3.8 source obligations.

Source: Aschbacher–Smith, Hypothesis 13.3.1 and Lemma 13.6.27, printed
pp.884 and 934–935; Theorem 5.2.3, printed p.649.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

omit [IsElementaryAbelian 2 V] in
/-- The original ambient hypotheses exclude every global alternative of
5.2.3 in the presence of the actual exceptional component candidate. -/
theorem not_globalAlternative_of_original_candidate
    {z : G} {K : Subgroup (centralizer ({z} : Set G))}
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K) :
    ¬ Source523.GlobalAlternative G := by
  let : IsSimpleGroup G := d.hypothesis.qtke.simple
  have h := d.hypothesis.hypothesis1311
  exact not_globalAlternative_of_candidate T z hc h.no_M23 h.no_rankTwo

/-- The selected component is unique after applying genuine source 5.2.3;
none of that theorem's global alternatives remains an extra premise. -/
theorem component_unique_of_original_source523
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)))
    {K : Subgroup (centralizer ({s.z.val} : Set G))}
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) K) :
    ∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K := by
  exact (component_unique_or_global_of_original_source523 d s h523 L₁ hH hK hc).resolve_right
    (not_globalAlternative_of_original_candidate d hc)

/-- Apply the proved uniqueness to the literal terminal component conclusion.
Only the genuine earlier classification and source candidate remain explicit. -/
theorem terminal_component_conclusion_of_original_source523
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (h1338 : Earlier1338Two T) (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)))
    {K : Subgroup (centralizer ({s.z.val} : Set G))}
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) K) :
    Conclusion ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) := by
  exact terminal_component_conclusion_of_original_setup d.hypothesis.qtke s h1338 L₁ hH hK hc
    (component_unique_of_original_source523 d s h523 L₁ hH hK hc)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
