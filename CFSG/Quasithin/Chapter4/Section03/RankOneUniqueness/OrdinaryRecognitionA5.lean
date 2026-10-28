module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionContaining
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionPlacement
public import CFSG.Quasithin.ChapterC.Section03.A5.FullSylowExclusion

/-!
# Original ordinary exclusion when L is the deleted-five block

The outside choice already supplies a full Sylow of H and the local
C-component condition on the original L. Restrict these literal subgroups
to the containing ordinary component, then apply the exhaustive deleted-five
carrier exclusion. No identification of H with N_G(K), later ambient model
exclusion, or R₀ action is required in this specialized branch.

The second theorem applies the same exclusion to the original shared source
configuration. The general rank-one symplectic marking is still a separate
obligation: the deleted-five module is an additional hypothesis here.
Source: Aschbacher--Smith C.3.1 and 4.3.6, printed pp.149--151,614--615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual outside component cannot be ordinary when the original L
is an alternating-five block. Full component-normalizer equality is unnecessary. -/
theorem OutsideChoice.no_ordinary_component_of_alternatingFive
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (hb : IsAlternatingBlock L 5)
    (K : Subgroup c.H) (hK : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) : False := by
  let B := L.subgroupOf c.H
  obtain ⟨S,hS⟩ := (c.sylow_data D h hpsl).2.2
  have hS' : (S : Subgroup c.H) = ((T : Subgroup G) ⊓ c.H).subgroupOf c.H := by
    apply map_injective c.H.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right]
    exact hS
  have hl : B ∈ ChapterA.Section03.localCComponents S := by
    rw [hS']
    exact (c.local_component D h hpsl).1
  have hn : (S : Subgroup c.H) ≤ normalizer (B : Set c.H) := by
    rw [←subgroupOf_normalizer_eq c.contains,hS']
    intro s hs
    exact D.sylow_normalizes_component hs.1
  have hb' : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe c.contains).symm hb
  have hBK : B ≤ K := by
    intro b hb
    obtain ⟨k,hk,he⟩ := hLK hb
    exact (Subtype.ext he : k = b) ▸ hk
  have hout' : ¬ K ≤ normalizer (B : Set c.H) := by
    rw [←subgroupOf_normalizer_eq c.contains]
    intro hk
    apply hout
    rintro _ ⟨k,hkK,rfl⟩
    exact hk hkK
  exact no_ordinary_component_containing_alternatingFive (c.c28 D h).sqtk
    S B hb' hl hn K hK hBK hout'

/-- The same source exclusion at the original ordinary marking consumer. -/
theorem SourceConfiguration.ordinary_false_of_alternatingFive
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (hb : IsAlternatingBlock L 5) (ho : IsComponent c.H c.K) : False := by
  let := ho.2
  obtain ⟨P,hP⟩ := c.ordinary_component_sylow
  have hl := c.ordinaryLocal_mem_localCComponents D
  rw [←hP] at hl
  have hn : (P : Subgroup c.K) ≤ normalizer (c.ordinaryLocal : Set c.K) := by
    rw [hP]
    intro s hs l
    exact D.sylow_normalizes_component hs.1 (((l : c.K) : c.H) : G)
  have hb' : IsAlternatingBlock c.ordinaryLocal 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv c.ordinaryLocalEquiv.symm hb
  have hne : c.ordinaryLocal ≠ ⊤ := by
    intro he
    apply c.component_outside
    rintro _ ⟨k,hk,rfl⟩
    apply L.le_normalizer
    exact he.ge (show (⟨k,hk⟩ : c.K) ∈ (⊤ : Subgroup c.K) from trivial)
  exact no_quasisimple_alternatingFive_full_sylow (c.c28.sqtk.subgroup c.K)
    P c.ordinaryLocal hb' hl hn hne

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
