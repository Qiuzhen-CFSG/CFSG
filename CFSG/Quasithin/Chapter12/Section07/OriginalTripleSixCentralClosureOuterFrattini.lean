module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAutomizerCases
public import Theory.Frattini.PGroup

/-!
# The actual Frattini subgroup in the outer closure branch

An abelian closure fixes its original scalar point pointwise, and hence
induces the even Klein-four row. In either genuine outer branch the closure
is nonabelian. Its already constructed Frattini subgroup is contained in
the original order-two point and cannot be trivial, so it is that point.

Source: Aschbacher--Smith12.7.15 and the paragraph preceding12.7.17,
printed pp.843 and845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The whole original closure has precisely the original central point
as Frattini subgroup in the genuine outer automizer branch. -/
theorem original_tripleSix_central_closure_outer_frattini
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ¬ IsMulCommutative W ∧ (frattini W).map W.subtype = zpowers (z : G) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  let v := (tripleSixPointCoordinates D a z).toAdd
  obtain ⟨hWT,f,hf,_,hK,_,hfix,_,_,e,_,_,heven,_,hab⟩ :=
    original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot
  have hnon : ¬ IsMulCommutative W := by
    intro hw
    have hklein := hab hw
    apply houter
    intro b hb
    have hfb : f b ∈ (inducedAutomizer U W).map f := mem_map_of_mem _ hb
    let bS : Hexacode.fullVectorStabilizer v := ⟨f b,hfix hfb⟩
    have hmark : e bS ∈ (⊥ : Subgroup Two).prod core := by
      rw [←hklein]
      exact mem_map_of_mem _ hfb
    have he : hexSign (f b) = 1 := by
      apply (heven bS).mpr
      have hsign := ((core_mem_iff (e bS).2).mp hmark.2).1
      rw [mem_bot.mp hmark.1]
      change 1 = if (e bS).2.sign = 1 then 1 else Equiv.swap 0 1
      rw [if_pos hsign]
    obtain ⟨c,hc,hcb⟩ := show f b ∈ (inducedAutomizer U K).map f from hK.symm ▸ he
    exact hf hcb ▸ hc
  refine ⟨hnon,?_⟩
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hle : (frattini W).map W.subtype ≤ zpowers (z : G) := hc.2.2.2.1
  let : Fact (IsPGroup 2 W) := ⟨T.isPGroup'.to_le hWT⟩
  have hne : (frattini W).map W.subtype ≠ ⊥ := by
    intro hh
    have hb : frattini W = ⊥ := (map_eq_bot_iff_of_injective _ W.subtype_injective).mp hh
    let := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hb
    exact hnon inferInstance
  let := D.elementary
  have ho : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property)
    (fun hh => hz (Subtype.ext hh))
  have hzcard : Nat.card (zpowers (z : G)) = 2 := by
    rw [Nat.card_zpowers,ho]
  have hd := card_dvd_of_le hle
  rw [hzcard] at hd
  have hcard : Nat.card ((frattini W).map W.subtype) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun hh => hne ((eq_bot_iff_card _).mpr hh))
  exact eq_of_le_of_card_ge hle (by rw [hcard,hzcard])

end CFSG.Quasithin.Chapter12.Section07
