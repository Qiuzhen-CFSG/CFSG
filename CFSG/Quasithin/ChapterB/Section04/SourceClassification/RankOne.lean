module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SourceAssembly
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The even PSL2 source branch of B.4.2

K.3.1 recognizes the actual natural or Hermitian module. Every larger Hermitian
case is excluded by its proved FF obstruction; at the smallest parameter only
the full symmetric-five action survives. Natural best offenders are transported
from the actual ambient Sylow intersections to Sylow subgroups of the layer.
Both remaining outputs are literal corrected B.4.2 action rows with their
original module intertwiners, marked component and offender clauses.

Source: Aschbacher--Smith B.4.2(1),(5), K.3.1, pp.86 and 453--454.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] in
private theorem sylow_offenders_of_sylowInf
    (hgen : offenderSubgroup ρ = L)
    (hcalc : ∀ T : Sylow 2 G, ∀ A : Subgroup G, A ≤ T →
      (IsOffender ρ A ↔ A = (T : Subgroup G) ⊓ L)) :
    ∀ A : Subgroup G, IsBestOffender ρ A → ∃ S : Sylow 2 L,
      A = (S : Subgroup L).map L.subtype := by
  intro A hA
  have hAL : A ≤ L := hgen ▸ hA.le_offenderSubgroup ρ
  let := hA.1.2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 (A.subgroupOf L)).exists_le_sylow
  obtain ⟨T,hT⟩ := S.exists_comap_subtype_eq
  have hAT : A ≤ T := by
    intro a ha
    have hs : (⟨a,hAL ha⟩ : L) ∈ S := hAS ha
    change (⟨a,hAL ha⟩ : L) ∈ (S : Subgroup L) at hs
    rw [← hT] at hs
    exact hs
  refine ⟨S, ?_⟩
  rw [(hcalc T A hAT).mp (hA.isOffender ρ), ← hT]
  exact (subgroupOf_map_subtype (T : Subgroup G) L).symm

private noncomputable def markedFive (a : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hm : L.map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 5)) :
    MarkedActionEquiv ρ ⊤ L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5)) where
  action := {
    groupEquiv := Subgroup.topEquiv.trans a.groupEquiv
    linearEquiv := a.linearEquiv
    intertwines := fun g v => a.intertwines g v }
  contained := le_top
  subgroupEquiv := (L.equivMapOfInjective a.groupEquiv.toMonoidHom a.groupEquiv.injective).trans
    (MulEquiv.subgroupCongr hm)
  compatible _ := rfl

theorem psl2_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {r : ℕ} (hr : 2 ≤ r)
    (he : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2 ^ r)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  classical
  have hq := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
  obtain ⟨K,hK,hfin,hchar,hcard,e,hd,halt⟩ := h.psl2_case hr he
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  rcases halt with ⟨_,_,M,hquad,_,hgen,hcalc,_,_⟩ | ⟨s,hrs,_,hs,_,_,_,hodd,hlarge,hsmall⟩
  · let F : BinaryField := {
      Carrier := K
      degree := r
      degree_pos := by omega
      card_eq := hcard }
    let a : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2) := {
      groupEquiv := M.groupEquiv
      linearEquiv := M.coordinates
      intertwines := M.intertwines }
    exact .linearTwo F hgen a (sylow_offenders_of_sylowInf hgen (fun T => (hcalc T).2.2.2.2.1)) hquad
  · by_cases hs1 : 1 < s
    · exact ((hlarge hs1).2 hff).elim
    have hsEq : s = 1 := by omega
    rcases hsmall hsEq with ⟨_,_,hquad,_⟩ | ⟨a,hm,hquad,hgen,hactors,_⟩
    · rw [hquad] at hq
      norm_num at hq
    · rw [hgen]
      refine .symmetric 5 (Or.inl rfl) (markedFive a hm) ?_ hquad
      intro A hA
      have hh := (hactors A).mp hA
      change Offenders.CaseAFamily 5 ((A.subgroupOf ⊤).map
        (a.groupEquiv.toMonoidHom.comp (⊤ : Subgroup G).subtype))
      rw [← Subgroup.map_map, map_subgroupOf_eq_of_le (show A ≤ ⊤ from le_top)]
      exact hh

/-- Apply this source family to the original B.4.2 hypotheses and best offender. -/
theorem psl2_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {r : ℕ} (hr : 2 ≤ r) (he : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2 ^ r)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  psl2_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩ hr he
end CFSG.Quasithin.ChapterB.SourceClassification
