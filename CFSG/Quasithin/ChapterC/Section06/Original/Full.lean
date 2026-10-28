module
public import CFSG.Quasithin.ChapterC.Section06.Original.Guarded

/-!
# All six clauses of original C.6.1

The source statement retains the actual residual and core, the normalizer
index and Thompson span, both type-guarded elementary families and the
rank bounds. Its endgame includes the conditional S₄×C₂ identification,
the S₄ dihedral/semidihedral exception, and the D₈ normalizer quotient.
Every input is one of C.6.1(i)--(iv); the quotient models construct all
C.5 configuration and action data through the preceding dispatcher.
Source: Aschbacher--Smith C.6.1, printed pp.164--166.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {G : Type*} [Group G] {H Λ : Subgroup G}

def Endgame (H Λ : Subgroup G) : Prop :=
  let R := Λ ⊓ H
  let L := (pResidual 2 H).map H.subtype
  (GlobalIndexTwo H Λ ∧ (IsAlternatingBlock L 3 →
      Nonempty (H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (IsAlternatingBlock L 3 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧
      (IsDihedralGroup Λ ∨ IsSemidihedralGroup Λ)) ∨
    ((IsAlternatingBlock L 5 ∨ CubicPair L) ∧
      elementaryAbelianMaxJ (Λ ⊓ normalizer (R : Set G)) = elementaryAbelianMaxJ R ∧
      DihedralNormalizer H Λ)

/-- All six numbered clauses, retaining the literal type guards in (3)--(4). -/
structure SourceTheorem (H Λ : Subgroup G) : Prop where
  common : Common H Λ
  types : (∃ n, IsL2EvenBlock ((pResidual 2 H).map H.subtype) n) ∨
    IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∨
    IsAlternatingBlock ((pResidual 2 H).map H.subtype) 3 ∨
    CubicPair ((pResidual 2 H).map H.subtype)
  natural : ∀ n, IsL2EvenBlock ((pResidual 2 H).map H.subtype) n →
    primeRank 2 ((Λ ⊓ H) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) : Subgroup G) ≤ n ∧
      PairFamily H Λ
  cubic : IsAlternatingBlock ((pResidual 2 H).map H.subtype) 3 →
    primeRank 2 ((Λ ⊓ H) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) : Subgroup G) ≤ 1 ∧
      PairFamily H Λ
  four : (IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∨
    CubicPair ((pResidual 2 H).map H.subtype)) → FourFamily H Λ
  endgame : Endgame H Λ

variable [Finite G]

theorem Input.endgame (d : Input H Λ) : Endgame H Λ := by
  rcases d.conclusion.2 with ⟨n,hn,_,_,ha⟩ | ⟨h3,_,_,hc⟩ | ⟨ht,_,hJ,hg⟩
  · refine Or.inl ⟨ha,?_⟩
    intro h3
    let e := Classical.choice h3.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable ((pResidual 2 H).map H.subtype) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact hn.not_solvable.elim
  · rcases hc with ha | hb
    · exact Or.inl ⟨ha.1,fun _ => ha.2⟩
    · exact Or.inr (Or.inl ⟨h3,hb⟩)
  · rcases hg with ha | hc
    · refine Or.inl ⟨ha,?_⟩
      intro h3
      rcases ht with h5 | hp
      · have hh := h5.module_card_odd (by decide)
        have h3c := h3.module_card_odd (by decide)
        norm_num at hh h3c
        omega
      · exact (hp.not_chiZero (Or.inr (Or.inl h3))).elim
    · exact Or.inr (Or.inr ⟨ht,hJ,hc⟩)

theorem Input.source_theorem (d : Input H Λ) : SourceTheorem H Λ where
  common := d.conclusion.1
  types := d.residual_types
  natural _n hn := ⟨(d.natural_rank_and_family hn).1,(d.natural_rank_and_family hn).2.1⟩
  cubic h3 := ⟨(d.cubic_rank_and_family h3).1,(d.cubic_rank_and_family h3).2.1⟩
  four h := h.elim (fun h5 => (d.alternating_branch h5).1) (fun hp => (d.paired_branch hp).1)
  endgame := d.endgame

/-- C.6.1 with no earlier block, marking, rank or normalizer premise left over. -/
theorem theorem_C_6_1_full
    (hf : generalizedFitting H = pCore 2 H) (hm : QuotientModels H)
    (hΛ : IsPGroup 2 Λ) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = Λ ⊓ H) (hlt : Λ ⊓ H < Λ)
    (hc : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ Λ ⊓ H → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = Λ ⊓ H) : SourceTheorem H Λ :=
  (⟨hf,hm,hΛ,S,hS,hlt,hc⟩ : Input H Λ).source_theorem
end CFSG.Quasithin.ChapterC.Section06.Original
