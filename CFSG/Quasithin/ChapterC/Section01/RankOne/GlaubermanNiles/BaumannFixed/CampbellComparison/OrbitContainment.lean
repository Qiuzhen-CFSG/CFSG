module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.ConjugateOrbits
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.Commutator.CentralizingFactor


/-!
# Campbell II.5.4: conjugates lie in the paired replacement

The A-span of F′ᵍ is elementary abelian. Its join with C_A₁(F′ᵍ) is
therefore elementary and contains the maximum replacement F′ᵍ C_A₁(F′ᵍ),
so the joins coincide. Both are A-invariant. If [A₁,F′ᵍ] were nontrivial,
the commutator dichotomy would make Z′ᵍ A-invariant, contradicting the
original rank-one separation. Thus F′ᵍ centralizes A₁, and maximality
puts F′ᵍ inside A₁.

The final source consumer constructs the same actual maximal subgroup for
all moving maximum elementary A and all g outside it. Source: Campbell,
*Pushing up in Finite Groups* (1979), II.5.4, printed p.28;
Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Finite H] [Group H'] [Finite H']
  {B B' : Type*} [Group B] [Finite B] [Group B'] [Finite B']
  {e : B →* H} {e' : B' →* H'}
  {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem InLocalClass.paired_conjugate_le_replacement (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hAQ : ¬ A ≤ pCore 2 H)
    (M : Subgroup H) (hM : (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤)
    (hNZ : normalizer (d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) : Set H) ≤ M)
    (g : H) (hg : g ∉ M) :
    (d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom ≤
      d.transfer d' (Campbell.F H') ⊔
        (((A ⊓ pCore 2 H) ⊔ Campbell.F H) ⊓ centralizer (d.transfer d' (Campbell.F H') : Set H)) := by
  let Y := d.transfer d' (Campbell.F H')
  let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
  let Yg := Y.map (MulAut.conj g).toMonoidHom
  let A₀ := (A ⊓ pCore 2 H) ⊔ Campbell.F H
  let A₁ := Y ⊔ (A₀ ⊓ centralizer (Y : Set H))
  let C := A₁ ⊓ centralizer (Yg : Set H)
  let W := Yg ⊔ C
  let E := conjugateSpanBy Yg A
  have hd := h.paired_replacement_geometry hB m h' hB' m' d d' hS' hV A hA
  have hYg := h.paired_conjugates_in_core_thompson hB m h' hB' m' d d' hV g
  have hYQ := h.transferred_campbellF_le_core hB m h' hB' m' d d' hV
  have hRQ : Campbell.J (pCore 2 H) ≤ pCore 2 H := sSup_le fun _ hA => hA.1
  have hW := h'.paired_conjugate_replacement hB' m' d d' hYQ A₁ hd.2.1 hd.2.2.1 g
  have hCQ : C ≤ pCore 2 H := inf_le_left.trans hd.2.2.1
  have hAN : A ≤ normalizer (C : Set H) := hd.2.2.2.2.2 g
  let : IsElementaryAbelian 2 E := h.paired_conjugate_span_elementary hB m h' hB' m' d d'
    hS hS' hV A hA M hM hNZ g hg
  let : IsElementaryAbelian 2 A₁ := hd.2.1.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ A₁ from inf_le_left)
  have hCE : C ≤ centralizer (E : Set H) :=
    le_centralizer_conjugateSpanBy_of_normalizes C Yg A hAN inf_le_right
  let : IsElementaryAbelian 2 (E ⊔ C : Subgroup H) := IsElementaryAbelian.sup_of_le_centralizer hCE
  have hEQ : E ≤ pCore 2 H := conjugateSpanBy_le (hYg.1.trans hRQ) le_normalizer_of_normal
  have hWsub : W ≤ E ⊔ C := sup_le_sup (le_conjugateSpanBy Yg A) le_rfl
  have hWE : W = E ⊔ C := Subgroup.eq_of_le_of_card_ge hWsub
    (hW.2.2 _ ((sup_le hEQ hCQ).trans (pCore_isPGroup.le_sylow_of_normal d.sylow)) inferInstance)
  have hAW : A ≤ normalizer (W : Set H) := by
    rw [hWE]
    exact (le_inf (le_normalizer_conjugateSpanBy Yg A) hAN).trans
      (normalizer_inf_normalizer_le_normalizer_sup E C)
  have hAA₁ : A ≤ normalizer (A₁ : Set H) :=
    le_normalizer_iff_commutator_le_right.mpr (hd.2.2.2.2.1.trans hd.2.2.2.1)
  have hAC : A ≤ normalizer ((⁅A₁,W⁆ : Subgroup H) : Set H) := by
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hAA₁ ha),
      mem_normalizer_iff_map_conj_eq.mp (hAW ha)]
  have hcomm : ⁅A₁,W⁆ = ⁅A₁,Yg⁆ := by
    apply commutator_eq_of_product_centralizing_factor
      (coe_mul_of_left_le_normalizer_right Yg C
        ((le_centralizer_iff.mp (show C ≤ centralizer (Yg : Set H) from inf_le_right)).trans
          (Subgroup.centralizer_le_normalizer _)))
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show C ≤ A₁ from inf_le_left))
  have hzero : ⁅A₁,Yg⁆ = ⊥ := by
    rcases h'.paired_conjugate_commutator_dichotomy hB' m' d d' hS' A₁ hd.2.1 hd.2.2.1 g with hb | hz
    · exact hb
    · exfalso
      have hAZ : A ≤ normalizer (Z.map (MulAut.conj g).toMonoidHom : Set H) := by
        rw [←hz,←hcomm]
        exact hAC
      obtain ⟨x,hx,hxQ⟩ := Set.not_subset.mp hAQ
      have hxmap : x ∈ (normalizer (Z : Set H)).map (MulAut.conj g).toMonoidHom := by
        rw [map_equiv_normalizer_eq]
        exact hAZ hx
      obtain ⟨y,hy,hey⟩ := hxmap
      have hconj : g⁻¹*x*g ∈ M := by
        have he : g⁻¹*x*g=y := by rw [←hey]; simp [MulAut.conj_apply,mul_assoc]
        rw [he]
        exact hNZ hy
      have hginv : g⁻¹ ∉ M := by intro hh; exact hg (by simpa using M.inv_mem hh)
      exact h.campbell_maximal_separation hB m d hS M hM g⁻¹ x hginv (hA.1 hx) hxQ
        (by simpa using hconj)
  have hYC : Yg ≤ centralizer (A₁ : Set H) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  obtain ⟨A',hA',hFA'⟩ := h'.campbellF_le_some_maxElementary hB' d'
  let : IsElementaryAbelian 2 (d.transfer d' A') := (d.transfer_maxElementary d' A' hA').2.1
  have hYA' : Y ≤ d.transfer d' A' := map_mono (comap_mono hFA')
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYA'
  let : IsElementaryAbelian 2 Yg := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  exact maxElementary_contains_elementary_centralizer _ A₁ Yg hd.2.1
    ((hYg.1.trans hRQ).trans (pCore_isPGroup.le_sylow_of_normal d.sylow)) hYC

theorem InLocalClass.exists_paired_orbit_containment (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (hn : ¬ d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) ≤
      centralizer (Campbell.J (⊤ : Subgroup H) : Set H)) :
    ∃ M : Subgroup H, (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤ ∧
      normalizer (d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) : Set H) ≤ M ∧
      ∀ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), ¬ A ≤ pCore 2 H →
        ∀ g ∉ M, (d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom ≤
          d.transfer d' (Campbell.F H') ⊔
            (((A ⊓ pCore 2 H) ⊔ Campbell.F H) ⊓ centralizer (d.transfer d' (Campbell.F H') : Set H)) := by
  obtain ⟨M,hSM,hMt,hbound⟩ := h.exists_campbell_maximal_normalizer_bound hB m d hS
  have hNZ := hbound _ (d.transferred_fixed_centralizes_thompson d') hn
  exact ⟨M,hSM,hMt,hNZ,fun A hA hAQ g hg => InLocalClass.paired_conjugate_le_replacement
    h hB m h' hB' m' d d' hS hS' hV A hA hAQ M ⟨hSM,hMt⟩ hNZ g hg⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles
