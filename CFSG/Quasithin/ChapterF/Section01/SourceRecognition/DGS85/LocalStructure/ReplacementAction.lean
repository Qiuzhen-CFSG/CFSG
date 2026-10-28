module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementModule
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryConjugationSection

/-!
# Faithful conjugation on the actual DGS replacement span

Under contrary relative normality, the constructed elementary subgroup
V=<Z_delta^X> has a canonical faithful representation of X/C_X(V).
Its vector space is the additive copy of V inside X. The coordinate map
retains each original element, and the quotient action is original
conjugation. The denominator of the vector-space section is trivial.

The group action kernel is the literal centralizer, not an assumed two-core.
Identifying this quotient with a rank-one model, proving the residual fixed
space condition and the corrected Sylow fixed-generation premise remain
part of source assembly. The construction includes both neighboring-center branches.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121, and the corrected
5.12 module hypotheses, pp.113--115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal replacement module has a canonical faithful action of its
actual centralizer quotient, with original conjugation coordinates. -/
theorem source_replacement_faithful_action_of_inter_normal (h : LocallyRankOneTriple P B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ hE : IsElementaryAbelian 2 (V.subgroupOf X),
      letI := hE
      ∃ (K : Subgroup X) (hK : K.Normal),
        letI := hK
        ∃ σ : Representation (ZMod 2) (X ⧸ K) (Additive (V.subgroupOf X)),
          K = (centralizer (V : Set G)).subgroupOf X ∧ Function.Injective σ ∧
            Nonempty (BinaryConjugationSection X V ⊥ (σ.comp (QuotientGroup.mk' K))) := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (sylowCenterSpan (P i)) X
  have hVX : V ≤ X := ((source_replacement_span_le_inter_omega_of_inter_normal h i hn).trans
    ((map_subtype_le _).trans inf_le_left)).trans (le_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (source_replacement_span_le_inter_omega_of_inter_normal h i hn)
  let N := V.subgroupOf X
  let hE : IsElementaryAbelian 2 N := IsElementaryAbelian.subgroupOf hVX
  let := hE
  refine ⟨hE,?_⟩
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr (le_normalizer_conjugateSpanBy _ _)
  let K := centralizer (N : Set X)
  let hK : K.Normal := inferInstance
  let := hK
  let q := QuotientGroup.mk' K
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hk : q.ker = centralizer (N : Set X) := QuotientGroup.ker_mk' K
  let σ := NormalElementaryQuotient.representation N q hq hk
  refine ⟨K,hK,σ,?_,NormalElementaryQuotient.representation_injective N q hq hk,?_⟩
  · ext x
    constructor
    · intro hx v hv
      have he := hx ⟨v,hVX hv⟩ hv
      exact congrArg Subtype.val he
    · intro hx v hv
      apply Subtype.ext
      exact hx v hv
  · let e : N ≃* V := subgroupOfEquivOfLe hVX
    refine ⟨{
      section_le := hVX
      kernel_le := bot_le
      normalized := le_normalizer_conjugateSpanBy _ _
      coordinates := {
        toFun := fun v => Multiplicative.ofAdd (Additive.ofMul (e.symm v))
        map_one' := by simp only [map_one]; rfl
        map_mul' := fun _ _ => by simp only [map_mul]; rfl }
      onto := ?_
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · intro w
      exact ⟨e w.toAdd.toMul,congrArg (fun v => Multiplicative.ofAdd (Additive.ofMul v))
        (e.symm_apply_apply _)⟩
    · ext v
      change e.symm v = 1 ↔ (v : G) = 1
      constructor
      · intro hv
        have he := congrArg e hv
        rw [e.apply_symm_apply,map_one] at he
        exact congrArg Subtype.val he
      · intro hv
        have he : v = 1 := Subtype.ext hv
        rw [he,map_one]
    · intro x v
      apply Multiplicative.toAdd.injective
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (congrArg Subtype.val
        (NormalElementaryQuotient.representation_apply N q hq hk x
          (Additive.ofMul (e.symm v)))).symm


/-- The original noncentral interface, retained as a specialization of the general construction. -/
theorem source_replacement_faithful_action (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ hE : IsElementaryAbelian 2 (V.subgroupOf X),
      letI := hE
      ∃ (K : Subgroup X) (hK : K.Normal),
        letI := hK
        ∃ σ : Representation (ZMod 2) (X ⧸ K) (Additive (V.subgroupOf X)),
          K = (centralizer (V : Set G)).subgroupOf X ∧ Function.Injective σ ∧
            Nonempty (BinaryConjugationSection X V ⊥ (σ.comp (QuotientGroup.mk' K))) := by
  have _ := hB
  have _ := hS
  have _ := hnc
  exact source_replacement_faithful_action_of_inter_normal h i hn

end CFSG.Quasithin.ChapterF.Source.DGS85
