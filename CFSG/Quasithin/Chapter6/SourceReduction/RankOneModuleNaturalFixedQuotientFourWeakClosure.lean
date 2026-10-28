module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOriginal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientRank
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubled

/-!
# E.6.1 for the original Hermitian layer

The full original Hermitian model makes the moved layer irreducible under L.
Its conjugates under M therefore have trivial intersection or coincide.
Faithfulness identifies its Sylow centralizer with O₂(LT), and uniqueness
over LT supplies the final E.6.1 condition. No TI or weak-closure assumption
is added to the original source hypotheses.

Away from half-degree two, the actual first Thompson subgroup centralizes
the layer, so the original rank-one theorem gives globalR = 1.
Source: Aschbacher–Smith, 6.1.3–4, printed pp.664–665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n s : ℕ} [NeZero s]

local instance weakClosureFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance weakClosureBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

omit [Finite G] in
private theorem hermitian_invariant_subgroup {B : Subgroup G}
    (hm : IsConjugationModel L B (SL2.BinarySmall.hermitian s))
    (A : Subgroup G) (hAB : A ≤ B) (hLA : L ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = B := by
  obtain ⟨e,f,hf⟩ := hm
  let D := (A.subgroupOf B).map f.toMonoidHom
  have hi : ∀ g x, x ∈ D → multiplicativeAction s g x ∈ D := by
    intro g x hx
    obtain ⟨q,hq⟩ := e.surjective g
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    have he : e (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl,hq]
    obtain ⟨v,hv,rfl⟩ := hx
    let y := f.symm (multiplicativeAction s g (f v))
    have hy : y ∈ A.subgroupOf B := by
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian s g (f v).toAdd)) : G) ∈ A
      rw [←he,hf]
      exact (mem_normalizer_iff.mp (hLA l.property) v.val).mp hv
    exact ⟨y,hy,f.apply_symm_apply _⟩
  rcases multiplicativeAction_irreducible s D hi with hb | ht
  · left
    apply bot_unique
    intro x hx
    let v : B := ⟨x,hAB hx⟩
    have hv : f v ∈ D := mem_map_of_mem f.toMonoidHom (show v ∈ A.subgroupOf B from hx)
    rw [hb] at hv
    exact mem_bot.mpr (congrArg Subtype.val
      (f.injective ((mem_bot.mp hv).trans f.map_one.symm)))
  · right
    apply le_antisymm hAB
    intro x hx
    let v : B := ⟨x,hx⟩
    have hv : f v ∈ D := by rw [ht]; trivial
    obtain ⟨w,hw,he⟩ := hv
    have hvA : v ∈ A.subgroupOf B := (f.injective he) ▸ hw
    exact hvA

/-- The actual Hermitian moved layer is TI under the original M. -/
theorem original_hermitian_layer_ti
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian s))
    {g : G} (hg : g ∈ M) :
    layer L V ⊓ (layer L V).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (layer L V).map (MulAut.conj g).toMonoidHom = layer L V := by
  have hnL := hm.normalizes
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
      (((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal) hg)
  have hnLg : L ≤ normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G) := by
    have hc := map_mono (f := (MulAut.conj g).toMonoidHom) hnL
    rwa [hgL,map_equiv_normalizer_eq] at hc
  rcases hermitian_invariant_subgroup hm
      (layer L V ⊓ (layer L V).map (MulAut.conj g).toMonoidHom) inf_le_left
      ((le_inf hnL hnLg).trans inf_normalizer_le_normalizer_inf) with hb | he
  · exact Or.inl hb
  · right
    symm
    apply eq_of_le_of_card_ge (he.symm.le.trans inf_le_right)
    rw [card_map_of_injective (MulAut.conj g).injective]

/-- Faithfulness on the original layer detects its exact Sylow centralizer. -/
theorem original_hermitian_layer_sylow_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian s)) :
    ChapterE.Section06.sylowCentralizer (T : Subgroup G) (layer L V) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hCL : L ⊓ centralizer (layer L V : Set G) = L.pCoreIn 2 :=
    hm.centralizer_eq_core (OrthogonalFourMinus.RankOne.hermitian_injective s)
  have hlocal : (L ⊔ (T : Subgroup G)) ⊓ centralizer (layer L V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    ambient_centralizer_eq_core_of_normal_supplement L (layer L V) T
      h.sylow_normalizes_L (h.layer_le_L.trans le_sup_left)
      (sup_le hm.normalizes h.sylow_normalizes_layer)
      T.isPGroup' hCL (local_core_centralizes_layer h)
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    obtain ⟨S,hS⟩ := h.local_mem.1.prop.2.1
    exact (pCoreIn_le_sylow _ S).trans_eq hS
  exact le_antisymm ((inf_le_inf_right _ le_sup_right).trans_eq hlocal)
    (le_inf hQ (local_core_centralizes_layer h))

/-- The full original Hermitian model supplies E.6.1 on the same moved layer,
including TI and the required uniqueness over its Sylow centralizer. -/
theorem original_hermitian_layer_hypothesisE61
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian s)) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V) := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop,?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes_L) (le_componentOrbit L T)
  refine ⟨h.simpleQTKE,h.maximal,h.sylow_le,h.nontrivial_action,
    h.layer_elementary,h.layer_le_T,
    (normal_subgroupOf_iff_le_normalizer h.layer_le_T).mpr h.sylow_normalizes_layer,
    fun g hg => original_hermitian_layer_ti h hm hg,?_⟩
  intro N hN hle
  have hLT : L ⊔ (T : Subgroup G) ≤ N := by
    apply le_trans ?_ hle
    refine le_inf (le_inf (sup_le h.L_le h.sylow_le)
      (sup_le hm.normalizes h.sylow_normalizes_layer)) ?_
    rw [original_hermitian_layer_sylow_centralizer h hm]
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have h₁ := hu.normalizer_unique N hN
  have h₂ := hu.normalizer_unique M h.maximal
  rw [horbit] at h₁ h₂
  exact (h₁ hLT).trans (h₂ (sup_le h.L_le h.sylow_le)).symm

/-- The original outside witness and Hermitian model give global rank one
away from half-degree two, with Thompson centralization already discharged. -/
theorem original_hermitian_layer_globalR
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian s))
    (hs : 1 < s) (hs2 : s ≠ 2) :
    ChapterE.globalR (layer L V) = 1 :=
  original_layer_rank_one_of_thompson_centralizes h hout
    ((h.rankOneInput hout).commutator_input.hermitian_thompson_one_centralizes_of_half_degree_ne_two
      hm hs hs2)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
