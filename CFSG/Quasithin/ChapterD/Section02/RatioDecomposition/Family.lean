module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Embedded
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Theory.GroupTheory.Fitting.Core

/-!
# Finite literal families of ratio factors

A decomposition records embedded faithful indecomposable actions, their
independent commutator supports and the original starred-subgroup family.
Disjoint unions compose decompositions through a one-step split. The resulting
starred blocks form a genuine partition, generate their original actors and
supply an internal direct product with the original multiplication map.

The additional `FittingFull` property records the D.2.17 hypothesis on each
factor without changing the underlying partition or action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, D.2.16–17,
printed pp.187–188 (1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u v
variable {G H L : Type u} {V W X : Type v}
  [Group G] [Group H] [Group L]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]

structure Decomposition (ρ : Representation (ZMod 2) G V) where
  Index : Type
  [finiteIndex : Finite Index]
  [nonemptyIndex : Nonempty Index]
  factor : Index → Factor ρ
  group_generation : ⨆ i, (factor i).actor = ⊤
  space_generation : ⨆ i, (factor i).space = ⊤
  space_independent : iSupIndep (fun i => (factor i).space)
  cross : ∀ i j, i ≠ j → (factor i).space ≤ fixedSpace ρ (factor j).actor
  covers : ∀ A ∈ QhatStar ρ, ∃ i, ∃ B ∈ QhatStar (factor i).action,
    B.map (factor i).embedding.groupMap = A
attribute [instance] Decomposition.finiteIndex Decomposition.nonemptyIndex

namespace Decomposition
variable {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}
  {τ : Representation (ZMod 2) L X}

def singleton [Finite G] [Nontrivial G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hi : IsRatioIndecomposable ρ)
    (hg : Jhat ρ = ⊤) (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤) : Decomposition ρ where
  Index := PUnit
  factor := fun _ => {
    Carrier := G
    Space := V
    action := ρ
    embedding := Embedding.refl ρ
    faithful := hf
    indecomposable := hi
    generated := hg
    full := hm }
  group_generation := by simp [Factor.actor, Embedding.refl, MonoidHom.range_eq_map]
  space_generation := by simp [Factor.space, Embedding.refl]
  space_independent := iSupIndep_subsingleton _
  cross i j hij := (hij (Subsingleton.elim _ _)).elim
  covers A hA := ⟨PUnit.unit,A,hA,by simp [Embedding.refl]⟩

private theorem independent_sum {ι κ : Type*}
    (a : ι → Submodule (ZMod 2) V) (b : κ → Submodule (ZMod 2) V)
    (ha : iSupIndep a) (hb : iSupIndep b) (hd : Disjoint (⨆ i,a i) (⨆ j,b j)) :
    iSupIndep (Sum.elim a b) := by
  classical
  intro i
  cases i with
  | inl i =>
    have hds : Disjoint (a i ⊔ ⨆ j, ⨆ (_ : j ≠ i), a j) (⨆ j,b j) :=
      hd.mono_left (sup_le (le_iSup a i) (iSup_le fun j => iSup_le fun _ => le_iSup a j))
    simpa only [iSup_sum, Sum.elim_inl, Sum.elim_inr, ne_eq,
      Sum.inl.injEq, Sum.inr_ne_inl, not_false_eq_true, iSup_true] using
      (ha i).disjoint_sup_right_of_disjoint_sup_left hds
  | inr i =>
    have hds : Disjoint (b i ⊔ ⨆ j, ⨆ (_ : j ≠ i), b j) (⨆ j,a j) :=
      hd.symm.mono_left (sup_le (le_iSup b i) (iSup_le fun j => iSup_le fun _ => le_iSup b j))
    simpa only [iSup_sum, Sum.elim_inl, Sum.elim_inr, ne_eq,
      Sum.inr.injEq, Sum.inl_ne_inr, not_false_eq_true, iSup_true, sup_comm] using
      (hb i).disjoint_sup_right_of_disjoint_sup_left hds

noncomputable def combine (d : Decomposition σ) (c : Decomposition τ)
    (e : Embedding σ ρ) (f : Embedding τ ρ)
    (hg : e.groupMap.range ⊔ f.groupMap.range = ⊤)
    (hs : IsCompl e.spaceMap.range f.spaceMap.range)
    (hcross1 : e.spaceMap.range ≤ fixedSpace ρ f.groupMap.range)
    (hcross2 : f.spaceMap.range ≤ fixedSpace ρ e.groupMap.range)
    (hstars : ∀ A ∈ QhatStar ρ,
      (∃ B ∈ QhatStar σ, B.map e.groupMap = A) ∨
      (∃ B ∈ QhatStar τ, B.map f.groupMap = A)) : Decomposition ρ := by
  classical
  refine {
    Index := d.Index ⊕ c.Index
    factor := Sum.elim (fun i => (d.factor i).map e) (fun i => (c.factor i).map f)
    group_generation := ?_
    space_generation := ?_
    space_independent := ?_
    cross := ?_
    covers := ?_ }
  · simp only [iSup_sum, Sum.elim_inl, Sum.elim_inr, Factor.map_actor,
      ← Subgroup.map_iSup, d.group_generation, c.group_generation,
      ← MonoidHom.range_eq_map]
    exact hg
  · simp only [iSup_sum, Sum.elim_inl, Sum.elim_inr, Factor.map_space,
      ← Submodule.map_iSup, d.space_generation, c.space_generation, Submodule.map_top]
    exact hs.sup_eq_top
  · have hind : iSupIndep (Sum.elim
        (fun i => (d.factor i).space.map e.spaceMap)
        (fun i => (c.factor i).space.map f.spaceMap)) := by
      apply independent_sum _ _
        (e.spaceMap.iSupIndep_map e.space_injective d.space_independent)
        (f.spaceMap.iSupIndep_map f.space_injective c.space_independent)
      simpa only [← Submodule.map_iSup, d.space_generation, c.space_generation,
        Submodule.map_top] using hs.disjoint
    convert hind using 1
    funext i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Factor.map_space]
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Sum.elim_inl, Factor.map_space, Factor.map_actor]
        exact e.map_fixed _ _ (d.cross i j (fun he => hij (congrArg Sum.inl he)))
      | inr j =>
        simp only [Sum.elim_inl, Sum.elim_inr, Factor.map_space, Factor.map_actor]
        apply le_trans (b := e.spaceMap.range)
        · rintro _ ⟨v,_,rfl⟩; exact ⟨v,rfl⟩
        · exact hcross1.trans (fixedSpace_antitone ρ (map_le_range _ _))
    | inr i =>
      cases j with
      | inl j =>
        simp only [Sum.elim_inl, Sum.elim_inr, Factor.map_space, Factor.map_actor]
        apply le_trans (b := f.spaceMap.range)
        · rintro _ ⟨v,_,rfl⟩; exact ⟨v,rfl⟩
        · exact hcross2.trans (fixedSpace_antitone ρ (map_le_range _ _))
      | inr j =>
        simp only [Sum.elim_inr, Factor.map_space, Factor.map_actor]
        exact f.map_fixed _ _ (c.cross i j (fun he => hij (congrArg Sum.inr he)))
  · intro A hA
    rcases hstars A hA with ⟨B,hB,hBA⟩ | ⟨B,hB,hBA⟩
    · obtain ⟨i,D,hD,hDB⟩ := d.covers B hB
      refine ⟨Sum.inl i,D,hD,?_⟩
      change D.map (e.groupMap.comp (d.factor i).embedding.groupMap) = A
      rw [← Subgroup.map_map, hDB, hBA]
    · obtain ⟨i,D,hD,hDB⟩ := c.covers B hB
      refine ⟨Sum.inr i,D,hD,?_⟩
      change D.map (f.groupMap.comp (c.factor i).embedding.groupMap) = A
      rw [← Subgroup.map_map, hDB, hBA]

theorem actors_independent (d : Decomposition ρ) :
    iSupIndep (fun i => (d.factor i).actor) := by
  intro i
  apply disjoint_iff_inf_le.mpr
  rintro g ⟨hgi,hgothers⟩
  obtain ⟨a,rfl⟩ := hgi
  have hfix : (d.factor i).space ≤
      fixedSpace ρ (⨆ j, ⨆ (_ : j ≠ i), (d.factor j).actor) := by
    rw [fixedSpace_iSup_family]
    apply le_iInf
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simpa only [iSup_pos hji] using d.cross i j (Ne.symm hji)
  have ha : a = 1 := by
    apply (d.factor i).faithful
    ext w
    simp only [map_one,Module.End.one_apply]
    apply (d.factor i).embedding.space_injective
    rw [(d.factor i).embedding.equivariant]
    exact hfix ⟨w,rfl⟩ ⟨_,hgothers⟩
  simpa only [ha,map_one] using (mem_bot.mpr (rfl : (1:G)=1))

theorem actors_commute (d : Decomposition ρ) (hf : Function.Injective ρ)
    {i j : d.Index} (hij : i ≠ j) {x y : G}
    (hx : x ∈ (d.factor i).actor) (hy : y ∈ (d.factor j).actor) : Commute x y := by
  apply hf
  ext v
  simp only [map_mul,Module.End.mul_apply]
  have hyv : ρ y v - v ∈ (d.factor j).space :=
    (d.factor j).embedding.moved_le_range (Submodule.subset_span ⟨y,hy,v,Submodule.mem_top,rfl⟩)
  have hxv : ρ x v - v ∈ (d.factor i).space :=
    (d.factor i).embedding.moved_le_range (Submodule.subset_span ⟨x,hx,v,Submodule.mem_top,rfl⟩)
  have hxy : ρ x (ρ y v - v) = ρ y v - v := d.cross j i hij.symm hyv ⟨x,hx⟩
  have hyx : ρ y (ρ x v - v) = ρ x v - v := d.cross i j hij hxv ⟨y,hy⟩
  rw [map_sub] at hxy hyx
  rw [sub_eq_iff_eq_add.mp hxy,sub_eq_iff_eq_add.mp hyx]
  abel

@[expose] def block (d : Decomposition ρ) (i : d.Index) : Set (Subgroup G) :=
  (Subgroup.map (d.factor i).embedding.groupMap) '' QhatStar (d.factor i).action

theorem block_nonempty (d : Decomposition ρ) (i : d.Index) : (d.block i).Nonempty := by
  have hn : (QhatStar (d.factor i).action).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have ht : (⊤ : Subgroup (d.factor i).Carrier) = ⊥ := by
      rw [← (d.factor i).generated,Jhat,he,sSup_empty]
    exact top_ne_bot ht
  exact hn.image _

theorem block_generates (d : Decomposition ρ) (i : d.Index) :
    sSup (d.block i) = (d.factor i).actor := by
  rw [block,sSup_image]
  simp only [← Subgroup.map_iSup]
  rw [← sSup_eq_iSup]
  change (Jhat (d.factor i).action).map (d.factor i).embedding.groupMap = _
  rw [(d.factor i).generated,← MonoidHom.range_eq_map]
  rfl

theorem block_stars (d : Decomposition ρ) : (⋃ i, d.block i) = QhatStar ρ := by
  ext A
  constructor
  · intro hA
    obtain ⟨i,B,hB,rfl⟩ := Set.mem_iUnion.mp hA
    exact ((d.factor i).embedding.stars B).mp hB
  · intro hA
    obtain ⟨i,B,hB,rfl⟩ := d.covers A hA
    exact Set.mem_iUnion.mpr ⟨i,B,hB,rfl⟩

theorem blocks_disjoint (d : Decomposition ρ) : Pairwise (fun i j => Disjoint (d.block i) (d.block j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro A hAi hAj
  have hA : A ∈ QhatStar ρ := d.block_stars ▸ Set.mem_iUnion.mpr ⟨i,hAi⟩
  have hi : A ≤ (d.factor i).actor := by rw [← d.block_generates i]; exact le_sSup hAi
  have hj : A ≤ (d.factor j).actor := by rw [← d.block_generates j]; exact le_sSup hAj
  exact hA.1.2.1.1 (le_bot_iff.mp ((le_inf hi hj).trans
    (d.actors_independent.pairwiseDisjoint hij).le_bot))

theorem product_equiv (d : Decomposition ρ) (hf : Function.Injective ρ)
    [DecidableEq d.Index] :
    ∃ e : (∀ i, (d.factor i).Carrier) ≃* G,
      ∀ i x, e (Pi.mulSingle i x) = (d.factor i).embedding.groupMap x := by
  let : Fintype d.Index := Fintype.ofFinite d.Index
  let f := fun i => (d.factor i).embedding.groupMap
  have hc : Pairwise fun i j => ∀ (x : (d.factor i).Carrier) (y : (d.factor j).Carrier),
      Commute (f i x) (f j y) := by
    intro i j hij x y
    exact d.actors_commute hf hij ⟨x,rfl⟩ ⟨y,rfl⟩
  let q := MonoidHom.noncommPiCoprod f hc
  have hq : Function.Injective q := MonoidHom.injective_noncommPiCoprod_of_iSupIndep f
    d.actors_independent (fun i => (d.factor i).embedding.group_injective)
  have hqs : Function.Surjective q := MonoidHom.range_eq_top.mp (by
    rw [MonoidHom.noncommPiCoprod_range]
    exact d.group_generation)
  refine ⟨MulEquiv.ofBijective q ⟨hq,hqs⟩,?_⟩
  intro i x
  exact MonoidHom.noncommPiCoprod_mulSingle f (hcomm := hc) i x

@[expose] def FittingFull (d : Decomposition ρ) : Prop :=
  ∀ i, subspaceCommutator (d.factor i).action ⊤
    (fittingSubgroup (d.factor i).Carrier) = ⊤

theorem singleton_fitting_full [Finite G] [Nontrivial G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hi : IsRatioIndecomposable ρ)
    (hg : Jhat ρ = ⊤) (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hfit : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    (singleton hf hi hg hm).FittingFull := fun _ => hfit

theorem combine_fitting_full (d : Decomposition σ) (c : Decomposition τ)
    (e : Embedding σ ρ) (f : Embedding τ ρ)
    (hg : e.groupMap.range ⊔ f.groupMap.range = ⊤)
    (hs : IsCompl e.spaceMap.range f.spaceMap.range)
    (hcross1 : e.spaceMap.range ≤ fixedSpace ρ f.groupMap.range)
    (hcross2 : f.spaceMap.range ≤ fixedSpace ρ e.groupMap.range)
    (hstars : ∀ A ∈ QhatStar ρ,
      (∃ B ∈ QhatStar σ, B.map e.groupMap = A) ∨
      (∃ B ∈ QhatStar τ, B.map f.groupMap = A))
    (hd : d.FittingFull) (hc : c.FittingFull) :
    (combine d c e f hg hs hcross1 hcross2 hstars).FittingFull := by
  intro i
  cases i with
  | inl i => exact hd i
  | inr i => exact hc i

end Decomposition
end CFSG.Quasithin.ChapterD.RatioDecomposition
