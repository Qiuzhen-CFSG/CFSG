module
public import CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedCompletion
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-!
# Actor-rank restrictions for the remaining exchanged natural actions

Faithfulness on the spanning exchanged pair embeds the index-two constituent
stabilizer in its actual symmetric model. This bounds the original actor rank.
G.10.2 excludes the S₇ constituent; S₅ and S₈ force equality, including trivial
X₀ and a half-dimensional marked space. The S₆ constituent leaves actor rank
three or four. These restrictions use the original source hypotheses, without
the stronger larger-actor hypothesis used by the Chapter 14 adapter from which
the stabilizer calculation is adapted.

The exact finite list feeds `CorrectedReduction` and the strict quotient.
Whole-action recognition of these natural rows remains necessary.
Source: Aschbacher--Smith G.10.2, G.10.16 and G.11.6, printed pp.357,363--366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition

private theorem symmetric_eight_two_rank : primeRank 2 (Equiv.Perm (Fin 8)) ≤ 4 := by
  let S := Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeSylow
  rw [S.primeRank_eq]
  change primeRank 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeGroup ≤ 4
  rw [primeRank_equiv 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeWreathEquiv]
  apply WreathTwoElementaryRank.rank_bound (r := 2) _ (by decide)
  apply primeRank_le_of_noncommutative_card_prime_pow (n := 2)
  · norm_num [DihedralGroup.nat_card, DihedralGroup.card]
  · exact DihedralGroup.not_commutative (by decide) (by decide)

private theorem elementary_card (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
  rw [Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)

/-- The index-two stabilizer embeds in the literal natural symmetric model. -/
private theorem natural_stabilizer_embedding
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
    {v : U} {W I : Submodule (ZMod 2) U} {X H : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hH : H ≤ subspaceStabilizer ρ I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤) (n : ℕ)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    ∃ j : (subspaceStabilizer ρ I).subgroupOf X →* Equiv.Perm (Fin n),
      Function.Injective j := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let P := H ⊔ (X ⊓ subspaceStabilizer ρ I)
  let σ := Section09.constituentAction ρ H (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right
  obtain ⟨e,c,stable,hc⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let i : Y →* P := {
    toFun := fun y => ⟨y.val.val, (show X ⊓ subspaceStabilizer ρ I ≤ P from le_sup_right) ⟨y.val.property,y.property⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let j := d.toMonoidHom.comp ((QuotientGroup.mk' σ.ker).comp i)
  refine ⟨j, (injective_iff_map_eq_one j).mpr ?_⟩
  intro y hy
  have hq : QuotientGroup.mk' σ.ker (i y) = 1 := by
    apply d.injective
    change d (QuotientGroup.mk' σ.ker (i y)) = 1 at hy
    simpa only [map_one] using hy
  have hk : σ (i y) = 1 := (QuotientGroup.eq_one_iff _).mp hq
  apply Subtype.ext
  apply Subtype.ext
  exact h.eq_one_of_fixes_spanning_constituent hgen y.val.property (fun u hu =>
    congrArg (fun a : Module.End (ZMod 2) I => (a ⟨u,hu⟩ : U)) hk)

/-- Adding the exchanged orbit contributes exactly one to the actor rank. -/
theorem exchanged_natural_actor_bound
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
    {v : U} {W I : Submodule (ZMod 2) U} {X H : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hH : H ≤ subspaceStabilizer ρ I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤)
    (hindex : (subspaceStabilizer ρ I).relIndex X = 2) (n r : ℕ)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n)))
    (hr : primeRank 2 (Equiv.Perm (Fin n)) ≤ r) :
    finrank (ZMod 2) (Additive X) ≤ r + 1 := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  obtain ⟨j,hj⟩ := natural_stabilizer_embedding h hH hgen n hm
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective (MonoidHom.ofInjective hj).symm.toMonoidHom
    (MonoidHom.ofInjective hj).symm.injective
  have hc := (primeRank_le_iff_elementary_card_le _).mp hr j.range inferInstance
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, elementary_card Y] at hc
  have hy := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have he := Y.card_mul_index
  change Y.index = 2 at hindex
  rw [hindex, elementary_card Y, elementary_card X, ← pow_succ] at he
  have he' := (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  omega

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The remaining natural degrees with literal actor and marked-space ranks.
In particular the seven-letter constituent is impossible. -/
theorem exchanged_natural_ranks
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hnonsolv : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I)
    (n : ℕ) (hn : 5 ≤ n) (hnu : n ≤ 8)
    (hmodel : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    (n = 5 ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) V = 8 ∧
      finrank (ZMod 2) (Additive X) = 3 ∧ X₀ = ⊥ ∧ finrank (ZMod 2) W = 4) ∨
    (n = 6 ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) V = 8 ∧
      (finrank (ZMod 2) (Additive X) = 3 ∨ finrank (ZMod 2) (Additive X) = 4)) ∨
    (n = 8 ∧ finrank (ZMod 2) I = 6 ∧ finrank (ZMod 2) V = 12 ∧
      finrank (ZMod 2) (Additive X) = 5 ∧ X₀ = ⊥ ∧ finrank (ZMod 2) W = 6) := by
  obtain ⟨x,_,hc,hd,_⟩ := exchanged_lowRank_pair h cover hw hS hnonsolv hL hm hI hgeo
  have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
    apply top_unique
    rw [← hc.sup_eq_top]
    exact sup_le (Homogeneous.le_orbitSpan _ _ I) (le_iSup (fun y : X => I.map (ρ y)) x)
  obtain ⟨_,_,_,_,hi,_⟩ := hgeo
  have hb := exchanged_natural_actor_bound h hI.invariant hgen hi n
  obtain ⟨e,c,stable,hc'⟩ := hmodel
  have hdim := c.finrank_eq
  rw [finrank_top] at hdim
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have hbound := h.dimension_bound.1
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · have hr := hb 2 ⟨e,c,stable,hc'⟩
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    simp only [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide),Fintype.card_fin] at hdim
    have heq := h.numerical_equality_of_actor_dimension_le (by omega)
    exact Or.inl ⟨rfl,by omega,by omega,by omega,heq.1,by omega⟩
  · have hr := hb 3 ⟨e,c,stable,hc'⟩
      BinaryNaturalDual.FiveActors.ModuleGeometry.symmetric_six_rank_le_three
    simp only [BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin] at hdim
    exact Or.inr (Or.inl ⟨rfl,by omega,by omega,by omega⟩)
  · have hr := hb 3 ⟨e,c,stable,hc'⟩
      Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric.le
    simp only [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] at hdim
    omega
  · have hr := hb 4 ⟨e,c,stable,hc'⟩ symmetric_eight_two_rank
    simp only [BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Fintype.card_fin] at hdim
    have heq := h.numerical_equality_of_actor_dimension_le (by omega)
    exact Or.inr (Or.inr ⟨rfl,by omega,by omega,by omega,heq.1,by omega⟩)

end CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
