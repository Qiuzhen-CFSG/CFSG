module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.Lifting
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.FlagCoordinates
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Bruhat
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.StandardOvergroups

/-!
# Degree-five generation by actual rank-two flag overgroups

In basis coordinates, enlarge the supplied minimal parabolic by omitting one
additional node. Nonadjacent omitted nodes give two binary two-dimensional
blocks and quotient S₃ × S₃. Adjacent omitted nodes give one three-dimensional
block and quotient PSL₃(2); every other diagonal block has trivial linear group.
The checked flag diagonal action identifies each kernel with the intrinsic
two-core. These equivalences are transported through the actual embedding in K.

The overgroups generate: their join contains the standard Borel, so the proved
Bruhat overgroup theorem makes it a partial-flag stabilizer. Each cut is omitted
by one of the chosen pairs, forcing that flag to be empty. Basis conjugation
and the supplied component isomorphism transport this conclusion to K.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1145,
the L₅(2) generation paragraph in the proof of 15.3.49. This is the intrinsic
component helper; quotient lifting and the degree-four alternative belong to
`BinaryGeneration.lean`.
-/

open Subgroup
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration

private theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
private theorem univ_five : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide

private theorem label01 : pairLabel 0 1 = ![0, 0, 0, 1, 2] := by
  funext t
  fin_cases t <;> simp [pairLabel, cutLabel, univ_four, Finset.filter_insert,
    Finset.filter_singleton]
private theorem label12 : pairLabel 1 2 = ![0, 1, 1, 1, 2] := by
  funext t
  fin_cases t <;> simp [pairLabel, cutLabel, univ_four, Finset.filter_insert,
    Finset.filter_singleton]
private theorem label23 : pairLabel 2 3 = ![0, 1, 2, 2, 2] := by
  funext t
  fin_cases t <;> simp [pairLabel, cutLabel, univ_four, Finset.filter_insert,
    Finset.filter_singleton]

private theorem adjacent_block_card (a : Fin 3) :
    Fintype.card (Block (pairLabel a.castSucc a.succ) (a.castLE (by decide))) = 3 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases a <;>
    simp [label01, label12, label23, univ_five, Finset.filter_insert, Finset.filter_singleton]

private theorem adjacent_other_card (a : Fin 3) (k : Fin 5)
    (hk : k ≠ a.castLE (by decide)) :
    Fintype.card (Block (pairLabel a.castSucc a.succ) k) ≤ 1 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases a <;> fin_cases k <;>
    simp_all [label01, label12, label23, univ_five, Finset.filter_insert, Finset.filter_singleton]

/-- Only the three-dimensional block survives among the diagonal factors. -/
private noncomputable def adjacentFactorsEquiv (a : Fin 3) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (pairLabel a.castSucc a.succ) k)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) := by
  classical
  let k : Fin 5 := a.castLE (by decide)
  let f := Pi.evalMonoidHom
    (fun k : Fin 5 => BinaryLinear.GL (BlockSpace (pairLabel a.castSucc a.succ) k)) k
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      funext l
      by_cases hl : l = k
      · subst l
        exact hxy
      · have hc := adjacent_other_card a l hl
        exact (linearBlock_eq_one_of_card_le_one _ _ hc (x l)).trans
          (linearBlock_eq_one_of_card_le_one _ _ hc (y l)).symm
    · intro x
      exact ⟨Function.update 1 k x, Function.update_self ..⟩
  let c : BlockSpace (pairLabel a.castSucc a.succ) k ≃ₗ[ZMod 2] Space 3 :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
      (Fintype.equivFinOfCardEq (adjacent_block_card a)).symm
  exact (MulEquiv.ofBijective f hf).trans
    ((linearGroupCongr c).trans linearThreeEquivProjective)

private theorem pair_small (b : FiveBasis) (i j : Fin 4) (hij : i ≠ j) :
    SmallQuotient (flagStabilizer b ({i, j} : Set (Fin 4))ᶜ) := by
  by_cases h : i.val + 1 < j.val ∨ j.val + 1 < i.val
  · exact Or.inl ⟨(flagDiagonalQuotientEquiv b _).trans (pairFactorsEquiv i j h)⟩
  · have hadj : ∃ a : Fin 3, ({i, j} : Set (Fin 4)) = {a.castSucc, a.succ} := by
      have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · let a : Fin 3 := ⟨i.val, by have := j.isLt; omega⟩
        refine ⟨a, ?_⟩
        have hai : a.castSucc = i := Fin.ext rfl
        have haj : a.succ = j := Fin.ext (by dsimp [a]; omega)
        rw [hai, haj]
      · let a : Fin 3 := ⟨j.val, by have := i.isLt; omega⟩
        refine ⟨a, ?_⟩
        have haj : a.castSucc = j := Fin.ext rfl
        have hai : a.succ = i := Fin.ext (by dsimp [a]; omega)
        rw [hai, haj, Set.pair_comm]
    obtain ⟨a, ha⟩ := hadj
    rw [ha]
    exact Or.inr ⟨(flagDiagonalQuotientEquiv b _).trans (adjacentFactorsEquiv a)⟩

private theorem exists_other (i : Fin 4) : ∃ j : Fin 4, i ≠ j := by
  by_cases hi : i = 0
  · exact ⟨1, by simp [hi]⟩
  · exact ⟨0, hi⟩

/-- No proper cut is preserved by all pairs containing the original node. -/
private theorem standard_pairs_generate (i : Fin 4) (W : Subgroup (LinearGroup 5))
    (hW : ∀ j : Fin 4, i ≠ j → flagStabilizer standardBasis ({i, j} : Set (Fin 4))ᶜ ≤ W) :
    W = ⊤ := by
  obtain ⟨j, hij⟩ := exists_other i
  have hBW : standardBorel ≤ W :=
    (flagStabilizer_antitone standardBasis (Set.subset_univ _)).trans (hW j hij)
  obtain ⟨cuts, hcuts⟩ := standard_overgroups_of_bruhat hasBruhatDecomposition W hBW
  have hc (j : Fin 4) (hij : i ≠ j) : cuts ⊆ ({i, j} : Set (Fin 4))ᶜ := by
    apply (CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.cutStabilizer_le_iff
      standardBasis _ _).mp
    change flagStabilizer standardBasis _ ≤ flagStabilizer standardBasis _
    rw [← hcuts]
    exact hW j hij
  have he : cuts = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    by_cases hki : i = k
    · have := hc j hij hk
      simp [← hki] at this
    · have := hc k hki hk
      simp at this
  rw [hcuts, he, flagStabilizer_empty]

private theorem pairs_generate (b : FiveBasis) (i : Fin 4) (W : Subgroup (LinearGroup 5))
    (hW : ∀ j : Fin 4, i ≠ j → flagStabilizer b ({i, j} : Set (Fin 4))ᶜ ≤ W) :
    W = ⊤ := by
  let c := MulAut.conj b.equivFun
  have hb : b.map b.equivFun = standardBasis := by
    ext i j
    simp [standardBasis, Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have hmap : ∀ cuts : Set (Fin 4),
      (flagStabilizer b cuts).map c.toMonoidHom = flagStabilizer standardBasis cuts := by
    intro cuts
    rw [flagStabilizer_map_conj, hb]
  have he : W.map c.toMonoidHom = ⊤ := by
    apply standard_pairs_generate i
    intro j hij
    rw [← hmap]
    exact map_mono (hW j hij)
  apply top_unique
  intro g _
  have hm : c g ∈ W.map c.toMonoidHom := by rw [he]; trivial
  simpa only [mem_map_equiv, MulEquiv.symm_apply_apply] using hm

/-- Transport the intrinsic two-core, as well as the overgroup itself. -/
private theorem small_map {A X : Type*} [Group A] [Group X]
    (f : A →* X) (hf : Function.Injective f) (Q : Subgroup A) (hQ : SmallQuotient Q) :
    SmallQuotient (Q.map f) := by
  let a := (Q.equivMapOfInjective f hf).symm
  let q := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  change _ ∨ _ at hQ
  rcases hQ with hQ | hQ
  · obtain ⟨e⟩ := hQ
    exact Or.inl ⟨q.trans e⟩
  · obtain ⟨e⟩ := hQ
    exact Or.inr ⟨q.trans e⟩

open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
  (linearModel ambientFlagStabilizer)
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
  (deletedFlag_stabilizer)

/-- The actual rank-two flag overgroups of any supplied degree-five minimal
parabolic form a nonempty family generating the component. Each member has
literal intrinsic two-core quotient S₃ × S₃ or PSL₃(2). -/
public theorem rankTwoFive_generation {X : Type*} [Group X] [Finite X] {K P : Subgroup X}
    (pos : BinaryGeometry.Position K P 5) (S : Sylow 2 K)
    (hSP : (S : Subgroup K) ≤ P.subgroupOf K) :
    (smallComponentOvergroups K P).Nonempty ∧ K ≤ sSup (smallComponentOvergroups K P) := by
  classical
  obtain ⟨b, i, _hi, hP⟩ := position_deletedFlag (m := 4) (by decide) pos S hSP
  let e := linearModel pos.model
  let f : LinearGroup 5 →* X := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hPmodel : P = (flagStabilizer b {i}ᶜ).map f := by
    rw [hP, ambientFlagStabilizer, deletedFlag_stabilizer]
    change ((flagStabilizer b {i}ᶜ).comap e.toMonoidHom).map K.subtype = _
    rw [show (flagStabilizer b {i}ᶜ).comap e.toMonoidHom =
      (flagStabilizer b {i}ᶜ).map e.symm.toMonoidHom from
        (map_equiv_eq_comap_symm e.symm _).symm, map_map]
  have hsmall (j : Fin 4) (hij : i ≠ j) :
      (flagStabilizer b ({i, j} : Set (Fin 4))ᶜ).map f ∈ smallComponentOvergroups K P := by
    refine ⟨?_, ?_, small_map f hf _ (pair_small b i j hij)⟩
    · rw [hPmodel]
      apply map_mono
      apply flagStabilizer_antitone
      intro k hk hki
      exact hk (Or.inl hki)
    · rintro x ⟨g, _hg, rfl⟩
      exact (e.symm g).property
  constructor
  · obtain ⟨j, hij⟩ := exists_other i
    exact ⟨_, hsmall j hij⟩
  · have hW : (sSup (smallComponentOvergroups K P)).comap f = ⊤ := by
      apply pairs_generate b i
      intro j hij
      exact map_le_iff_le_comap.mp (le_sSup (hsmall j hij))
    intro x hx
    have hm : e ⟨x, hx⟩ ∈ (sSup (smallComponentOvergroups K P)).comap f := by
      rw [hW]
      trivial
    change f (e ⟨x, hx⟩) ∈ sSup (smallComponentOvergroups K P) at hm
    change (e.symm (e ⟨x, hx⟩)).val ∈ sSup (smallComponentOvergroups K P) at hm
    simpa only [MulEquiv.symm_apply_apply] using hm

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
