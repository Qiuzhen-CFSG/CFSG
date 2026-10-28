module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement.Overgroup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement.Parity
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement.MatrixBlocks

/-!
# Symplectic Borel placement

The marked Sylow normalizer is the full preimage of a Borel in L/Z(L).
Its join with the source Q = C_T(V) is solvable of characteristic two, so
E.6.7 supplies a decomposition whose blocks all have type A₃. If the Borel
escapes M, a block survives and embeds subnormally in a finite direct power
of the standard matrix Borel. Its quotient of order three forces even n,
and the root-commutator calculation excludes the resulting subnormal block,
including at n=2. At n=1, the genuine Sp₄(2)' Sylow is self-normalizing
and containment holds directly.

`exists_borel` concludes containment for every symplectic derived model.
The complete universal source E.6.7 input remains explicit; the actual
overgroup, its characteristic-two condition, and block exclusion are proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem alternating_three_of_solvable {X : Type*} [Group X] [Group.IsSolvable X]
    (hx : ChapterC.IsChiZeroBlock X) : ChapterC.IsAlternatingBlock X 3 := by
  rcases hx with ⟨n, hn, hshort, F, _, _, hF, hpsl, _⟩ | h3 | h5
  · obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hpsl
    let _ : Finite X := hshort.finite
    let _ : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three E (by
        rw [hE]
        have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
        omega)
    let _ : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.IsPerfect.not_isSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E)
      inferInstance).elim
  · exact h3
  · obtain ⟨e⟩ := h5.2.2.quotient_iso
    let _ : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let _ : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance).elim

/-- Every E.6.7 block in the constructed overgroup has alternating-three type.
This uses solvability, not the false intrinsic rank-one assertion for A₃. -/
theorem overgroup_blocks_alternating_three
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : SymplecticDerivedModel L n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
      (markedBorel S ⊔ sylowCentralizer (T : Subgroup G) V))
    (i : Fin d.count) : ChapterC.IsAlternatingBlock (d.block i) 3 := by
  let _ : Group.IsSolvable (markedBorel S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) :=
    overgroup_solvable (Q := sylowCentralizer (T : Subgroup G) V) hL (inf_le_right.trans (Subgroup.centralizer_le hU.1))
    (T.isPGroup'.to_le inf_le_left) hm S hS
  let _ : Group.IsSolvable (d.block i) := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (d.le i)) (inclusion_injective _)
  exact alternating_three_of_solvable (d.type i)

/-- Failure of containment produces a genuine subnormal A₃-block in a power
of the concrete nonbinary matrix Borel. The binary case is already closed.
The remaining intrinsic matrix exclusion is not assumed by this theorem. -/
theorem borel_or_even_matrix_block (h : HypothesisE61 K T M V) (input : E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : SymplecticDerivedModel L n) :
    (∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) ∨
      (1 < n ∧ Even n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2 ^ n ∧ ∃ (X : Type u) (_ : Group X),
          ChapterC.IsAlternatingBlock X 3 ∧
          ∃ (k : ℕ) (f : X →* (Fin k → Theory.SpecificGroups.SymplecticFour.borel (F := F))),
            Function.Injective f ∧ f.range.IsSubnormal) := by
  by_cases hn : n = 1
  · subst n
    exact Or.inl (exists_borel_of_model_one h hU hL hm)
  have hnlarge : 1 < n := lt_of_le_of_ne hm.1 (Ne.symm hn)
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL rfl
  by_cases hBM : markedBorel S ≤ M
  · exact Or.inl ⟨markedBorel S, le_inf (markedBorel_le S) hBM, markedBorel_preimage S⟩
  obtain ⟨d⟩ := overgroup_decomposition input hU hL hm S hS
  have hex : ∃ i, ¬ d.block i ≤ M := by
    by_contra! hi
    apply hBM
    have hD : markedBorel S ⊔ sylowCentralizer (T : Subgroup G) V ≤ M := by
      rw [d.generated]
      exact sup_le inf_le_right (iSup_le hi)
    exact le_sup_left.trans hD
  obtain ⟨i, _⟩ := hex
  have ha := overgroup_blocks_alternating_three hU hL hm S hS d i
  obtain ⟨F, hfield, hfinite, hchar, hF, k, f, hf, hs⟩ :=
    overgroup_matrix_embedding (Q := sylowCentralizer (T : Subgroup G) V) hL (inf_le_right.trans (Subgroup.centralizer_le hU.1))
      (T.isPGroup'.to_le inf_le_left) hm hnlarge S hS ha.2.1.twoPerfect
      (inclusion (d.le i)) (inclusion_injective _) (by
        exact (inclusion_range (d.le i)).symm ▸ d.subnormal i)
  exact Or.inr ⟨hnlarge, even_degree_of_matrix_block hF ha f hf, F, hfield, hfinite, hchar, hF, d.block i, inferInstance,
    ha, k, f, hf, hs⟩

/-- Borel containment for every odd exponent, including the exact derived binary endpoint. -/
theorem exists_borel_of_odd_exponent (h : HypothesisE61 K T M V) (input : E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : SymplecticDerivedModel L n) (hn : Odd n) :
    ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B := by
  rcases borel_or_even_matrix_block h input hU hL hm with hb | ⟨_, he, _⟩
  · exact hb
  · exact ((Nat.not_even_iff_odd.mpr hn) he).elim

/-- The symplectic Borel containment step of E.6.8, including Sp₄(2)'.
The only additional source input is universal E.6.7 with all its clauses;
the Borel is the full preimage of a Sylow normalizer in the actual L/Z(L). -/
theorem exists_borel (h : HypothesisE61 K T M V) (input : E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : SymplecticDerivedModel L n) :
    ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B := by
  rcases borel_or_even_matrix_block h input hU hL hm with hb |
    ⟨hn, heven, F, hfield, hfinite, hchar, hF, X, hgroup, hx, k, f, hf, hs⟩
  · exact hb
  · exact (MatrixBlocks.no_alternatingThree_embedding hn heven hF hx f hf hs).elim

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
