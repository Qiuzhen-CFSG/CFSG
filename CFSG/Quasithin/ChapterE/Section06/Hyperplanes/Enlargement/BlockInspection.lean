module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.FixedSpaces
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Transport
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance

/-!
# Assembly of the block inspection for E.6.23

Given an actual corank-two overgroup, exclude its proper block alternative,
and reduce its proper ordinary-component alternative to an actual A₆
configuration. The fixed-space argument then excludes this configuration
using the separate orbit-containment input. Thus the original block equals
its overgroup and is a block of the larger centralizer.

For a conjugate preserving U, apply C.1.9 directly inside C_G(U). Otherwise
U and its conjugate meet in corank exactly two; both blocks persist there,
and C.1.9 gives the equal-or-commuting alternative. Odd-core vanishing
discharges C.1.9's extra O₂,₃ condition in both cases.

The lifting and two proper-overgroup inspections remain explicit unproved
obligations. This module does not yet establish BlockEnlargement from the
permitted earlier-source inputs alone. In particular the solvable A₃ case
cannot be inserted into the perfect C-component family for 1.2.4.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed pp.254–255 (PDF pp.265–266), and C.1.9, p.123.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
open ComponentBalance

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The two proper-overgroup inspections force equality with the original block. -/
theorem eq_of_inspections [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hsix : SixOrbitContainment M V)
    (hblock : ProperBlockExclusion M V) (hcomponent : ProperComponentInspection M V)
    {U A L X : Subgroup G} (hU : U ∈ obstructionFamily M V) (hUh : IsHyperplane V U)
    (hL : SmallBlock U L) (he : ¬ L ≤ M)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U) (hc : subgroupCorank V A = 2)
    (hLX : L ≤ X)
    (hX : (CentralizerBlock A X ∧ ChapterC.IsChiZeroBlock X) ∨ CentralizerComponent A X) :
    L = X := by
  by_contra hn
  have hp : L < X := lt_of_le_of_ne hLX hn
  rcases hX with ⟨hb, ht⟩ | hcomp
  · exact hblock U hU hUh L hL he A hA hAU hc X hp hb ht
  · exact no_proper_six_enlargement h h15 h13 hsix hU hUh hL he hA hAU hc
      (hcomponent U hU hUh L hL he A hA hAU hc X hp hcomp)

/-- Equality transfers the actual block, including subnormality, to C_G(A). -/
theorem block_persists_of_inspections [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hsix : SixOrbitContainment M V) (hlift : CorankTwoLifting M V)
    (hblock : ProperBlockExclusion M V) (hcomponent : ProperComponentInspection M V)
    {U A L : Subgroup G} (hU : U ∈ obstructionFamily M V) (hUh : IsHyperplane V U)
    (hL : SmallBlock U L) (he : ¬ L ≤ M)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U) (hc : subgroupCorank V A = 2) :
    CentralizerBlock A L := by
  obtain ⟨X, hLX, hX⟩ := hlift U hU hUh L hL he A hA hAU hc
  have heq := eq_of_inspections h h15 h13 hsix hblock hcomponent hU hUh hL he hA hAU hc hLX hX
  subst X
  rcases hX with ⟨hb, _⟩ | hcomp
  · exact hb
  · have hs : ChapterC.IsShort L := hL.2.2.elim (fun h => h.2.1) (fun h => h.2.1)
    exact ⟨hcomp.1, ⟨inferInstance,
      hs.of_mulEquiv (subgroupOfEquivOfLe hcomp.1).symm, hcomp.2.1⟩⟩

omit [Finite G] in
private theorem escape_conjugate {L : Subgroup G} (he : ¬ L ≤ M)
    {g : G} (hg : g ∈ M) : ¬ L.map (MulAut.conj g).toMonoidHom ≤ M := by
  intro hle
  apply he
  intro x hx
  have hc := hle (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have hh := M.mul_mem (M.mul_mem (M.inv_mem hg) hc) hg
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- Conditional assembly; the three inspection obligations must still be proved.
No persistence or unconditional commutation is among the assumptions. -/
theorem blockEnlargement_of_inspections [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (h21 : OddCoreFree V) (hsix : SixOrbitContainment M V)
    (h19 : BlockCommutationInput G) (hlift : CorankTwoLifting M V)
    (hblock : ProperBlockExclusion M V) (hcomponent : ProperComponentInspection M V) :
    BlockEnlargement M V := by
  intro U hU hUh L hL he g hg
  let f := (MulAut.conj g).toMonoidHom
  have hUg : IsHyperplane V (U.map f) :=
    ⟨(map_mono (f := f) hUh.1).trans (mem_normalizer_iff_map_conj_eq.mp hg.2).le,
      (corank_conjugate V U g hg.2).trans hUh.2⟩
  have hLg := smallBlock_conjugate hL g
  by_cases hfix : U = U.map f
  · rw [← hfix] at hLg
    exact centralizerBlocks_equal_or_commute h19 h21 hU.1 hU.2.1
      ⟨hL.1, hL.2.1⟩ ⟨hLg.1, hLg.2.1⟩
  · have hm := (lemma_E_6_16_1 h h15 hUh (fun hh => he (hL.1.trans hh))).2.1
    have heg : ¬ L.map f ≤ M := escape_conjugate he hg.1
    have hUgG : U.map f ∈ obstructionFamily M V :=
      small_escape_mem h hUg.1 (by rw [hUg.2]; omega) (fun hc => heg (hLg.1.trans hc))
    have hcor : subgroupCorank V (U ⊓ U.map f) = 2 :=
      (hyperplane_intersection_index hUh hUg hfix).1
    have hAG : U ⊓ U.map f ∈ obstructionFamily M V :=
      small_escape_mem h (inf_le_left.trans hUh.1) (by omega)
        (fun hc => he ((hL.1.trans (Subgroup.centralizer_le inf_le_left)).trans hc))
    exact centralizerBlocks_equal_or_commute h19 h21 hAG.1 hAG.2.1
      (block_persists_of_inspections h h15 h13 hsix hlift hblock hcomponent
        hU hUh hL he hAG inf_le_left hcor)
      (block_persists_of_inspections h h15 h13 hsix hlift hblock hcomponent
        hUgG hUg hLg heg hAG inf_le_right hcor)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
