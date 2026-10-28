module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedSylowSource
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry
public import Stellmacher.ElementaryAbelianMaxOrder
/-!
# The actual ambient rank in the single A5 centralizer branch

The original Thompson equality puts every maximum elementary subgroup of the
ambient Sylow inside the selected Sylow. With trivial block centralizer, its
marked dihedral wreath model bounds these elementary subgroups by sixteen.
This removes the rank premise from the secondary component census.

Source: Aschbacher–Smith, 2.4.29, printed pp.545–546.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.single_alternating_ambient_rank_le_four_of_centralizer_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥) :
    primeRank 2 T ≤ 4 := by
  let R := (d.S:Subgroup d.H).map d.H.subtype
  let Di := centralizer (d.block:Set d.H)
  obtain ⟨e,he⟩ := d.single_alternating_marked_ambient_sylow_model hG T hM hTM hu hST hsingle hA
  let f : R →* SymmetricFourWreath.P :=
    (MonoidHom.fst SymmetricFourWreath.P Di).comp e.toMonoidHom
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    change ((MonoidHom.fst SymmetricFourWreath.P Di).comp e.toMonoidHom).ker=⊥
    rw [he,d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA,hD]
    simp
  have hJ := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).2.2
  apply (primeRank_le_iff_elementary_card_le T).mpr
  intro E hE
  let A := E.map (T:Subgroup G).subtype
  have hA : IsElementaryAbelian 2 A := hE.map _
  obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty (T:Subgroup G)
  have hBR : B≤R := (le_sSup hB).trans (hJ.le.trans (sSup_le fun _ hC=>hC.1))
  let : IsElementaryAbelian 2 B := hB.2.1
  let eB := subgroupOfEquivOfLe hBR
  have hBi : IsElementaryAbelian 2 (B.subgroupOf R) :=
    IsElementaryAbelian.of_surjective eB.symm.toMonoidHom eB.symm.surjective
  have hc := SymmetricFourWreath.elementaryInP_card_bound ((B.subgroupOf R).map f) (hBi.map f)
  calc
    Nat.card E = Nat.card A := (card_map_of_injective (f:=(T:Subgroup G).subtype) (K:=E) (T:Subgroup G).subtype_injective).symm
    _ ≤ Nat.card B := hB.2.2 A (map_subtype_le _) hA
    _ = Nat.card (B.subgroupOf R) := (Nat.card_congr eB.toEquiv).symm
    _ = Nat.card ((B.subgroupOf R).map f) := (card_map_of_injective hf).symm
    _ ≤ 2^4 := hc
end CFSG.Quasithin.Chapter2
