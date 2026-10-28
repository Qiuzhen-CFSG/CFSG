module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySixteenFusion

/-!
# An intrinsic bound on elementary subgroups of Hall–Janko

Use the existing checked Sylow enumeration. An elementary subgroup inside
the distinguished four has order at most four. Otherwise, fix an involution
outside that four: all elements of the subgroup lie among its commuting
involutions, of which the certificate gives at most sixteen. Sylow conjugacy
transfers the bound to every elementary subgroup of the actual J₂ carrier.
No new enumeration or computation is needed. The ordinary unitary source
uses this to exclude an elementary image of order at least 64.

Source: GLS3 Table 5.3g; the native ATLAS J2G1-p100B0 Sylow certificates.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.ElementarySixteenFusion
open ExceptionalParabolics GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData RankOneFourNormalizer Checks

theorem elementary_sylow_card_le_sixteen
    (W : Subgroup Carrier) (hWs : W ≤ s) [IsElementaryAbelian 2 W] : Nat.card W ≤ 16 := by
  classical
  by_cases hWf : W ≤ four
  · exact (card_le_of_le hWf).trans (by rw [card_four]; decide)
  obtain ⟨a,ha,hafour⟩ := Set.not_subset.mp hWf
  obtain ⟨i,hi⟩ := exists_sElement (hWs ha)
  have hiW : sElement i ∈ W := hi.symm ▸ ha
  have hinot : i ∉ fourIndices := by
    intro h
    apply hafour
    have hf : sElement i ∈ four := by
      simp only [fourIndices,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact fourElement_mem 0
      · exact fourElement_mem 1
      · exact fourElement_mem 2
      · exact fourElement_mem 3
    exact hi ▸ hf
  have hinv {i : Fin 128} (hi : sElement i ∈ W) : involutionIndex i := by
    have hs : inclusion (sElement i) * inclusion (sElement i) = 1 := by
      rw [← map_mul, ← pow_two,elemPow_eq_one_of_isElementaryAbelian _ hi,map_one]
    rw [sElement_inclusion] at hs
    exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hs,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hs⟩
  let idx : W → Fin 128 := fun y => Classical.choose (exists_sElement (hWs y.property))
  have hidx (y : W) : sElement (idx y) = (y : Carrier) :=
    Classical.choose_spec (exists_sElement (hWs y.property))
  have hidxinj : Function.Injective idx := by
    intro y z hyz
    exact Subtype.ext ((hidx y).symm.trans ((congrArg sElement hyz).trans (hidx z)))
  have hidxmem (y : W) : idx y ∈ commutingInvolutions i := by
    have hyW : sElement (idx y) ∈ W := (hidx y).symm ▸ y.property
    have hh := congrArg (fun z : W => inclusion (z : Carrier))
      (mul_comm' (⟨sElement i,hiW⟩ : W) ⟨sElement (idx y),hyW⟩)
    change inclusion (sElement i * sElement (idx y)) = inclusion (sElement (idx y) * sElement i) at hh
    simp only [map_mul,sElement_inclusion] at hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinv hyW,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hh,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hh⟩
  let f : W → ↥(commutingInvolutions i) := fun y => ⟨idx y,hidxmem y⟩
  have hb := Nat.card_le_card_of_injective f (fun y z h => hidxinj (congrArg Subtype.val h))
  have hc : Nat.card ↥(commutingInvolutions i) = (commutingInvolutions i).card := by simp
  rw [hc] at hb
  obtain h | ⟨h,_,_⟩ := commuting_involutions_check i (hinv hiW) hinot <;> omega

theorem elementary_card_le_sixteen
    (W : Subgroup Carrier) [IsElementaryAbelian 2 W] : Nat.card W ≤ 16 := by
  obtain ⟨P,hWP⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_le_sylow
  let S : Sylow 2 Carrier := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier P S
  let e : Carrier ≃* Carrier := MulAut.conj g
  let W' := W.map e.toMonoidHom
  have hP : (P : Subgroup Carrier).map e.toMonoidHom = s :=
    congrArg (fun Q : Sylow 2 Carrier => (Q : Subgroup Carrier)) hg
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map e.toMonoidHom
  have hb := elementary_sylow_card_le_sixteen W' (hP ▸ map_mono hWP)
  rwa [card_map_of_injective e.injective] at hb
end Sporadic.LeechRelated.J2.ElementarySixteenFusion
