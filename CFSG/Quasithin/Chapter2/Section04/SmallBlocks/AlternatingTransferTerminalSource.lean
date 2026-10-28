module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTransferFixedFiveSource
/-!
# The actual transfer involution contradicts the secondary A6 component

A transferred involution in T_u outside the original S is outside every
marked subgroup whose image lies in S. The index-two four-normalizer
criterion in the actual A6 component forces a factor five in its centralizer;
C_G(z)=M has order 2304. This is the literal terminal application, retaining
the original ambient groups and the actual transfer witness.

Source: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_transfer_marks_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥)
    (K Tu F : Subgroup G) (hTuK : Tu ≤ normalizer (K : Set G))
    (hTu : IsPGroup 2 Tu) (e : K ≃* AlternatingSix.ShadowLocal.A6)
    [IsKleinFour F] (hFK : F ≤ K) (hFTu : F ≤ Tu)
    (R : Subgroup Tu) (hR : R.index = 2)
    (hRS : R.map Tu.subtype ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hRF : R.map Tu.subtype ≤ normalizer (F : Set G))
    (hx : ∃ x ∈ Tu, x ∉ normalizer (F : Set G))
    (z : G) (hz : centralizer ({z} : Set G) = M)
    (hfuse : ∃ i∈Tu, i∉(d.S : Subgroup d.H).map d.H.subtype ∧
      orderOf i=2 ∧ IsConj z i) : False := by
  obtain ⟨i,hiTu,hiS,hi2,hzi⟩ := hfuse
  let it : Tu := ⟨i,hiTu⟩
  have hi : it∉R := fun hh => hiS (hRS ⟨it,hh,rfl⟩)
  exact d.single_alternating_moving_four_not_isConj hG T hM hTM hu hST hsingle hA hD
    K Tu F hTuK hTu e hFK hFTu R hR hRF hx it hi hi2 z hz hzi
end CFSG.Quasithin.Chapter2
