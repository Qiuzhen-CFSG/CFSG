module
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.ExceptionalElimination
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Basic
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.HalfSylow
public import CFSG.Quasithin.Chapter1.Section01Inheritance

/-!
# Original selection inputs for the A₆ exceptional branch

Even characteristic at the original Sylow subgroup makes the selected
maximal two-local, and hence its involution centralizers, characteristic two.
Lemma 2.3.10 supplies the escaping half-Sylow β criterion; the Sylow transport
bound supplies the half-order estimate. The literal action kernel and its
surjective Sylow image give the quotient index 32.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 2.5.26,
printed p.569, using 1.1.3(2), 2.3.7(1), and 2.3.10.
-/

public section
open Subgroup Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne
open A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

theorem original_earlierSelection (d : EarlierSetup κ G) : EarlierSelection d.M d.T := by
  have hM : d.M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (d.simpleQTKE.evenCharacteristic d.T d.M d.maximalM d.t_le_m)
  refine ⟨?_, ?_, ?_⟩
  · intro g j hj ho
    have hMg : d.M.map (MulAut.conj g).toMonoidHom ∈ Chapter1.He G :=
      map_core_centralizer_le (MulAut.conj g).toMonoidHom (MulAut.conj g).injective d.M 2 hM
    have hp : IsPGroup 2 (zpowers j) := IsPGroup.of_card (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using ho)
    have hc := pCoreIn_selfCentralizing_centralizer hMg hp (zpowers_le.mpr hj)
    change _ ⊓ centralizer (zpowers j : Set G) ∈ Chapter1.He G at hc
    simpa only [zpowers_eq_closure, centralizer_closure] using hc
  · intro A J hAT hi hAJ hJ hout
    exact lemma_2_3_10 d.simpleQTKE d.T d.t_le_m d.unique_maximal hAT hi
      ⟨J, ⟨hJ, hAJ⟩, hout⟩
  · intro J hJ
    have h := gamma_twoPart_double_le d.T d.t_le_m d.unique_maximal hJ
    omega

theorem original_core_index (d : EarlierSetup κ G) : (d.SC.subgroupOf d.S).index = 32 := by
  rw [← d.toImageSylow_kernel, index_ker,
    MonoidHom.range_eq_top.mpr (ElementaryCore.toImageSylow_surjective d), card_top]
  exact AlternatingSix.ShadowLocal.sylow_card d.imageSylow
end CFSG.Quasithin.Chapter2.A6ShadowRankOne
