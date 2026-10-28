module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedGeneration.SwappedActor

/-!
# The actual pair-centralizer E-member

The norm construction identifies the source subgroup C_(K Kᵃ)(a), without
replacing its ambient embedding. Its join with the original tau is the
nonsolvable E-member required by the paired E.2.2 generation argument.

Source: Aschbacher–Smith, E.1.11, printed p.213, and E.2.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.PairedGeneration.SwappedActor
variable {G : Type*} [Group G] [Finite G]

theorem pair_centralizer_tau_source (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    {a : G} (ha : a ∈ A) (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    let I := (K ⊔ K.map (MulAut.conj a).toMonoidHom) ⊓ centralizer ({a} : Set G)
    IsEMemberAt f (T : Subgroup G) A (I ⊔ tau (T : Subgroup G) A) ∧
      ¬ Group.IsSolvable (I ⊔ tau (T : Subgroup G) A : Subgroup G) := by
  dsimp only
  rw [← NormPair.norm_eq_pair_centralizer hK hm
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha)]
  exact ⟨norm_tau_member T hK hcore hindex hr hAT ha hm hne,
    norm_tau_not_solvable _ hK hm⟩

end CFSG.Quasithin.ChapterE.Structure.PairedGeneration.SwappedActor
