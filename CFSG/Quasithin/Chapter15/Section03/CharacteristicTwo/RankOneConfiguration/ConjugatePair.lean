module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.GroupTheory.IndexTwoConjugatePair

/-!
# The conjugate module pair from the fixed-plane geometry

The module calculation must identify `Z_S ∩ U_L` with `Z_S ∩ V₂`.
Since the central involution of `T` is not in either definite plane,
it is absent from `U_L`. The index-two conjugate-pair theorem then
gives the actual direct product, with its multiplication embeddings.
The action on `U_L` is the supplied compatible natural-eight action;
normalization of its conjugate is proved from invariance of `XS`.

This is the group-theoretic part of Aschbacher–Smith 15.3.32(5),
combined manuscript (1 March 2004), printed p.1133. The fixed-plane
identity and the residual construction of `XS` remain explicit inputs.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

open Subgroup

variable {G : Type*} [Group G]

/-- The central involutions of `T` belong to the fixed plane `Z_S`. -/
theorem centralInvolutions_le_fixedPlane (d : LocalData G) : d.Z ≤ d.ZS :=
  le_inf (le_conjugateSpanBy d.Z d.M)
    ((centralInvolutions_le_centralizer_sylow d.T).trans (centralizer_le inf_le_left))

/-- Source 15.3.32(5), conditional on the geometric intersection calculation
and the invariance of the end-node overgroup. The result includes the
actual direct-product isomorphism with the prescribed embeddings. -/
theorem lemma_15_3_32_5_of_geometry [Finite G]
    (d : LocalData G) {I N : Subgroup G} (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (hUS : d.componentModule I c.L ≤ d.S)
    (hSN : d.S ≤ N) (hNI : N ≤ I)
    (hTN : (d.T : Subgroup G) ≤ normalizer (N : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZplane : ¬ d.Z ≤ d.V₂)
    (hfixed : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    let U := d.componentModule I c.L
    Disjoint U (U.conjBy t) ∧
      N ≤ normalizer ((U ⊔ U.conjBy t : Subgroup G) : Set G) ∧
      U ≤ centralizer (U.conjBy t : Set G) ∧
      ∃ e : U × U.conjBy t ≃* ↥(U ⊔ U.conjBy t),
        ∀ u v, (e (u, v) : G) = (u : G) * (v : G) := by
  let U := d.componentModule I c.L
  have hnot : ¬ d.Z ≤ U := by
    intro hZU
    exact hZplane ((le_inf (centralInvolutions_le_fixedPlane d) hZU).trans
      (hfixed.le.trans inf_le_right))
  obtain ⟨x, hxZ, hxU⟩ := Set.not_subset.mp hnot
  rcases hxZ with ⟨xT, ⟨xC, hxC, rfl⟩, rfl⟩
  have hZ₀ : Nat.card (omega₁ (center d.T) (p := 2)) = 2 := by
    simpa only [LocalData.Z, centralInvolutions, ChapterA.Section05To06.centralOmega,
      card_map_of_injective (d.T : Subgroup G).subtype_injective,
      card_map_of_injective (center d.T).subtype_injective] using hZ
  have hxpow : (xC : d.T) ^ 2 = 1 := by
    let _ : IsElementaryAbelian 2 (omega₁ (center d.T) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative (center d.T)
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian xC hxC)
  have hxne : (xC : d.T) ≠ 1 := by
    intro he
    apply hxU
    change ((xC : d.T) : G) ∈ U
    rw [he]
    exact U.one_mem
  have hd : Disjoint U (U.conjBy t) :=
    disjoint_conjugate_of_avoiding_central_involution d.T.isPGroup' hZ₀
      xC xC.property (orderOf_eq_prime hxpow hxne) hxU hUS inf_le_left
      hindex ht htS hSN (hTN ht) (hNI.trans a.normalizes)
  exact ⟨hd, conjugate_pair_direct_product hUS hSN (hTN ht)
    (hNI.trans a.normalizes) hd⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

end
