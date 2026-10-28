module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Earlier
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At

/-!
# Fixed-involution setup at the original Sylow subgroup

The fixed line gives an involution. The original uniqueness theorem identifies
its centralizer with both the component and module normalizers. Every structural
invocation concerns the original G,T; the universal interfaces remain unchanged.
This is the local form of the proof in SmallFusion/Setup.lean.

Source: Aschbacher–Smith, 12.4.3 and the setup of 12.4.5, pp.812–813.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_orbit_eq (h : Hypothesis1223 K T L)
    (structural : Structural1222At K T) : componentOrbit L (T : Subgroup G) = L := by
  apply le_antisymm _ (le_componentOrbit L _)
  exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
    (structural L h).1

/-- Construct the centralizer/normalizer setup from the proved order of the
fixed subgroup. This applies to either small-module branch. -/
theorem exists_fixed_involution_setup_of_card_two
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hcard : Nat.card (fixedSubgroup L V) = 2) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (L : Set G) = centralizer ({z} : Set G) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) ∧
      centralizer (omegaOneAmbient ((center (T : Subgroup G)).map
        (T : Subgroup G).subtype) : Set G) ≤ normalizer (L : Set G) := by
  let _ := D.elementary
  have hne : fixedSubgroup L V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcard
    omega
  obtain ⟨z, hzne, _⟩ := (Nat.card_eq_two_iff' (1 : fixedSubgroup L V)).mp hcard
  have hz1 : (z : G) ≠ 1 := fun he => hzne (Subtype.ext he)
  have hzsq : (z : G) ^ 2 = 1 := by
    simpa using elemPow_eq_one_of_isElementaryAbelian
      (z : G) z.property.1
  have hzorder : orderOf (z : G) = 2 :=
    orderOf_eq_prime hzsq hz1
  have hzgen : fixedSubgroup L V = zpowers (z : G) := by
    apply (eq_of_le_of_card_ge (zpowers_le_of_mem z.property) ?_).symm
    rw [Nat.card_zpowers, hzorder, hcard]
  have hstruct := structural L h
  have hMnorm : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
    (hstruct.2.2 V D).2.2.2.resolve_right hne
  have hMC : normalizer (L : Set G) ≤ normalizer (fixedSubgroup L V : Set G) :=
    (le_inf hMnorm (normalizer_le_normalizer_centralizer L)).trans
      inf_normalizer_le_normalizer_inf
  have hMCz : normalizer (L : Set G) ≤ centralizer ({(z : G)} : Set G) := by
    rwa [hzgen, normalizer_zpowers_eq_centralizer_of_order_two _ hzorder] at hMC
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier earlier
    h.simpleQTKE T h.maximal_faithful.1
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hLN
    simpa only [source_orbit_eq h structural] using hu.normalizer_unique N hN hLN
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer hstruct.1
  let : IsElementaryAbelian 2 (fixedSubgroup L V) :=
    IsElementaryAbelian.of_le inf_le_left
  have hfixP : IsPGroup 2 (fixedSubgroup L V) :=
    IsElementaryAbelian.isPGroup 2 (fixedSubgroup L V)
  have hfixne : fixedSubgroup L V ≠ ⊥ := hne
  have hCzM : centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) := by
    rw [← normalizer_zpowers_eq_centralizer_of_order_two _ hzorder, ← hzgen]
    apply normalizer_le_of_unique_maximalTwoLocal huniq hfixP hfixne
    exact hLT.trans hMC
  have hVM : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal huniq
      (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
      (sup_le D.normalizes (hstruct.2.2 V D).1)
  have hzcenter : (z : G) ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
    refine ⟨⟨z, D.le_sylow z.property.1⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro t
    apply Subtype.ext
    change (t : G) * (z : G) = (z : G) * (t : G)
    exact mem_centralizer_singleton_iff.mp
      (hMCz (hstruct.1 t.property))
  have hzomega : (z : G) ∈ omegaOneAmbient
      ((center (T : Subgroup G)).map (T : Subgroup G).subtype) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl (z : G) hzcenter
      (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property.1)
  refine ⟨z, hzorder, hzgen, le_antisymm hMCz hCzM, le_antisymm hMnorm hVM,
    hzomega, ?_⟩
  exact (centralizer_le (Set.singleton_subset_iff.mpr hzomega)).trans hCzM


end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
