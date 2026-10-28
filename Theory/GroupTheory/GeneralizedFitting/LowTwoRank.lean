module
public import Theory.GroupTheory.SimpleTwoRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductCenters
public import Theory.GroupTheory.PrimeRankProduct
/-!
# A centerless semisimple group of two-rank at most two is simple

Each centerless component is nonabelian simple and has two-rank at least two
by the genuine Brauer–Suzuki consequence. Distinct components commute with
trivial intersection, so their product would have two-rank at least four.
Thus there is a single component and it is the whole nontrivial group.

Source: Aschbacher–Smith A.2.12, printed pp.35–36.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] [Nontrivial G]

theorem isSimple_of_semisimple_centerless_twoRank_le_two
    (hsemi : componentLayer G = ⊤) (hz : center G = ⊥) (hr : primeRank 2 G ≤ 2) :
    IsSimpleGroup G := by
  have hCZ {C : Subgroup G} (hC : IsComponent G C) : center C = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    exact le_bot_iff.mp (hz ▸ hC.center_map_le_center_of_semisimple hsemi)
  have hCS {C : Subgroup G} (hC : IsComponent G C) : IsSimpleGroup C := by
    let := hC.2
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq (hCZ hC)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hex : ∃ C : Subgroup G, IsComponent G C := by
    by_contra! hh
    have ht : (⊤ : Subgroup G) = ⊥ := by
      apply le_bot_iff.mp
      rw [← hsemi]
      exact sSup_le fun C hC => (hh C hC).elim
    exact top_ne_bot ht
  obtain ⟨C, hC⟩ := hex
  have hall (D : Subgroup G) (hD : IsComponent G D) : D = C := by
    by_contra hne
    let := hC.2
    let := hD.2
    let := hCS hC
    let := hCS hD
    have hcr := two_le_twoRank_of_nonabelian_simple
      (Group.IsPerfect.not_isMulCommutative C)
    have hdr := two_le_twoRank_of_nonabelian_simple
      (Group.IsPerfect.not_isMulCommutative D)
    have hc : C ≤ centralizer (D : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD (Ne.symm hne))
    have hd : Disjoint C D := by
      rw [disjoint_iff_inf_le]
      rintro x ⟨hxC,hxD⟩
      have hx : (⟨x,hxC⟩ : C) ∈ center C := by
        apply mem_center_iff.mpr
        intro y
        exact Subtype.ext (hc y.property x hxD).symm
      rw [hCZ hC, mem_bot] at hx
      exact congrArg Subtype.val hx
    have hup : primeRank 2 (C ⊔ D : Subgroup G) ≤ primeRank 2 G :=
      primeRank_le_of_injective 2 (C ⊔ D).subtype (C ⊔ D).subtype_injective
    rw [primeRank_sup_eq_add_of_disjoint_commuting C D hd hc 2] at hup
    omega
  have htop : C = ⊤ := by
    apply top_unique
    rw [← hsemi]
    exact sSup_le fun D hD => (hall D hD).le
  let : IsSimpleGroup C := hCS hC
  exact ((MulEquiv.subgroupCongr htop).trans topEquiv).symm.isSimpleGroup

end Theory.GroupTheory
