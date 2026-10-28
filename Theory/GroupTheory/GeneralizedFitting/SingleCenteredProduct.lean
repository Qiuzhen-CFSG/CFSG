module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CenterlessProduct
public import Theory.GroupTheory.DisjointCommutingProduct
/-!
# A direct complement for the sole centered component

When a component is proper and every other component is centerless, the
other components form an independent commuting family. Their external
product is therefore isomorphic to their generated subgroup B, and B is
centerless. The distinguished component centralizes B, has trivial
intersection with it, and together they generate the semisimple group.

The complement includes an actual component, retained in the conclusion
for subsequent two-local arguments. Source: Aschbacher–Smith A.2.12(III),
printed p.37.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.exists_centerless_direct_complement
    (hsemi : componentLayer G = ⊤) {C : Subgroup G} (hC : IsComponent G C)
    (hproper : C ≠ ⊤)
    (hothers : ∀ D : Subgroup G, IsComponent G D → D ≠ C → center D = ⊥) :
    ∃ B : Subgroup G, center B = ⊥ ∧
      (∃ D : Subgroup G, IsComponent G D ∧ D ≤ B) ∧ Nonempty (G ≃* C × B) := by
  classical
  let I := {D : Subgroup G // IsComponent G D ∧ D ≠ C}
  let H : I → Subgroup G := fun i => i.val
  let B : Subgroup G := ⨆ i : I, H i
  let : Fintype I := Fintype.ofFinite I
  have hc : Pairwise fun i j : I => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact ((commutator_eq_bot_iff_le_centralizer.mp
      (i.property.1.commutator_eq_bot_of_ne j.property.1
        (fun he => hij (Subtype.ext he)))) hx y hy).symm
  have hz (i : I) : center (H i) = ⊥ := hothers i.val i.property.1 i.property.2
  let f : (∀ i : I, H i) →* G := noncommPiCoprod hc
  have hf : Function.Injective f := injective_noncommPiCoprod_of_iSupIndep
    (iSupIndep_of_centerless_of_pairwise_commute H hz hc)
  have hr : f.range = B := noncommPiCoprod_range
  let eB : (∀ i : I, H i) ≃* B :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  have hBP : center (∀ i : I, H i) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    change x = 1
    funext i
    rw [Subgroup.center_pi] at hx
    have hi := hx i (Set.mem_univ i)
    simpa [hz i] using hi
  have hBZ : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := ((centerCongr eB).symm ⟨x, hx⟩).property
    change eB.symm x ∈ center (∀ i : I, H i) at hh
    rw [hBP, mem_bot] at hh
    exact eB.symm.injective (hh.trans (map_one eB.symm).symm)
  have hcomm : C ≤ centralizer (B : Set G) := by
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro i
    exact commutator_eq_bot_iff_le_centralizer.mp
      (i.property.1.commutator_eq_bot_of_ne hC i.property.2)
  have hgen : C ⊔ B = ⊤ := by
    apply top_unique
    rw [← hsemi]
    apply sSup_le
    intro D hD
    by_cases he : D = C
    · simpa only [he] using (le_sup_left : C ≤ C ⊔ B)
    · exact (le_iSup H (⟨D, hD, he⟩ : I)).trans le_sup_right
  have hd : Disjoint C B := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨hxC, hxB⟩
    have hz : (⟨x, hxB⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hcomm hxC y y.property)
    rw [hBZ, mem_bot] at hz
    exact congrArg Subtype.val hz
  have hD : ∃ D : Subgroup G, IsComponent G D ∧ D ≠ C := by
    by_contra! hh
    apply hproper
    apply top_unique
    rw [← hsemi]
    exact sSup_le fun D hD => (hh D hD).le
  obtain ⟨D, hD, hDC⟩ := hD
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C B hd hcomm
  exact ⟨B, hBZ, ⟨D, hD, le_iSup H (⟨D, hD, hDC⟩ : I)⟩,
    ⟨(e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv)).symm⟩⟩

end Theory.GroupTheory
