module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The component Sylow subgroup and its ambient center

An actual identification L ≃ A₆ identifies T_L with D₈ by intersecting the
Sylow subgroup with L normal in C_G(z). Since T normalizes T_L, it normalizes
its characteristic center of order two and therefore centralizes that center.
The identification of L itself remains an explicit premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
after Lemma 16.3.12, printed p.1182 / PDF p.1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

theorem component_dihedral_of_equiv (d : Prepared T z t L)
    (e : L ≃* AlternatingSix.ShadowLocal.A6) :
    Nonempty (componentSylow T L ≃* DihedralGroup 4) := by
  let C := involutionCentralizer z
  have hTC : (T : Subgroup G) ≤ C := d.counterexample.localSetup.sylow_centralizes
  have hLC : L ≤ C := d.counterexample.localSetup.component.1
  let : (L.subgroupOf C).Normal := d.counterexample.normal
  obtain ⟨S, hS⟩ := (T.subtype hTC).exists_subgroupOf_eq_of_normal (L.subgroupOf C)
  let j := subgroupOfEquivOfLe hLC
  let P := S.mapSurjective (f := j.toMonoidHom) j.surjective
  have hP : (P : Subgroup L) = (T : Subgroup G).subgroupOf L := by
    change (S : Subgroup _).map j.toMonoidHom = _
    rw [hS]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, hLC x.property⟩, x.property⟩, hx, rfl⟩
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨q⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral Q
  let swap : componentSylow T L ≃* (T : Subgroup G).subgroupOf L := {
    toFun x := ⟨⟨x, x.property.2⟩, x.property.1⟩
    invFun x := ⟨x.val, x.property, x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ⟨swap.trans ((MulEquiv.subgroupCongr hP.symm).trans
    (((P : Subgroup L).equivMapOfInjective e.toMonoidHom e.injective).trans q))⟩

omit [Finite G] in
theorem component_center_central_of_dihedral (d : Prepared T z t L)
    (hD : Nonempty (componentSylow T L ≃* DihedralGroup 4)) :
    (T : Subgroup G) ≤ centralizer (ambientCenter (componentSylow T L) : Set G) := by
  obtain ⟨e⟩ := hD
  have hc : Nat.card (centerIn (componentSylow T L)) = 2 := by
    rw [centerIn_eq_map_center, card_map_of_injective (componentSylow T L).subtype_injective,
      Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide
  have hn : (T : Subgroup G) ≤ normalizer (componentSylow T L : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer d.counterexample.sylow_le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have h := centralizes_of_normalizes_card_two hc (normalizes_centerIn hn)
  simpa only [centerIn_eq_map_center, ambientCenter] using h

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
