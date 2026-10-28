module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import Theory.SpecificGroups.OrthogonalFourBinary.NaturalAction

/-!
# Lifting finite orthogonal calculations through the compatible action

The kernel of the actual quadratic-isometry action is `C_M(V)`, proved
from compatibility with conjugation. An abelian image of `Y` therefore
puts its commutator subgroup in `C_G(V)`. A bound on the normalizer of
the image of `T_E` lifts to `N_M(T_E)≤T` when the action kernel lies in `T`.

`actionImage` always uses the specified `NaturalAction`; no abstract
wreath-group identification is substituted for the action. The remaining
finite image calculations are separate proof obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2, 15.3.7 and the proof of 15.3.68, printed pp.1121–1122 and 1154.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] {V M : Subgroup G}

def actionImage (d : OrthogonalFourBinary.NaturalAction V M) (H : Subgroup G) :=
  (H.subgroupOf M).map d.action

theorem action_ker (d : OrthogonalFourBinary.NaturalAction V M) :
    d.action.ker = (centralizer (V : Set G)).subgroupOf M := by
  ext m
  constructor
  · intro hm
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := d.intertwines m ⟨v,hv⟩
    change d.action m = 1 at hm
    rw [hm] at hh
    have he : (m : G) * v * (m : G)⁻¹ = v := by
      exact hh.symm.trans (congrArg Subtype.val (d.coordinates.symm_apply_apply ⟨v,hv⟩))
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hm
    change d.action m = 1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    let v := d.coordinates.symm (Multiplicative.ofAdd w)
    have hh := d.intertwines m v
    have hc := mem_centralizer_iff.mp hm (v : G) v.property
    have he : (m : G) * (v : G) * (m : G)⁻¹ = v :=
      mul_inv_eq_iff_eq_mul.mpr hc.symm
    have hv : d.coordinates.symm (Multiplicative.ofAdd
        ((d.action m).val (Multiplicative.toAdd (d.coordinates v)))) = v :=
      Subtype.ext (hh.trans he)
    have hh' := congrArg d.coordinates hv
    simpa [v] using hh'

theorem actionImage_commutative_commutator
    (d : OrthogonalFourBinary.NaturalAction V M) (Y : Subgroup G) (hYM : Y ≤ M)
    [IsMulCommutative (actionImage d Y)] : ⁅Y,Y⁆ ≤ centralizer (V : Set G) := by
  have he : ⁅actionImage d Y, actionImage d Y⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hker : ⁅Y.subgroupOf M,Y.subgroupOf M⁆ ≤ d.action.ker := by
    apply (Subgroup.map_eq_bot_iff (H := ⁅Y.subgroupOf M,Y.subgroupOf M⁆) (f := d.action)).mp
    rw [map_commutator]
    exact he
  rw [action_ker d] at hker
  have hh := map_mono (f := M.subtype) hker
  rw [map_commutator, map_subgroupOf_eq_of_le hYM] at hh
  exact hh.trans (map_comap_le _ _)

theorem lineT_normalizer_of_action_bound
    (d : OrthogonalFourBinary.NaturalAction V M) (T E : Subgroup G)
    (hTM : T ≤ M) (hkerT : M ⊓ centralizer (V : Set G) ≤ T)
    (hN : normalizer (actionImage d (lineT T E) : Set _) ≤ actionImage d T) :
    M ⊓ normalizer (lineT T E : Set G) ≤ T := by
  have hker : d.action.ker ≤ T.subgroupOf M := by
    rw [action_ker d]
    exact fun m hm => hkerT ⟨m.property,hm⟩
  have hpre : (actionImage d T).comap d.action = T.subgroupOf M := by
    rw [actionImage, comap_map_eq, sup_of_le_left hker]
  intro x hx
  let m : M := ⟨x,hx.1⟩
  have hm : m ∈ normalizer ((lineT T E).subgroupOf M : Set M) := by
    rw [← subgroupOf_normalizer_eq (show lineT T E ≤ M from inf_le_left.trans hTM)]
    exact hx.2
  have hi : d.action m ∈ normalizer (actionImage d (lineT T E) : Set _) :=
    ((lineT T E).subgroupOf M).le_normalizer_map d.action (mem_map_of_mem _ hm)
  have ht : m ∈ (actionImage d T).comap d.action := hN hi
  rw [hpre] at ht
  exact ht
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
