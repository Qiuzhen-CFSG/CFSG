module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs
public import Theory.GroupTheory.FourOmegaCenterSylowPromotion

/-!
# The global Sylow step in the opposite-involution construction

Apply central omega weak closure to the literal C_T(w) and the original
flag point. The local geometry and local Sylow arrangement remain explicit;
in particular no arbitrary centralizer intersection is declared Sylow.

Source: Aschbacher--Smith, 14.3.22, printed p.999.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- Local Sylow maximality and the printed omega-center calculation promote
the actual C_T(w), with no conjugation or change of the supplied T. -/
theorem global_sylow_of_local_geometry
    (F : InvariantFlag T V 2) (z w : G) (hz : F.Vi 1 = zpowers z)
    (hwT : w ∈ (T : Subgroup G)) (hw : orderOf w = 2)
    (hnf : ¬ IsConj z w) (hprod : IsConj w (w * z))
    (homega : omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({w} : Set G)) =
      closure ({z, w} : Set G))
    (hlocal : ∃ S : Sylow 2 (F.H ⊓ centralizer ({w} : Set G) : Subgroup G),
      (S : Subgroup _).map (F.H ⊓ centralizer ({w} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({w} : Set G)) :
    normalizer ((T : Subgroup G) ⊓ centralizer ({w} : Set G) : Set G) ≤ F.H ∧
    ∃ S : Sylow 2 (centralizer ({w} : Set G)),
      (S : Subgroup _).map (centralizer ({w} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({w} : Set G) := by
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have hH := F.H_eq_centralizer (by decide) z hz
  have hwH : w ∈ F.H := F.invariant 1 hwT
  have hzw : Commute z w := (mem_centralizer_singleton_iff.mp (hH ▸ hwH)).symm
  have hprod' : IsConj w (z * w) := hzw.eq ▸ hprod
  constructor
  · rw [hH]
    exact normalizer_le_centralizer_of_four_omega_center_fusion _ z w hz2 hw hzw
      homega hnf hprod'
  · apply exists_sylow_centralizer_of_four_omega_center _ z w
      T.isPGroup'.to_inf_left inf_le_right hz2 hw hzw homega hnf hprod'
    rw [← hH]
    exact hlocal

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
