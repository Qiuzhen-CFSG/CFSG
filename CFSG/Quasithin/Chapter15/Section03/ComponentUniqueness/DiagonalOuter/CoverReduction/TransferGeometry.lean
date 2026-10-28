module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FusionReduction
public import Theory.GroupTheory.DihedralRotationQuotient
public import Theory.GroupTheory.LocalNormalizerUniqueness


/-!
# Normalizer and transfer deductions for the diagonal-cover branch

Equal central quotients and equal embedded centers identify two nested covers.
Applying this to the larger outside overgroup gives the normalizer equality
once the uniform local reduction has supplied its generating formula.
The normalizer equality and `C_I(L) = V₁` then give both the normalizer action
and its kernel bound required by `field_fusion_of_transfer_geometry`.

An actual split dihedral quotient supplies the two reflections, the half-turn,
the conjugation relation, and the index-two subgroup with cyclic-four quotient.
The final theorem derives TI and field-class fusion from these data and the
remaining representative-centralizer and intrinsic model inputs. It assumes
neither TI nor any fusion or nonfusion conclusion.

The marked cover, Sylow-three normalizer, and the centralizer of the chosen
representative still have to be constructed in the standing rank-two setup.
These are conditional deductions, not a theorem asserting 15.3.38.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1136--1137.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

/-- The local centralizer equality gives the actual action kernel bound. -/
theorem normalizer_action_and_kernel (V I L : Subgroup G)
    (hI : I = normalizer (V : Set G))
    (hL : I ≤ normalizer (L : Set G))
    (hC : I ⊓ centralizer (L : Set G) = V) :
    centralizer (V : Set G) ≤ normalizer (L : Set G) ∧
      centralizer (V : Set G) ⊓ centralizer (L : Set G) ≤ V := by
  have hCI : centralizer (V : Set G) ≤ I :=
    (Subgroup.centralizer_le_normalizer _).trans hI.ge
  exact ⟨hCI.trans hL, (inf_le_inf_right _ hCI).trans hC.le⟩

private theorem eq_of_common_center_and_quotient [Finite G]
    (L L₁ V : Subgroup G) (hLL : L ≤ L₁)
    (hZ : (center L).map L.subtype = V)
    (hZ₁ : (center L₁).map L₁.subtype = V)
    (e : (L ⧸ center L) ≃* (L₁ ⧸ center L₁)) : L = L₁ := by
  have hc : Nat.card (center L) = Nat.card (center L₁) := by
    rw [← card_map_of_injective L.subtype_injective,
      ← card_map_of_injective L₁.subtype_injective, hZ, hZ₁]
  apply eq_of_le_of_card_ge hLL
  rw [(center L).card_eq_card_quotient_mul_card_subgroup,
    (center L₁).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr e.toEquiv, hc]

/-- The overgroup reduction forces equality of the covers and of their
common supplements. Both central quotients here are actual group quotients. -/
theorem normalizer_eq_of_cover_extension [Finite G]
    (I L L₁ V D S : Subgroup G)
    (hLL : L ≤ L₁)
    (hZ : (center L).map L.subtype = V)
    (hZ₁ : (center L₁).map L₁.subtype = V)
    (e : (L ⧸ center L) ≃* (L₁ ⧸ center L₁))
    (hI : I = L ⊔ D ⊔ S)
    (hN : normalizer (V : Set G) = L₁ ⊔ D ⊔ S) :
    L = L₁ ∧ I = normalizer (V : Set G) := by
  have h := eq_of_common_center_and_quotient L L₁ V hLL hZ hZ₁ e
  exact ⟨h, by rw [hI, hN, h]⟩

/-- Construct the transfer data from the dihedral section, and feed the
normalizer geometry and explicit model facts into the published fusion reduction.
The section representatives must be identified with the intended graph and field
actions before applying this in the source theorem. -/
theorem field_fusion_of_split_cover_geometry [Finite G]
    (T : Sylow 2 G) (hG : IsPPerfect 2 G)
    (V I L F J : Subgroup G) [IsKleinFour V]
    (d : DihedralGroup.SplitSection (L.subgroupOf (T : Subgroup G)))
    (hI : I = normalizer (V : Set G))
    (hIL : I ≤ normalizer (L : Set G))
    (hCI : I ⊓ centralizer (L : Set G) = V)
    (v z : G) (hv : v ∈ V) (hv1 : v ≠ 1)
    (hCv : centralizer ({v} : Set G) ≤ I)
    (hJI : J ≤ I)
    (htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : J, (MulAut.conj (m : G)) x = y)
    (hF : IsPPerfect 2 F)
    (hsmall : ¬ 4 ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom))
    (houtside : (d.firstReflection : G) * (d.halfTurn : G) ∉ V)
    (hfixedV : (d.firstReflection : G) * (d.halfTurn : G) ∈ centralizer (V : Set G))
    (hfixedF : (d.firstReflection : G) * (d.halfTurn : G) ∈ centralizer (F : Set G))
    (K : Subgroup (centralizer ({(d.firstReflection : G)} : Set G)))
    (hK : IsComponent (centralizer ({(d.firstReflection : G)} : Set G)) K)
    (hz : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)))
    (hinside : ∀ x : G, x ∈ L → orderOf x = 2 → IsConj x v ∨ IsConj x z)
    (hcoset : ∀ x : G, orderOf x = 2 → x * (d.halfTurn : G)⁻¹ ∈ L →
      IsConj x (d.halfTurn : G)) :
    IsTISubgroup V ∧ IsConj (d.firstReflection : G) (d.halfTurn : G) ∧
      IsConj ((d.firstReflection : G) * (d.halfTurn : G)) (d.halfTurn : G) := by
  obtain ⟨hnorm, hkernel⟩ := normalizer_action_and_kernel V I L hI hIL hCI
  have htransI : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : I, (MulAut.conj (m : G)) x = y := by
    intro x y hx hx1 hy hy1
    obtain ⟨m, hm⟩ := htrans x y hx hx1 hy hy1
    exact ⟨⟨m, hJI m.property⟩, hm⟩
  have hf : (((d.halfTurnInTransfer : T) : G)) = (d.halfTurn : G) :=
    congrArg (fun x : T => (x : G)) d.halfTurnInTransfer_coe
  have hconj : (MulAut.conj (d.secondReflection : G)) (d.firstReflection : G) =
      (d.firstReflection : G) * (((d.halfTurnInTransfer : T) : G)) := by
    rw [hf]
    exact congrArg (fun x : T => (x : G)) d.conjugate_firstReflection
  have h := field_fusion_of_transfer_geometry T hG V I L F hI v z hv hv1 hCv htransI hF
    hnorm hkernel hsmall d.transferSubgroup d.transferSubgroup_index d.cyclicQuotient
    d.cyclicQuotient_kernel d.halfTurnInTransfer d.cyclicQuotient_halfTurn
    d.firstReflection d.firstReflection_order (d.secondReflection : G) hconj
    (hf.symm ▸ houtside) (hf.symm ▸ hfixedV) (hf.symm ▸ hfixedF) K hK hz hinside
    (hf.symm ▸ hcoset)
  simpa only [hf] using h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
