module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Center
public import Theory.Frattini.PGroup

/-!
# Lifting displacement through the actual center

In the third C.1.34 case, the nontrivial abelian quotient Q/Z(Q) forces Q to
be nonabelian. Its derived subgroup is L-invariant and lies in Z(Q); natural
irreducibility makes it all of Z(Q). Thus Z(Q) ≤ Φ(Q), and a subgroup which
surjects onto Q/Z(Q) already generates Q. Both layers use one common marking.

Source: Aschbacher–Smith, C.1.34(3), printed pp.136–137, as used in the
k = 3 paragraph of 15.3.23, printed p.1129 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W" => Fin 3 → ZMod 2

variable [Finite G]

omit [Finite G] in
/-- Nonabelianness and irreducibility of the genuine center give [Q,Q] = Z(Q). -/
theorem core_derived_eq_center (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel L (commutatorCore L) (coreCenter L) e (DualCopies (ZMod 2) 2)) :
    ⁅commutatorCore L, commutatorCore L⁆ = coreCenter L := by
  let Q := commutatorCore L
  let Z := coreCenter L
  let _ := n.lower_normal
  have hZQ : Z ≤ Q := map_subtype_le _
  let _ : IsMulCommutative (Q ⧸ Z.subgroupOf Q) := IsMulCommutative.of_comm fun a b => by
    apply n.quotientIso.injective
    simp only [map_mul, mul_comm]
  have hDZ : ⁅Q, Q⁆ ≤ Z := by
    have h := map_mono (f := Q.subtype)
      ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Z.subgroupOf Q)).mp
        (inferInstance : IsMulCommutative (Q ⧸ Z.subgroupOf Q)))
    rwa [Q.map_subtype_commutator, map_subgroupOf_eq_of_le hZQ] at h
  have hn : L ≤ normalizer ((⁅Q, Q⁆ : Subgroup G) : Set G) := by
    rw [← Q.map_subtype_commutator]
    exact (normalizer_commutator_ge_right (L.pCoreIn 2) L).trans
      (normalizer_le_normalizer_characteristic_image Q (_root_.commutator Q))
  rcases natural_invariant_eq_bot_or_eq m hDZ hn with hb | hz
  · have hcomm : IsMulCommutative Q := commutator_self_eq_bot_iff.mp hb
    have hZ : Z = Q := by
      change (center Q).map Q.subtype = Q
      rw [center_eq_top_iff.mpr hcomm, ← MonoidHom.range_eq_map, range_subtype]
    let _ : Nontrivial (Q ⧸ Z.subgroupOf Q) := n.quotientIso.toEquiv.nontrivial
    obtain ⟨q, hq⟩ := exists_ne (1 : Q ⧸ Z.subgroupOf Q)
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) q
    exact (hq ((QuotientGroup.eq_one_iff q).mpr (by change (q : G) ∈ Z; rw [hZ]; exact q.property))).elim
  · exact hz

/-- The whole natural center lies in the intrinsic Frattini subgroup of Q. -/
theorem coreCenter_le_frattini (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel L (commutatorCore L) (coreCenter L) e (DualCopies (ZMod 2) 2)) :
    coreCenter L ≤ (frattini (commutatorCore L)).map (commutatorCore L).subtype := by
  let _ : Fact (IsPGroup 2 (commutatorCore L)) :=
    ⟨(L.isPGroup_pCoreIn 2).to_le (commutatorCore_le L)⟩
  rw [← core_derived_eq_center L m n, ← (commutatorCore L).map_subtype_commutator]
  exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

/-- Displacement onto the actual central quotient already generates Q. -/
theorem eq_core_of_sup_center (L H : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel L (commutatorCore L) (coreCenter L) e (DualCopies (ZMod 2) 2))
    (hH : H ≤ commutatorCore L) (hsup : H ⊔ coreCenter L = commutatorCore L) :
    H = commutatorCore L := by
  let Q := commutatorCore L
  have hZ : coreCenter L ≤ (frattini Q).map Q.subtype := coreCenter_le_frattini L m n
  have ht : H.subgroupOf Q ⊔ frattini Q = ⊤ := by
    apply map_injective Q.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hH, ← MonoidHom.range_eq_map, range_subtype]
    exact le_antisymm (sup_le hH (map_subtype_le _))
      (hsup.ge.trans (sup_le_sup_left hZ H))
  have hf := frattini_nongenerating ht
  have hh := congrArg (map Q.subtype) hf
  rwa [map_subgroupOf_eq_of_le hH, ← MonoidHom.range_eq_map, range_subtype] at hh

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
end
