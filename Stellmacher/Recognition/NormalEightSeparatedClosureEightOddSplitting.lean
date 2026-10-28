module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightLocalData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightActionCore
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightOddActionData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightOddGeometry
public import Theory.GroupAction.InvertedOddCentralComplement

/-!
# Assembling the odd-action local splitting

The moving plane and the fixed subgroup of the lifted odd automorphism are
first complementary inside the closure centralizer. Mapping the fixed subgroup
back into the Sylow subgroup gives the concrete `LocalSplitting` interface.
The selected involution is fixed by the actor, whereas the central involution
is moved. The outside involution fixes the complementary factor pointwise.

The order-six action supplies the geometric actor. The abstract fixed-factor
theorem gives its complement, completing the assembly following Janko–Thompson, Math. Z. 113
(1970), Lemma 3.1, printed p.388.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G]

/-- Transport a complementary fixed factor to the concrete local interface.
The complement and pointwise-fixing premises are supplied by the odd-action
splitting argument. -/
public theorem localSplitting_of_oddActionData_fixed_complement
    {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) (z : S) (a : OddActionData d z)
    (hproduct : a.plane.subgroupOf (closureCentralizer d) ⊔
      MulAut.fixedSubgroup a.actor = ⊤)
    (hdisjoint : Disjoint (a.plane.subgroupOf (closureCentralizer d))
      (MulAut.fixedSubgroup a.actor))
    (hfixed : ∀ b ∈ MulAut.fixedSubgroup a.actor,
      (closureCentralizer d).normalizerMonoidHom ⟨a.outside, a.outside_normalizes⟩ b = b) :
    Nonempty (LocalSplitting d z) := by
  let T := closureCentralizer d
  let B := (MulAut.fixedSubgroup a.actor).map T.subtype
  let : IsElementaryAbelian 2 (closureInSylow d) := closureInSylow_elementary d
  have hAT : a.plane ≤ T := a.plane_le.trans (closureInSylow d).le_centralizer
  have hprod : a.plane ⊔ B = T := by
    have hh := congrArg (Subgroup.map T.subtype) hproduct
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAT,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hdis : Disjoint a.plane B := by
    apply disjoint_def.mpr
    intro s hs hB
    obtain ⟨b, hb, rfl⟩ := hB
    have hbA : b ∈ a.plane.subgroupOf T := hs
    have hb1 : b = 1 := disjoint_def.mp hdisjoint hbA hb
    exact congrArg Subtype.val hb1
  have hiB : i ∈ B := by
    exact mem_map_of_mem T.subtype (show (⟨i, a.involution_mem⟩ : T) ∈
      MulAut.fixedSubgroup a.actor from
        (MulAut.mem_fixedSubgroup _ _).mpr a.actor_fixes_involution)
  have hzB : z ∉ B := by
    rintro ⟨b, hb, he⟩
    have he' : b = (⟨z, a.central_mem⟩ : T) := Subtype.ext he
    apply a.actor_moves_central
    rw [← he']
    exact (MulAut.mem_fixedSubgroup _ _).mp hb
  have hxB : a.outside ∈ centralizer (B : Set S) := by
    rintro b ⟨v, hv, rfl⟩
    have hh := congrArg Subtype.val (hfixed v hv)
    change a.outside * (v : S) * a.outside⁻¹ = (v : S) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact ⟨{
    plane := a.plane
    fixed := B
    mover := a.mover
    outside := a.outside
    plane_elementary := a.plane_elementary
    plane_card := a.plane_card
    plane_le := a.plane_le
    plane_normalized := a.plane_normalized
    product := hprod
    disjoint := hdis
    index := a.index
    involution_mem_fixed := hiB
    central_not_mem_fixed := hzB
    mover_outside := a.mover_outside
    outside_mem_conjugate := a.outside_mem_conjugate
    outside_order := a.outside_order
    outside_not_centralizing := a.outside_not_centralizing
    outside_centralizes_fixed := hxB }⟩

variable [Finite G]

/-- The fixed subgroup of the geometric odd actor supplies the local splitting. -/
public theorem localSplitting_of_oddActionData
    {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) (z : S) (a : OddActionData d z) :
    Nonempty (LocalSplitting d z) := by
  let T := closureCentralizer d
  let A := a.plane.subgroupOf T
  let x := T.normalizerMonoidHom ⟨a.outside, a.outside_normalizes⟩
  let : IsElementaryAbelian 2 (closureInSylow d) := closureInSylow_elementary d
  have hAT : a.plane ≤ T := a.plane_le.trans (closureInSylow d).le_centralizer
  have hcentral : A ≤ center T := by
    intro v hv
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact (b.property (v : S) (a.plane_le hv)).symm
  have hxA : ∀ v ∈ A, x v ∈ A := by
    intro v hv
    exact (mem_normalizer_iff.mp
      (a.plane_normalized a.outside_mem_centralizer) (v : S)).mp hv
  have hnontrivial : ∃ v ∈ A, x v ≠ v := by
    obtain ⟨v, hv, hmove⟩ := a.outside_moves_plane
    refine ⟨⟨v, hAT hv⟩, hv, ?_⟩
    intro hh
    apply hmove
    have hh' := congrArg Subtype.val hh
    change a.outside * v * a.outside⁻¹ = v at hh'
    exact mul_inv_eq_iff_eq_mul.mp hh'
  obtain ⟨hproduct, hdisjoint, hfixed⟩ :=
    MulAut.fixed_complement_of_inverted_odd_index_two A a.actor x hcentral
      a.actor_odd a.actor_plane_stable hxA a.actor_inverted a.actor_plane_free
      a.outside_fixed_index hnontrivial
  exact localSplitting_of_oddActionData_fixed_complement d z a hproduct hdisjoint hfixed

/-- The actual order-six action on the closure gives the local direct splitting.
No hypothesis on the cardinality of the fixed factor is required. -/
public theorem localSplitting_of_action_card_six
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (hact6 : Nat.card (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range = 6) :
    Nonempty (LocalSplitting d z) := by
  obtain ⟨a⟩ := nonempty_oddActionData_of_action_card_six
    S W hW z hzW hzC hz i hiW hi hiC hno d hc hact6
  exact localSplitting_of_oddActionData d z a

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
