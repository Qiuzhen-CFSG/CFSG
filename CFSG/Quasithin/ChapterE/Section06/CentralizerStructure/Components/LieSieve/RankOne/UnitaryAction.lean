module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.ActionReduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Inputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Center
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Rigidity
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.UnitaryThree.SylowOrders
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The PSU₃ fixed-field Borel action

Write q = 2ⁿ for the fixed-field order. The genuine model equivalence stored
in `IsPSU L 3 q` retains a matrix field of order q² and conjugation x ↦ x^q.
The intrinsic Sylow-center order theorem uses that equivalence and Hermitian
form transport; the center is not replaced by an unrelated additive group.

Semilinear coverage and the intrinsic fixer theorem prove that an involutory
automorphism fixing the Borel pointwise is trivial. Applying this to conjugation
by elements of V gives C_V(B) = C_V(L). The displacement [V,B] is an invariant subgroup of the
embedded Sylow center. Escape from M makes it nonzero, so the proved
irreducible center action makes it the whole center, of order q.
Finally the coprime splitting identifies the actual conjugation kernels on V
and on [V,B]. The first isomorphism theorem then transports the cyclic action
image of order q−1 from the model center to V.

`calculation_of_isPSU` discharges both intrinsic inputs using the actual model.
No `BorelAlternative` hypothesis or dependent `modelWitness` theorem is used.
The supplied Borel equality remains the independent placement input, owned by
the rank-one source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247–248, using the splitting argument on printed p.246.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction

variable {G H : Type*} [Group G] [Group H]

variable [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

/-- Pointwise Borel rigidity identifies C_V(B) with C_V(L). The automorphism
is the literal conjugation action of v on L, and has square one because V is
elementary abelian. -/
theorem fixed_of_rigid
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L) (hB : sylowBorel S = L ⊓ M) (hr : BorelRigid S) :
    V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
      V ⊓ centralizer (L : Set G) := by
  let _ := h.elementary
  have hVL := component_normalized_by_V h hU hL
  let φ : V →* MulAut L := L.normalizerMonoidHom.comp (inclusion hVL)
  apply le_antisymm
  · rintro v ⟨hv, hc⟩
    refine ⟨hv, ?_⟩
    have hp : (⟨v, hv⟩ : V) ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian v hv
    have he : φ ⟨v, hv⟩ = 1 := hr _ (by rw [← map_pow, hp, map_one]) (by
      intro b hb
      apply Subtype.ext
      change v * (b : G) * v⁻¹ = (b : G)
      have hb' : (b : G) ∈ L ⊓ M := hB ▸ mem_map_of_mem L.subtype hb
      rw [← mem_centralizer_iff.mp hc b hb', mul_inv_cancel_right])
    apply mem_centralizer_iff.mpr
    intro l hl
    have he' := congrArg (fun a : MulAut L => ((a ⟨l, hl⟩ : L) : G)) he
    change v * l * v⁻¹ = l at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · exact inf_le_inf_left V (centralizer_le inf_le_left)

/-- The local displacement is the whole embedded Sylow center. Its known
containment and invariance allow intrinsic irreducibility to apply; the zero
case contradicts component escape from M using pointwise Borel rigidity. -/
theorem displacement_eq_center_of_irreducible
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : sylowBorel S = L ⊓ M) (hr : BorelRigid S)
    (hi : ∀ A : Subgroup L, A ≤ sylowCenter S →
      normalizer (S : Set L) ≤ normalizer (A : Set L) → A = ⊥ ∨ A = sylowCenter S) :
    ⁅V, L ⊓ M⁆ = (sylowCenter S).map L.subtype := by
  let W := ⁅V, L ⊓ M⁆
  have hWL : W ≤ L := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (component_normalized_by_V h hU hL))
  have hmap : (W.subgroupOf L).map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hWZ : W ≤ (sylowCenter S).map L.subtype := by
    have he : (sylowCenter S).map L.subtype =
        (center ↥(L ⊓ sylowCentralizer (T : Subgroup G) V)).map
          (L ⊓ sylowCentralizer (T : Subgroup G) V).subtype := by
      rw [sylowCenter, map_embeddedCenter _ _ L.subtype_injective, hS]
    rw [he]
    exact BorelActions.displacement_le_center h hU hL (component_normalized_by_V h hU hL) rfl
  have hZW : W.subgroupOf L ≤ sylowCenter S := by
    intro w hw
    exact (mem_map_iff_mem L.subtype_injective).mp (hWZ hw)
  have hNW : normalizer (S : Set L) ≤ normalizer (W.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro b hb w hw
    have hb' : (b : G) ∈ L ⊓ M := hB ▸ mem_map_of_mem L.subtype hb
    exact (mem_normalizer_iff.mp
      ((normalizer_commutator_ge_right V (L ⊓ M)) hb') w).mp hw
  rcases hi _ hZW hNW with hzero | he
  · have hwzero : W = ⊥ := by rw [← hmap, hzero, Subgroup.map_bot]
    have hfix := fixed_of_rigid h hU hL S hB hr
    have hVC : V ≤ centralizer (L : Set G) := by
      apply (show V ≤ V ⊓ centralizer (L : Set G) from ?_).trans inf_le_right
      rw [← hfix]
      exact le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp hwzero)
    exact False.elim (component_not_le h earlier hU hL
      ((le_centralizer_iff.mp hVC).trans h.centralizer_le))
  · change W = _
    rw [← hmap, he]

/-- Conditional PSU₃ action assembly. `calculation_of_isPSU` below supplies
both intrinsic model premises. Borel placement is the independent equality hB. -/
theorem calculation_of_intrinsic
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : sylowBorel S = L ⊓ M) (hr : BorelRigid S) (ha : CenterAction S n) :
    ActionCalculation M V L n := by
  have hfixed := fixed_of_rigid h hU hL S hB hr
  have hW := displacement_eq_center_of_irreducible h earlier hU hL S hS hB hr ha.irreducible
  have hBN := component_intersection_normalizes h hU hL.1
  have hd := intersection_decomposition h hU hL (.unitary hn hm) S hS hB
  refine ⟨hfixed, ?_, ?_⟩
  · rw [hW, card_map_of_injective L.subtype_injective, sylowCenter,
      card_map_of_injective (S : Subgroup L).subtype_injective]
    exact BorelActions.UnitaryThree.sylow_center_card hm (by omega) S
  · let W := ⁅V, L ⊓ M⁆
    have hBNW : L ⊓ M ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
    have hVW : ∀ b : ↥(L ⊓ M), (b : G) ∈ centralizer (V : Set G) ↔
        (b : G) ∈ centralizer (W : Set G) := by
      intro b
      constructor
      · intro hb
        exact centralizer_le (show W ≤ V from le_sup_left.trans hd.1.le) hb
      · intro hb
        apply mem_centralizer_iff.mpr
        intro v hv
        have hjoin : W ⊔ (V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G)) ≤
            centralizer ({(b : G)} : Set G) := by
          apply sup_le
          · intro w hw
            exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hb w hw)
          · intro c hc
            exact mem_centralizer_singleton_iff.mpr
              (mem_centralizer_iff.mp hc.2 b b.property).symm
        exact mem_centralizer_singleton_iff.mp (hjoin (hd.1.symm ▸ hv))
    obtain ⟨e⟩ := exists_actionEquiv V (L ⊓ M) W (L ⊓ M) hBN hBNW (MulEquiv.refl _) hVW
    obtain ⟨a⟩ := ha.cyclic_image
    have hh : Nonempty (inducedAutomizer W (L ⊓ M) ≃*
        Multiplicative (ZMod (2 ^ n - 1))) := by
      rw [show W = (sylowCenter S).map L.subtype from hW, ← hB]
      obtain ⟨eZ⟩ := exists_actionMapEquiv (sylowCenter S) (normalizer (S : Set L))
        (sylowCenter_normalized S) L.subtype L.subtype_injective
      exact ⟨eZ.symm.trans a⟩
    exact ⟨e.trans (Classical.choice hh)⟩

/-- The PSU₃ action calculation for E.6.8(1): the Borel and component have
the same fixed subgroup in V, the displacement has order 2ⁿ, and the actual
induced Borel action is cyclic of order 2ⁿ−1. Only the independently owned
Borel-placement equality remains explicit; both intrinsic action inputs are
proved from the supplied PSU₃ model equivalence. -/
theorem calculation_of_isPSU
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : sylowBorel S = L ⊓ M) : ActionCalculation M V L n :=
  calculation_of_intrinsic h earlier hU hL hn hm S hS hB
    (borelRigid_of_isPSU hn hm S) (centerAction_of_isPSU hn hm S)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
