module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.LocalFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.Component
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Recognizing the alternating-five block in the S₆ branch

The marked cubic action moves a plane of order four. The whole two-core of
L centralizes the marked v, hence normalizes the actual residual Lᵥ. Relative
normality puts [O₂(L),Lᵥ] inside O₂(Lᵥ). An actual A₄ isomorphism and the
cubic residual quotient make that core have order four, so the moved plane
fills it and [O₂(L),Lᵥ] ≤ V. The cubic image normally generates the simple
A₅ action; two-perfection then gives normal generation of L itself. Thus
[O₂(L),L] ≤ V. Irreducibility and nontriviality of the marked natural action
give [V,L] = V, proving U(L) = V.

The fixed subgroup is trivial. Transport through the marking and the
odd-degree core-to-natural equivalence constructs the literal quotient
U(L)/C_U(L), with the prescribed conjugation formula, and proves every
short-group clause. No equality O₂(L) = V is used: the permitted central
extension L/V remains distinct from the action quotient L/O₂(L).

The source-facing assembly retains the actual component K and the S₆
normalizer-action isomorphism. `ResidualA4.Component` proves
O^{3′}(Gᵥ) = K and Lᵥ ≤ K from these hypotheses and the earlier universal
conjugacy alternative. Thus the A.3.18 application is derived with its
literal ambient group; it is not an assumed commutator or block conclusion.
The A₄ isomorphism is an independent input. The parent S₆ task must supply
it and `EarlierConjugates` before using the final consumer application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125; module conventions pp.876–877 and 926; the S₆ paragraph
in the proof of 13.6.6, printed p.927; A.3.18, pp.51–52.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix.BlockRecognition
open A5Module ChapterC BinaryPermutation
open BinaryPermutation.FiveCentralizerGeometry
universe u
variable {G : Type u} [Group G] {L V : Subgroup G}

abbrev marked (L V : Subgroup G) : Subgroup L := V.subgroupOf L

noncomputable def naturalToMarked (s : Marking L V) (hVL : V ≤ L) :
    Multiplicative (natural (Fin 5)) ≃* marked L V :=
  ((coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative.symm.trans
    (markingEquiv s)).trans (subgroupOfEquivOfLe hVL).symm

noncomputable def naturalMap (s : Marking L V) (hVL : V ≤ L) :
    Multiplicative (natural (Fin 5)) →* L :=
  (marked L V).subtype.comp (naturalToMarked s hVL).toMonoidHom

theorem naturalMap_injective (s : Marking L V) (hVL : V ≤ L) :
    Function.Injective (naturalMap s hVL) :=
  (marked L V).subtype_injective.comp (naturalToMarked s hVL).injective

theorem naturalMap_range (s : Marking L V) (hVL : V ≤ L) :
    (naturalMap s hVL).range = marked L V := by
  rw [naturalMap, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
    (naturalToMarked s hVL).surjective, ← MonoidHom.range_eq_map, range_subtype]

theorem naturalMap_action (s : Marking L V) (hVL : V ≤ L)
    (l : L) (x : Multiplicative (natural (Fin 5))) :
    naturalMap s hVL (naturalMulAction (Fin 5) (s.action l).val x) =
      l * naturalMap s hVL x * l⁻¹ := by
  apply Subtype.ext
  let e := coreEquivNatural (Fin 5) (by decide)
  have he : e.symm (naturalRepresentation (Fin 5) (s.action l).val x.toAdd) =
      act (s.action l) (e.symm x.toAdd) := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa only [e, LinearEquiv.apply_symm_apply] using
      (coreEquivNatural_equivariant (Fin 5) (by decide) (s.action l).val (e.symm x.toAdd)).symm
  change s.map (Multiplicative.ofAdd (e.symm
    (naturalRepresentation (Fin 5) (s.action l).val x.toAdd))) =
      (l : G) * s.map (Multiplicative.ofAdd (e.symm x.toAdd)) * (l : G)⁻¹
  rw [he]
  exact (s.equivariant l (e.symm x.toAdd)).symm

theorem marked_normal (s : Marking L V) (hVL : V ≤ L) : (marked L V).Normal := by
  constructor
  intro x hx l
  obtain ⟨v, rfl⟩ := (naturalMap_range s hVL).symm ▸ hx
  rw [← naturalMap_action s hVL]
  exact naturalMap_range s hVL ▸ ⟨_, rfl⟩

theorem marked_dichotomy (s : Marking L V) (hVL : V ≤ L)
    (N : Subgroup L) [N.Normal] (hle : N ≤ marked L V) :
    N = ⊥ ∨ N = marked L V := by
  let i := naturalMap s hVL
  let W := (AddSubgroup.toZModSubmodule 2) ((AddSubgroup.toSubgroup).symm (N.comap i))
  let P : Subrepresentation (alternatingNaturalRepresentation (Ω := Fin 5)) :=
    ⟨W, by
      intro g x hx
      obtain ⟨l, rfl⟩ := s.onto g
      change i (naturalMulAction (Fin 5) (s.action l).val (Multiplicative.ofAdd x)) ∈ N
      rw [naturalMap_action]
      exact (inferInstance : N.Normal).conj_mem _ hx _⟩
  let : Representation.IsIrreducible (alternatingNaturalRepresentation (Ω := Fin 5)) :=
    alternatingNatural_isIrreducible (by decide)
  rcases IsSimpleOrder.eq_bot_or_eq_top P with hp | hp
  · left
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨v, rfl⟩ := (naturalMap_range s hVL).symm ▸ hle hx
    have hv : v.toAdd ∈ P.toSubmodule := hx
    rw [hp] at hv
    have hv1 : v = 1 := congrArg Multiplicative.ofAdd hv
    change i v = 1
    rw [hv1, map_one]
  · right
    apply le_antisymm hle
    intro x hx
    obtain ⟨v, rfl⟩ := (naturalMap_range s hVL).symm ▸ hx
    have hv : v.toAdd ∈ P.toSubmodule := by rw [hp]; trivial
    exact hv

theorem marked_not_central (s : Marking L V) (hVL : V ≤ L) :
    ¬ marked L V ≤ center L := by
  intro h
  have hall (g : alternatingGroup (Fin 5)) : g = 1 := by
    obtain ⟨l, rfl⟩ := s.onto g
    apply Subtype.ext
    apply naturalMulAction_injective_of_odd (Ω := Fin 5) (by decide)
    rw [Subgroup.coe_one, map_one]
    ext v : 1
    apply naturalMap_injective s hVL
    rw [naturalMap_action]
    have hv : naturalMap s hVL v ∈ marked L V :=
      naturalMap_range s hVL ▸ (show naturalMap s hVL v ∈ (naturalMap s hVL).range from ⟨v, rfl⟩)
    have hc := mem_center_iff.mp (h hv) l
    change l * naturalMap s hVL v * l⁻¹ = naturalMap s hVL v
    rw [hc, mul_inv_cancel_right]
  have hc := hall cubic
  have hn : cubic ≠ 1 := by decide +kernel
  exact hn hc

theorem marked_inf_center (s : Marking L V) (hVL : V ≤ L) :
    marked L V ⊓ center L = ⊥ := by
  let := marked_normal s hVL
  rcases marked_dichotomy s hVL (marked L V ⊓ center L) inf_le_left with h | h
  · exact h
  · exact (marked_not_central s hVL (h ▸ inf_le_right)).elim

theorem marked_commutator (s : Marking L V) (hVL : V ≤ L) :
    ⁅marked L V, (⊤ : Subgroup L)⁆ = marked L V := by
  let := marked_normal s hVL
  rcases marked_dichotomy s hVL ⁅marked L V, (⊤ : Subgroup L)⁆
    (commutator_le_left _ _) with h | h
  · exact (marked_not_central s hVL
      (commutator_top_right_eq_bot_iff_le_center.mp h)).elim
  · exact h

noncomputable def actionQuotient (s : Marking L V) (m : ModuleData s) :
    (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq m.action_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective s.action s.onto)

@[simp] theorem actionQuotient_mk (s : Marking L V) (m : ModuleData s) (l : L) :
    actionQuotient s m (QuotientGroup.mk' (pCore 2 L) l) = s.action l := rfl


theorem V_le_L (s : Marking L V) (m : ModuleData s) : V ≤ L :=
  m.V_le_core.trans (map_subtype_le _)

private theorem marked_le_core (s : Marking L V) (m : ModuleData s) :
    marked L V ≤ pCore 2 L := by
  intro x hx
  obtain ⟨y, hy, he⟩ := m.V_le_core hx
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

/-- A bound for the whole core commutator identifies the actual short-group layer. -/
theorem blockU_eq_marked (s : Marking L V) (m : ModuleData s)
    (hbound : blockU L ≤ marked L V) : blockU L = marked L V := by
  apply le_antisymm hbound
  rw [← marked_commutator s (V_le_L s m)]
  exact commutator_mono (marked_le_core s m) le_rfl

/-- The coordinates on U are the given marking, after its odd-degree core identification. -/
noncomputable def blockEquiv (s : Marking L V) (m : ModuleData s)
    (hbound : blockU L ≤ marked L V) : blockU L ≃* Multiplicative (natural (Fin 5)) :=
  (MulEquiv.subgroupCongr (blockU_eq_marked s m hbound)).trans
    (naturalToMarked s (V_le_L s m)).symm

private theorem blockEquiv_inverse (s : Marking L V) (m : ModuleData s)
    (hbound : blockU L ≤ marked L V) (x : blockU L) :
    naturalMap s (V_le_L s m) (blockEquiv s m hbound x) = (x : L) := by
  change ((naturalToMarked s (V_le_L s m))
    ((naturalToMarked s (V_le_L s m)).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem fixed_eq_bot (s : Marking L V) (m : ModuleData s)
    (hbound : blockU L ≤ marked L V) : blockFixed L = ⊥ := by
  apply Subgroup.map_injective (blockU L).subtype_injective
  rw [blockFixed_map, blockU_eq_marked s m hbound,
    marked_inf_center s (V_le_L s m), Subgroup.map_bot]

/-- The actual quotient U/C_U(L), including the conjugation formula. -/
noncomputable def blockModel (s : Marking L V) (m : ModuleData s)
    (hbound : blockU L ≤ marked L V) :
    BlockModuleModel L ((naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype) where
  quotientIso := actionQuotient s m
  moduleIso := ((QuotientGroup.quotientMulEquivOfEq (fixed_eq_bot s m hbound)).trans
    QuotientGroup.quotientBot).trans (blockEquiv s m hbound)
  intertwining l x := by
    change blockEquiv s m hbound (blockConjugate L l x) =
      naturalMulAction (Fin 5) (s.action l).val (blockEquiv s m hbound x)
    apply naturalMap_injective s (V_le_L s m)
    rw [blockEquiv_inverse, naturalMap_action, blockEquiv_inverse]
    rfl

/-- All five short-group clauses and the natural alternating module follow from commutator control. -/
theorem alternatingBlock_of_commutator_bound [Finite G] (s : Marking L V) (m : ModuleData s)
    (hbound : blockU L ≤ marked L V) : IsAlternatingBlock L 5 := by
  have hVL := V_le_L s m
  have hU := blockU_eq_marked s m hbound
  have hi : blockU L ⊓ center L = ⊥ := by rw [hU, marked_inf_center s hVL]
  have hirr : BlockModuleIrreducible L := by
    constructor
    · rw [hi, hU, bot_lt_iff_ne_bot]
      intro h
      exact marked_not_central s hVL (by rw [h]; exact bot_le)
    · intro N hN _ hle
      let := hN
      rw [hi, hU]
      exact marked_dichotomy s hVL N (hU ▸ hle)
  let : IsElementaryAbelian 2 (Multiplicative (natural (Fin 5))) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  have helem : IsElementaryAbelian 2 (blockU L) :=
    IsElementaryAbelian.of_surjective (blockEquiv s m hbound).symm.toMonoidHom
      (blockEquiv s m hbound).symm.surjective
  have hcentral : blockU L ≤ centralizer (pCore 2 L : Set L) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp (m.V_central_core (hbound hx)) y ⟨y, hy, rfl⟩
  have hquasi : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let := hquasi
  refine ⟨by decide, ⟨inferInstance, m.twoPerfect, m.fitting, helem, hcentral,
    Or.inl (IsQuasisimple.of_mulEquiv (actionQuotient s m).symm), hirr⟩, ?_⟩
  exact ⟨(naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype,
    ⟨blockModel s m hbound⟩, fun _ _ => rfl⟩

variable [Finite G]

omit [Finite G] in
private theorem residual_le_L (s : Marking L V) : Lv L (markedV s) ≤ L :=
  (map_subtype_le _).trans inf_le_left

omit [Finite G] in
private theorem core_le_local (s : Marking L V) (m : ModuleData s) :
    L.pCoreIn 2 ≤ L ⊓ Gv (markedV s) := by
  refine le_inf (pCoreIn_le 2 L) ?_
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact mem_centralizer_iff.mp (m.V_central_core (s.range_eq.le ⟨_, rfl⟩)) x hx

omit [Finite G] in
private theorem residual_normalized_by_core (s : Marking L V) (m : ModuleData s) :
    L.pCoreIn 2 ≤ normalizer (Lv L (markedV s) : Set G) :=
  (core_le_local s m).trans (le_normalizer_embedded_pResidual 2 _)

omit [Finite G] in
private theorem residual_normalizes_core (s : Marking L V) :
    Lv L (markedV s) ≤ normalizer (L.pCoreIn 2 : Set G) :=
  (residual_le_L s).trans (L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))

omit [Finite G] in
/-- Relative normality bounds the commutator by the two-core of the actual residual. -/
theorem core_residual_commutator_le (s : Marking L V) (m : ModuleData s) :
    ⁅L.pCoreIn 2, Lv L (markedV s)⁆ ≤ (Lv L (markedV s)).pCoreIn 2 := by
  let R := Lv L (markedV s)
  have hR := residual_le_L s
  let i : R →* L := inclusion hR
  let Q := (pCore 2 L).comap i
  have hQ : Q ≤ pCore 2 R := le_sSup ⟨inferInstance,
    pCore_isPGroup.comap_of_injective i (inclusion_injective hR)⟩
  have hleft : ⁅L.pCoreIn 2, R⁆ ≤ L.pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp (residual_normalizes_core s)
  have hright : ⁅L.pCoreIn 2, R⁆ ≤ R :=
    le_normalizer_iff_commutator_le_right.mp (residual_normalized_by_core s m)
  intro x hx
  have hxR := hright hx
  have hxQ : (⟨x, hxR⟩ : R) ∈ Q := by
    obtain ⟨y, hy, hyx⟩ := hleft hx
    change (⟨x, hR hxR⟩ : L) ∈ pCore 2 L
    have he : (⟨x, hR hxR⟩ : L) = y := Subtype.ext hyx.symm
    exact he ▸ hy
  exact ⟨⟨x, hxR⟩, hQ hxQ, rfl⟩

private def cubicSeeds : Fin 4 → Space := ![0, z, act cubic z, z + act cubic z]

private theorem cubicDifferences_injective :
    Function.Injective (fun i => act cubic (cubicSeeds i) - cubicSeeds i) := by
  decide +kernel

private theorem cubicDifference_mem (s : Marking L V) (m : ModuleData s) (x : Space) :
    s.map (Multiplicative.ofAdd (act cubic x - x)) ∈
      ⁅L.pCoreIn 2, Lv L (markedV s)⁆ := by
  obtain ⟨c, hc, hact⟩ := exists_residual_cubic s
  have hcR : (c : G) ∈ Lv L (markedV s) := ⟨c, hc, rfl⟩
  have hxQ : s.map (Multiplicative.ofAdd x) ∈ L.pCoreIn 2 :=
    m.V_le_core (s.range_eq.le ⟨_, rfl⟩)
  have hh := commutator_mem_commutator hcR hxQ
  rw [commutator_comm] at hh
  have he : s.map (Multiplicative.ofAdd (act cubic x - x)) =
      (c : G) * s.map (Multiplicative.ofAdd x) * (c : G)⁻¹ *
        (s.map (Multiplicative.ofAdd x))⁻¹ := by
    rw [← hact]
    rw [show Multiplicative.ofAdd (act (s.action (inclusion inf_le_left c)) x - x) =
      Multiplicative.ofAdd (act (s.action (inclusion inf_le_left c)) x) *
        (Multiplicative.ofAdd x)⁻¹ from by rw [ofAdd_sub, div_eq_mul_inv], map_mul, map_inv]
    rw [← s.equivariant]
    rfl
  exact he.symm ▸ hh

/-- The marked cubic contributes a plane of order four inside the residual two-core. -/
theorem residual_core_le_marked_of_A4 (s : Marking L V) (m : ModuleData s)
    (e : Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :
    (Lv L (markedV s)).pCoreIn 2 ≤ V := by
  let R := Lv L (markedV s)
  let Q := R.pCoreIn 2
  have hcR : Nat.card R = 12 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcQ : Nat.card Q = 4 := by
    have hc := (pCore 2 R).index_mul_card
    rw [index_eq_card, m.residual_quotient_card, hcR] at hc
    have he := Nat.card_congr ((pCore 2 R).equivMapOfInjective R.subtype R.subtype_injective).toEquiv
    change Nat.card (pCore 2 R) = Nat.card Q at he
    omega
  let f : Fin 4 → ↥(Q ⊓ V) := fun i =>
    ⟨s.map (Multiplicative.ofAdd (act cubic (cubicSeeds i) - cubicSeeds i)),
      core_residual_commutator_le s m (cubicDifference_mem s m _), s.range_eq.le ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    apply cubicDifferences_injective
    exact congrArg Multiplicative.toAdd (s.injective (congrArg Subtype.val h))
  have hcard : 4 ≤ Nat.card ↥(Q ⊓ V) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have heq : Q ⊓ V = Q := eq_of_le_of_card_ge inf_le_left (by omega)
  change Q ≤ V
  rw [← heq]
  exact inf_le_right

/-- The A₄ residual controls the action of the whole two-core on that residual. -/
theorem residual_commutator_bound (s : Marking L V) (m : ModuleData s)
    (e : Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :
    ⁅L.pCoreIn 2, Lv L (markedV s)⁆ ≤ V :=
  (core_residual_commutator_le s m).trans (residual_core_le_marked_of_A4 s m e)

/-- The actual local residual normally generates L: its cubic image is nontrivial
in A₅, and two-perfection removes the remaining two-group quotient. -/
theorem residual_normalClosure (s : Marking L V) (m : ModuleData s) :
    normalClosure ((Lv L (markedV s)).subgroupOf L : Set L) = ⊤ := by
  let R := (Lv L (markedV s)).subgroupOf L
  let N := normalClosure (R : Set L)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : (N.map s.action).Normal := (inferInstance : N.Normal).map s.action s.onto
  have ht : N.map s.action = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hz | ht
    · obtain ⟨c, hc, ha⟩ := exists_residual_cubic s
      have hcR : inclusion (show L ⊓ Gv (markedV s) ≤ L from inf_le_left) c ∈ R :=
        ⟨c, hc, rfl⟩
      have hcN := (show R ≤ N from le_normalClosure) hcR
      have hh : cubic ∈ N.map s.action := ha ▸ mem_map_of_mem s.action hcN
      rw [hz, mem_bot] at hh
      exact (show cubic ≠ 1 by decide +kernel) hh |>.elim
    · exact ht
  have hsup : N ⊔ pCore 2 L = ⊤ := by
    have hh := congrArg (fun H : Subgroup (alternatingGroup (Fin 5)) => H.comap s.action) ht
    simpa only [comap_map_eq, comap_top, m.action_kernel] using hh
  exact m.twoPerfect N inferInstance (isPGroup_quotient_of_sup_eq_top N (pCore 2 L)
    pCore_isPGroup hsup)

/-- Transfer the residual commutator bound through its actual normal generation. -/
theorem core_commutator_bound (s : Marking L V) (m : ModuleData s)
    (e : Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :
    blockU L ≤ marked L V := by
  let := marked_normal s (V_le_L s m)
  have hlocal : ⁅pCore 2 L, (Lv L (markedV s)).subgroupOf L⁆ ≤ marked L V := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le (residual_le_L s),
      show (marked L V).map L.subtype = V from map_subgroupOf_eq_of_le (V_le_L s m)]
    exact residual_commutator_bound s m e
  have h := commutator_normalClosure_le_of_normal (pCore 2 L)
    ((Lv L (markedV s)).subgroupOf L) (marked L V) hlocal
  rwa [residual_normalClosure s m] at h


/-- The literal A.3.18 residual identification and the block conclusion in the
same S₆ context. The A₄ isomorphism remains the independent extraction input. -/
theorem source_recognition {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}
    (d : Setup κ T s) (m : ModuleData s) (earlier : EarlierConjugates κ)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e₆ : XStar K ≃* Equiv.Perm (Fin 6))
    (e₄ : Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :
    (primeToResidual 3 (Gv (markedV s)) = K ∧ residual s ≤ K) ∧
      IsAlternatingBlock L 5 := by
  refine ⟨⟨primeToResidual_eq_component d earlier hodd K hK e₆,
    residual_le_component d m earlier hodd K hK e₆⟩, ?_⟩
  exact alternatingBlock_of_commutator_bound s m (core_commutator_bound s m e₄)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix.BlockRecognition

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open A5Module ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}

/-- Supply the actual block argument to `SourceData.contradiction_of_block`.
The parent supplies the independent A₄ extraction and the earlier universal
conjugacy theorem; no block or desired core equality is a premise. -/
theorem SourceData.isAlternatingBlock_of_residualA4
    {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}
    (d : Setup κ T s) {M : Subgroup G} (h : SourceData d M)
    (earlier : EarlierConjugates κ) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e₆ : XStar K ≃* Equiv.Perm (Fin 6))
    (e₄ : Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :
    IsAlternatingBlock L 5 :=
  (BlockRecognition.source_recognition d h.moduleData earlier hodd K hK e₆ e₄).2

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
