module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Obligations
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Overgroup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.Factors
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.SolvableBlockCentralization
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Conditional identification of the escaping characteristic-two component

Apply E.6.7 to the actual group D = ⟨X,Q⟩. If every selected factor
were an A₃ block and centralized X, their join would be a solvable
centralizing supplement. Pulling the set product back to X × L and
projecting its solvable residual shows X ≤ M, a contradiction.
A nonsolvable factor is a C-component of D. The exact A.3.8(3) orbit
input, applied modulo O₂(D) and then lifted, identifies it with a
Q-conjugate of X. Transport preserves the actual quotient and module;
X's original relative subnormality makes X a block of C_G(A).

The A₃-block centralization step is a separate, explicitly unproved
obligation. The conditional theorem below does not complete E.6.23 or
the requested characteristic-two lifting contract until it is discharged.
Neither corank two nor Hypothesis E.6.15 is needed for this reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7 and
E.6.23, printed pp.246 and 254; A.3.3–8, printed pp.41–45.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open InvariantSubspaces.BlockSelection
open CharacteristicTwoBlocks
-- A commuting solvable factor cannot be needed to cover a perfect subgroup.
private theorem perfect_le_of_commuting_solvable_cover {G : Type*} [Group G] [Finite G] (X D L : Subgroup G)
    [Group.IsPerfect X] [Group.IsSolvable L]
    (hc : L ≤ centralizer (X : Set G))
    (hcover : ∀ x ∈ X, ∃ d ∈ D, ∃ l ∈ L, d * l = x) : X ≤ D := by
  let f : X × L →* G := X.subtype.noncommCoprod L.subtype
    (fun x l => (mem_centralizer_iff.mp (hc l.property) x x.property))
  let P := D.comap f
  let a : P →* X := (MonoidHom.fst X L).comp P.subtype
  let b : P →* L := (MonoidHom.snd X L).comp P.subtype
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨d, hd, l, hl, he⟩ := hcover x x.property
    have hh : f (x, (⟨l, hl⟩ : L)⁻¹) = d := by
      change (x : G) * l⁻¹ = d
      rw [← he, mul_inv_cancel_right]
    exact ⟨⟨(x, (⟨l, hl⟩ : L)⁻¹), show f (x, (⟨l, hl⟩ : L)⁻¹) ∈ D from hh.symm ▸ hd⟩, rfl⟩
  have hab : (solvableResidual P).map a = ⊤ := by
    rw [map_solvableResidual_eq a ha, solvableResidual_eq_top]
  have hbb : (solvableResidual P).map b = ⊥ :=
    eq_bot_mono (map_solvableResidual_le b) solvableResidual_eq_bot
  intro x hx
  obtain ⟨y, hy, he⟩ := mem_map.mp (show (⟨x, hx⟩ : X) ∈
    (solvableResidual P).map a from hab.symm ▸ mem_top _)
  have hby : b y = 1 := by
    exact mem_bot.mp (hbb ▸ mem_map_of_mem b hy)
  have hay : (y.val.1 : G) = x := congrArg Subtype.val he
  have hbly : (y.val.2 : G) = 1 := congrArg Subtype.val hby
  have hmem : f y.val ∈ D := y.property
  change (y.val.1 : G) * (y.val.2 : G) ∈ D at hmem
  simpa only [hay, hbly, mul_one] using hmem


private theorem exists_non_three_factor {G : Type*} [Group G] [Finite G]
    {H M Q V A X : Subgroup G} (d : E67Decomposition Q M V A H)
    (hXH : X ≤ H) (hX : (X.subgroupOf H).IsCComponent) (hXM : ¬ X ≤ M)
    (hcentral : ∀ i, ChapterC.IsAlternatingBlock (d.block i) 3 →
      X ≤ centralizer (d.block i : Set G)) :
    ∃ i, ¬ ChapterC.IsAlternatingBlock (d.block i) 3 := by
  classical
  by_contra! hall
  let L := ⨆ i, d.block i
  have hc : L ≤ centralizer (X : Set G) :=
    iSup_le fun i => le_centralizer_iff.mp (hcentral i (hall i))
  have hlR : L ≤ (solvableRadical H).map H.subtype := by
    apply iSup_le
    intro i
    let B := (d.block i).subgroupOf H
    let : Group.IsSolvable (d.block i) := three_solvable (hall i)
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (d.le i)).toMonoidHom)
      (subgroupOfEquivOfLe (d.le i)).injective
    have hbR : B ≤ solvableRadical H := by
      have hh := map_solvableRadical_subtype_le_of_isSubnormal (d.subnormal i)
      have ht : solvableRadical B = ⊤ := top_unique
        (le_solvableRadical ⊤ inferInstance inferInstance)
      rw [ht, ← MonoidHom.range_eq_map, range_subtype] at hh
      exact hh
    have hm := map_mono (f := H.subtype) hbR
    rwa [map_subgroupOf_eq_of_le (d.le i)] at hm
  let : Group.IsSolvable ((solvableRadical H).map H.subtype) :=
    Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective (solvableRadical H))
  let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective (inclusion_injective hlR)
  let : Group.IsPerfect (X.subgroupOf H) := hX.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).toMonoidHom) (subgroupOfEquivOfLe hXH).surjective
  apply hXM
  apply perfect_le_of_commuting_solvable_cover X M L hc
  intro x hx
  have hp : x ∈ ((H ⊓ M : Subgroup G) : Set G) * (L : Set G) := by
    rw [← d.product]
    exact hXH hx
  obtain ⟨m, hm, l, hl, he⟩ := hp
  exact ⟨m, hm.2, l, hl, he⟩

/-- The selected factor is an actual Q-conjugate of the given C-component.
Only the explicitly named solvable-block obligation remains beyond the
exact earlier E.6.7 and A.3.8(3) source inputs. -/
theorem exists_factor_conjugate {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {M V A X : Subgroup G}
    (h : HypothesisE61 κ T M V) (h67 : E67Input T M V)
    (h38 : SylowOrbitSource κ) (hthree : ThreeBlockCentralization κ G)
    (hA : A ∈ obstructionFamily M V)
    (hX : X ∈ Chapter1.cComponentsIn (centralizer (A : Set G))) (hXM : ¬ X ≤ M)
    (hf : generalizedFitting ↥(X ⊔ sylowCentralizer (T : Subgroup G) V) =
      pCore 2 ↥(X ⊔ sylowCentralizer (T : Subgroup G) V)) :
    ∃ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
        (X ⊔ sylowCentralizer (T : Subgroup G) V),
      ∃ i, ∃ s ∈ sylowCentralizer (T : Subgroup G) V,
        d.block i = X.map (MulAut.conj s).toMonoidHom := by
  let Q := sylowCentralizer (T : Subgroup G) V
  let D := X ⊔ Q
  obtain ⟨hSyl, hDH⟩ := cComponent_overgroup_sylow h hA hX
  have hsq : IsSQTK κ D := h.obstructionIntermediate_sqtk hA hDH
  have hXD : X ≤ D := le_sup_left
  have hXC : (X.subgroupOf D).IsCComponent := hX.2.subgroupOf_of_le hXD hDH
  obtain ⟨d⟩ := h67 A hA D le_sup_right hDH
    (by
      unfold HasCharacteristicTwo
      rw [← hf]
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le)
  obtain ⟨i, hi⟩ := exists_non_three_factor d hXD hXC hXM
    (fun j hj => hthree D hsq hf (d.block j) X (d.le j) hXD hj (d.subnormal j) hXC)
  obtain ⟨S, hS⟩ := hSyl
  have hgen : X.subgroupOf D ⊔ (S : Subgroup D) = ⊤ := by
    apply (map_injective D.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXD, hS,
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨s, hs⟩ := cComponent_conjugate_of_generated h38 hsq S hXC hgen
    (factor_cComponent (d.le i) (d.type i) (d.subnormal i) hi)
  have hsQ : ((s : D) : G) ∈ Q := by
    change ((s : D) : G) ∈ sylowCentralizer (T : Subgroup G) V
    rw [← hS]
    exact mem_map_of_mem D.subtype s.property
  refine ⟨d, i, ((s : D) : G), hsQ, ?_⟩
  have hm := congrArg (Subgroup.map D.subtype) hs
  have he : D.subtype.comp (MulAut.conj (s : D)).toMonoidHom =
      (MulAut.conj ((s : D) : G)).toMonoidHom.comp D.subtype := by ext x; rfl
  rw [map_subgroupOf_eq_of_le (d.le i), map_map, he, ← map_map,
    map_subgroupOf_eq_of_le hXD] at hm
  exact hm

/-- Conditional assembly of characteristic-two component lifting. The remaining
centralization premise is an outstanding obligation, not an earlier theorem.
The factor equality is used to transport the literal quotient and module to X;
its original C-component membership supplies subnormality in C_G(A). -/
theorem characteristicTwoComponentBlocks_of_threeBlockCentralization
    {G : Type*} [Group G] [Finite G] {κ : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 κ T M V) (h67 : E67Input T M V)
    (h38 : SylowOrbitSource κ) (hthree : ThreeBlockCentralization κ G) :
    CharacteristicTwoComponentBlocks (sylowCentralizer (T : Subgroup G) V) M V := by
  intro A hA _ X hX hXM hf
  obtain ⟨d, i, s, _, hs⟩ := exists_factor_conjugate h h67 h38 hthree hA hX hXM hf
  let e : X ≃* d.block i := ((MulAut.conj s).subgroupMap X).trans
    (MulEquiv.subgroupCongr hs.symm)
  have ht : ChapterC.IsChiZeroBlock X := chiZero_of_mulEquiv (d.type i) e.symm
  exact ⟨⟨hX.1, ⟨inferInstance,
    ht.chi.short.of_mulEquiv (subgroupOfEquivOfLe hX.1).symm, hX.2.subnormal⟩⟩, ht⟩

/-- The characteristic-two component branch from the source-facing inputs.
The E.6.7 decomposition and A.3.8 orbit assertion remain explicit; the
A₃-block centralization premise is constructed from the exact C.1.9 input.
Hypothesis E.6.15 is retained at this boundary because it belongs to the
ambient E.6 setup, although this local branch does not use its disjunction.
-/
theorem characteristicTwoComponentBlocks
    {G : Type*} [Group G] [Finite G] {M V : Subgroup G}
    [IsElementaryAbelian 2 V]
    {κ : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 κ T M V)
    (_h15 : HypothesisE615 V) (h67 : E67Input T M V)
    (h38 : SylowOrbitSource κ) (h19 : BlockCommutationInput G) :
    CharacteristicTwoComponentBlocks (sylowCentralizer (T : Subgroup G) V) M V := by
  exact characteristicTwoComponentBlocks_of_threeBlockCentralization h h67 h38
    (CharacteristicTwoBlocks.threeBlockCentralization_of_blockCommutation h19)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
