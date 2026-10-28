module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Rank
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel

/-!
# The characteristic span of the small-block modules

In a finite group of characteristic two, distinct blocks commute. The span
of U(L) = [O₂(L),L] over all A₃ and A₅ blocks is characteristic and lies in
the two-core. Each of its factors has trivial centralizer under its own
block; a finite commuting-product calculation gives trivial intersection
of the full span with the ambient center.

This span contains every normalizer orbit of a selected small-block module.
It supplies the normal subgroup in E.6.10(4) without asserting that all of
O₂(L) is fixed-point-free: the central factor allowed by C.1.13(c) is retained.
Source: Aschbacher–Smith, E.6.10(4), printed p.249, using C.1.9 and C.1.13(c).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Blocks.OrbitOmega
open ChapterC
variable {G : Type*} [Group G]

private def movedModule (L : Subgroup G) : Subgroup G := (blockU L).map L.subtype

private theorem movedModule_map (L : Subgroup G) (a : MulAut G) :
    movedModule (L.map a.toMonoidHom) = (movedModule L).map a.toMonoidHom := by
  let e := equivMapOfInjective L a.toMonoidHom a.injective
  have he := RankOne.Solvable.blockU_map_equiv e
  rw [movedModule, ← he, map_map, movedModule, map_map]
  rfl

private theorem movedModule_fixed (L : Subgroup G)
    (hL : IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5) :
    movedModule L ⊓ centralizer (L : Set G) = ⊥ := by
  have hz : blockU L ⊓ center L = ⊥ := by
    rcases hL with hL | hL
    · rw [hL.center_eq_bot, inf_bot_eq]
    · rw [← blockFixed_map, hL.blockFixed_eq_bot, Subgroup.map_bot]
  apply bot_unique
  rintro x ⟨⟨a, ha, rfl⟩, hc⟩
  have haZ : a ∈ center L := mem_center_iff.mpr fun b =>
    Subtype.ext (hc b b.property)
  exact congrArg L.subtype (mem_bot.mp (hz ▸ (show a ∈ blockU L ⊓ center L from ⟨ha, haZ⟩)))

private theorem commuting_module_span_inf_center_eq_bot
    {ι : Type*} [Finite ι] (L D : ι → Subgroup G)
    (hDL : ∀ i, D i ≤ L i)
    (hc : ∀ i j, i ≠ j → L i ≤ centralizer (L j : Set G))
    (hfix : ∀ i, D i ⊓ centralizer (L i : Set G) = ⊥) :
    (⨆ i, D i) ⊓ center G = ⊥ := by
  classical
  let := Fintype.ofFinite ι
  have hs (s : Finset ι) : s.sup D ⊓ center G ≤ ⊥ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sup_insert]
      have hcomm : s.sup D ≤ centralizer (L i : Set G) :=
        Finset.sup_le fun j hj => (hDL j).trans (hc j i (ne_of_mem_of_not_mem hj hi))
      have hn : s.sup D ≤ normalizer (D i : Set G) :=
        (hcomm.trans (centralizer_le (hDL i))).trans (Subgroup.centralizer_le_normalizer _)
      rintro x ⟨hx, hz⟩
      have hp : x ∈ (D i : Set G) * ((s.sup D : Subgroup G) : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left (D i) (s.sup D) hn]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hp
      have haC : a ∈ centralizer (L i : Set G) :=
        ((centralizer (L i : Set G)).mul_mem_cancel_right (hcomm hb)).mp
          (center_le_centralizer _ hz)
      have ha1 : a = 1 := mem_bot.mp (hfix i ▸ (show a ∈ D i ⊓ centralizer (L i : Set G) from ⟨ha, haC⟩))
      simpa only [ha1, one_mul] using ih ⟨hb, by simpa only [ha1, one_mul] using hz⟩
  have ht := hs Finset.univ
  rw [Finset.sup_univ_eq_iSup] at ht
  exact bot_unique ht

private abbrev SmallBlockIndex (G : Type*) [Group G] :=
  {L : Subgroup G // IsBlock L ∧ (IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5)}

/-- The characteristic span of the actual moved modules of all A₃/A₅ blocks. -/
def smallBlockModuleSpan (G : Type*) [Group G] : Subgroup G :=
  ⨆ i : SmallBlockIndex G, movedModule i.val

/-- Automorphisms permute the blocks and carry their literal commutator layers. -/
theorem smallBlockModuleSpan_characteristic : (smallBlockModuleSpan G).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro a
  rw [smallBlockModuleSpan, Subgroup.map_iSup]
  apply iSup_le
  intro i
  let := i.property.1.finite
  let j : SmallBlockIndex G := ⟨i.val.map a.toMonoidHom, i.property.1.map_equiv a,
    i.property.2.imp (RankOne.Solvable.isAlternatingBlock_of_equiv (a.subgroupMap i.val))
      (RankOne.Solvable.isAlternatingBlock_of_equiv (a.subgroupMap i.val))⟩
  rw [← movedModule_map]
  exact le_iSup (fun i : SmallBlockIndex G => movedModule i.val) j

variable [Finite G]

/-- Subnormality places each block module, and hence their span, in O₂. -/
theorem smallBlockModuleSpan_le_core : smallBlockModuleSpan G ≤ pCore 2 G := by
  apply iSup_le
  intro i
  exact (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 i.property.1.subnormal)

/-- The commuting-product calculation removes the fixed points of the full span. -/
theorem smallBlockModuleSpan_inf_center_eq_bot
    (hf : generalizedFitting G = pCore 2 G) :
    smallBlockModuleSpan G ⊓ center G = ⊥ := by
  apply commuting_module_span_inf_center_eq_bot
    (fun i : SmallBlockIndex G => i.val) (fun i => movedModule i.val)
  · intro i
    exact map_subtype_le _
  · intro i j hij
    exact commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf)
        i.property.1 j.property.1 (fun he => hij (Subtype.ext he)))
  · intro i
    exact movedModule_fixed i.val i.property.2

omit [Finite G] in
/-- A single actual small block makes the characteristic module span nontrivial. -/
theorem smallBlockModuleSpan_ne_bot (L : Subgroup G) (hL : IsBlock L)
    (ha : IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5) :
    smallBlockModuleSpan G ≠ ⊥ := by
  intro he
  have hu : movedModule L ≤ smallBlockModuleSpan G :=
    le_iSup (fun i : SmallBlockIndex G => movedModule i.val) ⟨L, hL, ha⟩
  have hz : (blockU L).map L.subtype = ⊥ := bot_unique (he ▸ hu)
  exact hL.short.blockU_ne_bot ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp hz)

end CFSG.Quasithin.ChapterE.Section06.Blocks.OrbitOmega
