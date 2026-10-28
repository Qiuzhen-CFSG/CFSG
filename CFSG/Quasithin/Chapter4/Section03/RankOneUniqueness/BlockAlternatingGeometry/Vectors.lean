module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.Contracts
public import Theory.Representation.BinaryPermutation.SevenPairGeneration
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Marked vectors and ambient generation for the ordinary A₇ branch

Compatible coordinates identify U(K) with the binary seven-letter core.
The vector e₀₁ is a nonzero transposition displacement fixed by L, and
an actual lift of (02)(13) in K conjugates it to e₂₃ in the full module.
The two conjugates of L contain the six pair vectors forming a basis of U(K)
and generate the A₇ image.

For the ambient lift, retain the whole O₂(K): its commutator with K is U(K),
so it normalizes the join of the two conjugates. This join supplements O₂(K),
and two-perfection of K absorbs the remaining two-group quotient.
The final theorem applies the published local-geometry constructor; producing
the source coordinates remains a separate obligation.

Source: Aschbacher--Smith, original 4.3.7, printed p.616.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
open BinaryPermutation.SevenParabolic BinaryPermutation.SevenParabolic.Ordinary
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
namespace BlockAlternatingCoordinates
variable {c : SourceConfiguration T L} (d : BlockAlternatingCoordinates c)
include d
private abbrev A (c : SourceConfiguration T L) := c.K.map c.H.subtype
private abbrev J (c : SourceConfiguration T L) := A c ⊔ ((T : Subgroup G) ⊓ c.H)
private abbrev U (c : SourceConfiguration T L) := (ChapterC.blockU (A c)).map (A c).subtype

private theorem moved_le : ⁅U c,L⁆ ≤ L := by
  rw [d.full_module]
  exact c.c28.module_le.trans (conjugateSpanBy_le le_rfl inf_le_right)

private theorem pair_mem_moved (i : Fin 7) (hi : 2 ≤ i.val) (hi6 : i ≠ 6) :
    (d.chart.lift (SevenPairGeneration.pair i 6) : G) ∈ ⁅U c,L⁆ := by
  have hg : SevenPairGeneration.cycle i ∈ (L.subgroupOf (J c)).map d.chart.actor := by
    rw [d.five_image]
    exact SevenPairGeneration.cycle_mem i hi hi6
  rw [← SevenPairGeneration.cycle_displacement i hi hi6]
  exact d.chart.lift_displacement_mem L _ hg _

private theorem pair23_mem_moved :
    (d.chart.lift (SevenPairGeneration.pair 2 3) : G) ∈ ⁅U c,L⁆ := by
  rw [SevenPairGeneration.pair23_expression,d.chart.lift_add]
  exact (⁅U c,L⁆).mul_mem (d.pair_mem_moved 2 (by decide) (by decide))
    (d.pair_mem_moved 3 (by decide) (by decide))

private theorem conjugate_lift (k : J c) (hk : d.chart.actor k = SevenPairGeneration.exchange)
    (v : Space) : MulAut.conj (k.val)⁻¹ (d.chart.lift v : G) =
      (d.chart.lift (action SevenPairGeneration.exchange⁻¹ v) : G) := by
  have he := d.chart.lift_action k⁻¹ v
  rw [map_inv,hk] at he
  exact he.symm

private theorem module_le_pair (k : J c) (hk : d.chart.actor k = SevenPairGeneration.exchange) :
    U c ≤ L ⊔ L.map (MulAut.conj (k.val)⁻¹).toMonoidHom := by
  apply d.chart.lift_pair_basis_le
  intro i
  have h2 := d.moved_le (d.pair_mem_moved 2 (by decide) (by decide))
  have h3 := d.moved_le (d.pair_mem_moved 3 (by decide) (by decide))
  by_cases hi0 : i = 0
  · subst i
    rw [show (0 : Fin 6).castSucc = 0 from rfl,SevenPairGeneration.pair06_exchange]
    rw [← d.conjugate_lift k hk]
    exact mem_sup_right (mem_map_of_mem _ h2)
  by_cases hi1 : i = 1
  · subst i
    rw [show (1 : Fin 6).castSucc = 1 from rfl,SevenPairGeneration.pair16_exchange]
    rw [← d.conjugate_lift k hk]
    exact mem_sup_right (mem_map_of_mem _ h3)
  apply mem_sup_left
  apply d.moved_le
  apply d.pair_mem_moved
  · have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
    change 2 ≤ i.val
    omega
  · intro h
    have he := congrArg Fin.val h
    have hi := i.isLt
    change i.val = 6 at he
    omega

variable [Finite G]

private theorem generation (ha : ChapterC.IsAlternatingBlock c.K 7)
    (k : J c) (hkA : k.val ∈ A c) (hk : d.chart.actor k = SevenPairGeneration.exchange) :
    A c = L ⊔ L.map (MulAut.conj (k.val)⁻¹).toMonoidHom := by
  let B := L ⊔ L.map (MulAut.conj (k.val)⁻¹).toMonoidHom
  have hBA : B ≤ A c := by
    refine sup_le c.le_component ?_
    rintro _ ⟨l,hl,rfl⟩
    exact (A c).mul_mem ((A c).mul_mem ((A c).inv_mem hkA) (c.le_component hl))
      (by simpa only [inv_inv] using hkA)
  have hfirst : SevenPairGeneration.five ≤ (B.subgroupOf (J c)).map d.chart.actor := by
    rw [SevenPairGeneration.five, ← d.five_image]
    exact map_mono (subgroupOf_mono (J c) le_sup_left)
  have hsecond : SevenPairGeneration.five.map (MulAut.conj SevenPairGeneration.exchange⁻¹).toMonoidHom ≤
      (B.subgroupOf (J c)).map d.chart.actor := by
    rintro _ ⟨g,hg,rfl⟩
    have hgl : g ∈ (L.subgroupOf (J c)).map d.chart.actor := by
      rw [d.five_image]
      exact hg
    obtain ⟨l,hl,rfl⟩ := hgl
    refine ⟨k⁻¹*l*k,?_,?_⟩
    · change k.val⁻¹ * l.val * k.val ∈ B
      apply mem_sup_right
      exact ⟨l.val,hl,by simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]⟩
    · simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]
      rw [map_mul,map_mul,map_inv,hk]
  have himage : alternatingGroup (Fin 7) ≤ (B.subgroupOf (J c)).map d.chart.actor := by
    rw [← SevenPairGeneration.five_generation]
    exact sup_le hfirst hsecond
  have hsupp : A c ≤ B ⊔ (A c).pCoreIn 2 := by
    intro a haA
    let aJ : J c := ⟨a,(show A c ≤ J c from le_sup_left) haA⟩
    have haimage : d.chart.actor aJ ∈ alternatingGroup (Fin 7) := by
      rw [← d.chart.component_image]
      exact mem_map_of_mem _ haA
    obtain ⟨b,hb,hba⟩ := himage haimage
    have hdiff : b⁻¹*aJ ∈ d.chart.actor.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hba,inv_mul_cancel]
    have hcore : b.val⁻¹*a ∈ (J c).pCoreIn 2 := by
      exact mem_map_of_mem (J c).subtype (d.kernel ▸ hdiff)
    have hsmall : b.val⁻¹*a ∈ (A c).pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 (show A c ≤ J c from le_sup_left)
        ⟨(A c).mul_mem ((A c).inv_mem (hBA hb)) haA,hcore⟩
    have he := (B ⊔ (A c).pCoreIn 2).mul_mem (mem_sup_left hb) (mem_sup_right hsmall)
    change b.val * (b.val⁻¹ * a) ∈ B ⊔ (A c).pCoreIn 2 at he
    simpa only [mul_inv_cancel_left] using he
  have hcomm : ⁅(A c).pCoreIn 2,A c⁆ = U c := by
    rw [U,ChapterC.blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    rfl
  have hn : (A c).pCoreIn 2 ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact ((commutator_mono le_rfl hBA).trans hcomm.le).trans (d.module_le_pair k hk)
  exact le_antisymm (le_of_isPPerfect_of_le_sup_of_normalizes (A c) B ((A c).pCoreIn 2)
    (c.ambient_alternating_block ha).2.1.twoPerfect (isPGroup_pCoreIn 2 _) hn hsupp) hBA

/-- The vector and generation clauses follow from the compatible seven-letter coordinates. -/
theorem vectorGeometry (ha : ChapterC.IsAlternatingBlock c.K 7) :
    Nonempty (BlockAlternatingVectorGeometry c) := by
  have heven : SevenPairGeneration.exchange ∈ ((A c).subgroupOf (J c)).map d.chart.actor := by
    rw [d.chart.component_image]
    exact SevenPairGeneration.exchange_even
  obtain ⟨k,hkA,hk⟩ := heven
  refine ⟨{ z := (d.chart.lift (SevenPairGeneration.pair 0 1) : G)
            k := k.val
            z_ne := d.chart.lift_ne_one SevenPairGeneration.pair_ne
            z_two := d.chart.lift_two _
            z_commutator := ?_
            z_centralizes := ?_
            k_mem := hkA
            conjugate_mem := ?_
            generation := d.generation ha k hkA hk }⟩
  · have hr : Equiv.swap (0 : Fin 7) 1 ∈ ((c.I.pCoreIn 2).subgroupOf (J c)).map
        d.chart.actor := by
      rw [d.transposition]
      exact mem_zpowers _
    rw [← SevenPairGeneration.pair_displacement]
    exact d.chart.lift_displacement_mem _ _ hr _
  · intro l hl
    let lJ : J c := ⟨l,c.le_component.trans le_sup_left hl⟩
    have hm : d.chart.actor lJ ∈ SevenPairGeneration.five := by
      rw [SevenPairGeneration.five, ← d.five_image]
      exact mem_map_of_mem _ hl
    have hfix := (SevenPairGeneration.mem_five _).mp hm
    exact mem_centralizer_singleton_iff.mp
      ((d.chart.centralizes_lift_iff lJ _).mpr (SevenPairGeneration.pair_fixed _ hfix.2.1 hfix.2.2))
  · rw [d.conjugate_lift k hk,SevenPairGeneration.exchange_pair]
    rw [← d.full_module]
    exact d.pair23_mem_moved
end BlockAlternatingCoordinates

variable [Finite G]

/-- Assemble the actual marking from local geometry and the explicit vector calculation. -/
theorem SourceConfiguration.alternating_marking_of_local_geometry
    (c : SourceConfiguration T L) (ha : ChapterC.IsAlternatingBlock c.K 7)
    (d : BlockAlternatingLocalGeometry c) : Nonempty (BlockAlternatingMarking c) := by
  obtain ⟨v⟩ := d.toBlockAlternatingCoordinates.vectorGeometry ha
  exact c.alternating_marking_of_geometry ha d v
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
