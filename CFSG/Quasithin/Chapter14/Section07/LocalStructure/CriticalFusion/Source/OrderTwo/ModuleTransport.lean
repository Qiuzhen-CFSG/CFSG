module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.FixedCoordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# The original module in the order-two argument

The exact earlier 14.5.15(4) equality C_H(U/V₁)=O₂(H) descends the given
H-action through its actual S₅ marking. Both the section coordinates and the
natural projection are preserved. The proved alternating image of K transports
its fixed kernel and indecomposability; the universal SL₂(4) cover therefore
surjects onto this original section. Its upper fixed/moved identity and the
rank-two displacement and complement formulas now apply to literal H-actors.
Restricting the original coordinate map identifies U₀/V₁ with the original
projection kernel and gives |U₀|=2, 4 or 8.

`SectionCentralizer` is precisely an earlier source input, produced by qt-14-05
from 12.8.4; it is not inferred from dimensions or from O₂(K). The remaining
critical-pair exclusions proving 14.7.69 are not asserted by these transports.
The source V-line still requires its action marking when applying the fixed
plane partitions; a dimension count alone does not identify it.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.15(4), printed p.1017; Remark 14.7.64 and Lemmas 14.7.69–70,
printed pp.1069, 1072–1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Representation Representation.OneCohomology
open Chapter12.Section08
open Representation.SL2FourNatural
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The exact earlier 14.5.15(4) equality on the original section U/V₁. -/
def SectionCentralizer : Prop :=
  d.action.ker = (F.H.pCoreIn 2).subgroupOf F.H

/-- The action descended through the actual H/O₂(H) marking, on the same W. -/
def descendedAction (hc : d.SectionCentralizer) : Representation (ZMod 2) ChapterJ.S5 W :=
  (Units.coeHom (Module.End (ZMod 2) W)).comp
    (d.qH.liftOfSurjective d.qH_surjective ⟨d.action.asGroupHom, by
      intro h hh
      apply Units.ext
      change h ∈ d.action.ker
      rw [show d.action.ker = d.qH.ker from hc.trans d.qH_ker.symm]
      exact hh⟩)

theorem descendedAction_apply (hc : d.SectionCentralizer) (h : F.H) :
    d.descendedAction hc (d.qH h) = d.action h := by
  unfold descendedAction
  rw [MonoidHom.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem descendedAction_comp (hc : d.SectionCentralizer) :
    (d.descendedAction hc).comp d.qH = d.action := by
  ext h w
  exact LinearMap.congr_fun (d.descendedAction_apply hc h) w

/-- The projection is unchanged when the actors descend. -/
def descendedProjection (hc : d.SectionCentralizer) :
    (d.descendedAction hc).IntertwiningMap d.naturalQuotient.action :=
  d.projection.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g w
    obtain ⟨h, rfl⟩ := d.qH_surjective g
    rw [d.descendedAction_apply]
    exact LinearMap.congr_fun (d.projection.isIntertwining' h) w)

/-- Descent preserves the coordinate homomorphism and its actual kernel V₁. -/
def descendedSection (hc : d.SectionCentralizer) :
    BinaryConjugationSection F.H F.U (F.Vi 1) ((d.descendedAction hc).comp d.qH) where
  section_le := d.conjugationSection.section_le
  kernel_le := d.conjugationSection.kernel_le
  normalized := d.conjugationSection.normalized
  coordinates := d.conjugationSection.coordinates
  onto := d.conjugationSection.onto
  kernel_eq := d.conjugationSection.kernel_eq
  equivariant h v := by
    change _ = d.descendedAction hc (d.qH h) _
    rw [d.descendedAction_apply]
    exact d.conjugationSection.equivariant h v

/-- Each element of the marked SL₂(4) is lifted from the original K. -/
theorem alternatingActor_lift (g : SL) :
    ∃ k : (K F).subgroupOf F.H,
      d.qH k = alternatingActor d.naturalQuotient g := by
  have hg : alternatingActor d.naturalQuotient g ∈
      ((K F).subgroupOf F.H).map d.qH := by
    rw [d.K_image]
    exact (d.naturalQuotient.marking g).property
  obtain ⟨k, hk, he⟩ := hg
  exact ⟨⟨k, hk⟩, he⟩

/-- Conversely every element of K has its image in this same alternating marking. -/
theorem K_image_lift (k : (K F).subgroupOf F.H) :
    ∃ g : SL, alternatingActor d.naturalQuotient g = d.qH k := by
  have hk : d.qH k ∈ alternatingGroup (Fin 5) := by
    rw [← d.K_image]
    exact mem_map_of_mem d.qH k.property
  refine ⟨d.naturalQuotient.marking.symm ⟨d.qH k, hk⟩, ?_⟩
  exact congrArg Subtype.val (d.naturalQuotient.marking.apply_symm_apply _)

/-- The original fixed kernel remains the fixed kernel under actor descent. -/
theorem descended_fixed_kernel (hc : d.SectionCentralizer) :
    d.projection.toLinearMap.ker =
      fixed ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)) := by
  rw [d.fixed_kernel]
  ext w
  constructor
  · intro hw g
    obtain ⟨k, hk⟩ := d.alternatingActor_lift g
    change d.descendedAction hc (alternatingActor d.naturalQuotient g) w = w
    rw [← hk, d.descendedAction_apply]
    exact hw k
  · intro hw k
    obtain ⟨g, hg⟩ := d.K_image_lift k
    change d.action k w = w
    rw [← d.descendedAction_apply hc k, ← hg]
    exact hw g

theorem descended_indecomposable (hc : d.SectionCentralizer)
    (A B : Submodule (ZMod 2) W)
    (hA : ∀ g v, v ∈ A → d.descendedAction hc (alternatingActor d.naturalQuotient g) v ∈ A)
    (hB : ∀ g v, v ∈ B → d.descendedAction hc (alternatingActor d.naturalQuotient g) v ∈ B)
    (hAB : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  apply d.indecomposable A B _ _ hAB
  · intro k w hw
    obtain ⟨g, hg⟩ := d.K_image_lift k
    rw [← d.descendedAction_apply hc k, ← hg]
    exact hA g w hw
  · intro k w hw
    obtain ⟨g, hg⟩ := d.K_image_lift k
    rw [← d.descendedAction_apply hc k, ← hg]
    exact hB g w hw

include d in
/-- Finiteness comes from the original section map, without a replacement module. -/
theorem finite_section : Finite W :=
  Finite.of_surjective (fun v : F.U => (d.conjugationSection.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp d.conjugationSection.onto)

/-- Remark 14.7.64 on the original section and its original natural projection. -/
theorem original_cover (hc : d.SectionCentralizer) :
    ∃ q : SL2FourCentralCover.binaryAction.IntertwiningMap
      ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)),
      Function.Surjective q ∧
      (∀ w, d.projection (q w) = SL2FourCentralCover.projection w) ∧
      Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 2 ∧
      Nat.card F.U ≤ 128 := by
  let := d.finite_section
  obtain ⟨q, hq, hp, hk, hcard⟩ := original_section_cover
    d.naturalQuotient d.qH (d.descendedSection hc) (d.descendedProjection hc)
    d.projection_onto (le_of_eq (d.descended_fixed_kernel hc))
    (d.descended_indecomposable hc)
  refine ⟨q, hq, hp, hk, ?_⟩
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  simpa only [hpoint, Nat.reduceMul] using hcard

/-- The whole marked upper four-group has equal fixed and moved spaces. -/
theorem original_upper_moved_eq_fixed (hc : d.SectionCentralizer) :
    SL2CentralExtension.movedSpace
      ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient))
      (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F) ⊤ =
      SL2CentralExtension.upperFixed
        ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)) := by
  let := d.finite_section
  exact original_section_upper_moved_eq_fixed d.naturalQuotient (d.descendedProjection hc)
    d.projection_onto (le_of_eq (d.descended_fixed_kernel hc)) (d.descended_indecomposable hc)

/-- Rank two for the literal H-actor lifting a marked nonzero upper element. -/
theorem original_displacement_finrank (hc : d.SectionCentralizer)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (upper t)) :
    Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2 := by
  let := d.finite_section
  rw [← d.descendedAction_apply hc h, hh]
  exact original_section_upper_displacement_finrank d.naturalQuotient
    (d.descendedProjection hc) d.projection_onto
    (le_of_eq (d.descended_fixed_kernel hc)) (d.descended_indecomposable hc) t ht

/-- The original actor's displacement complements the original projection kernel. -/
theorem original_displacement_complement (hc : d.SectionCentralizer)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (upper t)) :
    Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker ∧
      SL2CentralExtension.upperFixed
        ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)) =
        (d.action h - LinearMap.id).range ⊔ d.projection.toLinearMap.ker := by
  rw [← d.descendedAction_apply hc h, hh]
  exact original_section_upper_complement d.naturalQuotient (d.descendedProjection hc)
    d.projection_onto (le_of_eq (d.descended_fixed_kernel hc))
    (d.descended_indecomposable hc) t ht

/-- The kernel order is measured on U₀/V₁ itself. -/
theorem card_U₀ : Nat.card d.U₀ =
    2 * 2 ^ Module.finrank (ZMod 2) d.projection.toLinearMap.ker := by
  let := d.finite_section
  rw [card_eq_card_quotient_mul_card_subgroup d.fixedCoordinates.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.fixedCoordinates
      d.fixedCoordinates_surjective).toEquiv]
  have hker : Nat.card d.fixedCoordinates.ker = 2 := by
    rw [d.fixedCoordinates_ker,
      Nat.card_congr (subgroupOfEquivOfLe d.point_le_U₀).toEquiv]
    simpa using F.card 1 (by decide)
  rw [hker, mul_comm]
  congr 1
  change Nat.card d.projection.toLinearMap.ker = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card]

/-- These are exactly the three cases used in the proof of 14.7.69. -/
theorem card_U₀_cases (hc : d.SectionCentralizer) :
    Nat.card d.U₀ = 2 ∨ Nat.card d.U₀ = 4 ∨ Nat.card d.U₀ = 8 := by
  obtain ⟨q, hq, hp, hk, hU⟩ := d.original_cover hc
  rw [d.card_U₀]
  interval_cases he : Module.finrank (ZMod 2) d.projection.toLinearMap.ker <;> decide

/-- Fixed vectors of a literal upper actor are detected by the original p. -/
theorem original_upper_fixed_iff (hc : d.SectionCentralizer)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (upper t)) (w : W) :
    d.action h w = w ↔ d.projection w 1 = 0 := by
  rw [← d.descendedAction_apply hc h, hh]
  let p := restrictedProjection d.naturalQuotient (d.descendedProjection hc)
  exact SL2FourCentralCover.quotient_upper_fixed_iff p
    (SL2FourCentralCover.isCover_of_natural_indecomposable p d.projection_onto
      (le_of_eq (d.descended_fixed_kernel hc)) (d.descended_indecomposable hc)) t ht w

/-- The same literal actor cannot centralize a binary hyperplane. -/
theorem original_no_fixed_hyperplane (hc : d.SectionCentralizer)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (upper t))
    (A : Submodule (ZMod 2) W)
    (hA : Module.finrank (ZMod 2) A + 1 = Module.finrank (ZMod 2) W) :
    ¬ ∀ w ∈ A, d.action h w = w := by
  let := d.finite_section
  intro hfix
  have hle : A ≤ (d.action h - LinearMap.id).ker := by
    intro w hw
    change d.action h w - w = 0
    exact sub_eq_zero.mpr (hfix w hw)
  have hd := Submodule.finrank_mono hle
  have hr := (d.action h - LinearMap.id).finrank_range_add_finrank_ker
  rw [d.original_displacement_finrank hc h t ht hh] at hr
  omega

/-- In the rank-two U₀ case its one-dimensional quotient is fixed by H.
This is the tilde-centrality used immediately before applying 14.7.68(2). -/
theorem kernel_fixed_of_card_U₀_four (hcard : Nat.card d.U₀ = 4)
    (h : F.H) (w : W) (hw : w ∈ d.projection.toLinearMap.ker) :
    d.action h w = w := by
  let := d.finite_section
  have hcardk : Nat.card d.projection.toLinearMap.ker = 2 := by
    have hk : Nat.card d.projection.toLinearMap.ker =
        2 ^ Module.finrank (ZMod 2) d.projection.toLinearMap.ker := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
        Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card]
    rw [d.card_U₀, ← hk] at hcard
    omega
  by_cases hw0 : w = 0
  · simp [hw0]
  obtain ⟨a, ha, he⟩ := (Nat.card_eq_two_iff' (0 : d.projection.toLinearMap.ker)).mp hcardk
  have hn : d.action h w ≠ 0 := by
    intro hz
    have hh := congrArg (d.action h⁻¹) hz
    rw [d.action.inv_self_apply, map_zero] at hh
    exact hw0 hh
  have hwe : (⟨w, hw⟩ : d.projection.toLinearMap.ker) = a :=
    he _ (fun hz => hw0 (congrArg Subtype.val hz))
  have hhe : (⟨d.action h w, d.projection_ker_invariant h w hw⟩ :
      d.projection.toLinearMap.ker) = a :=
    he _ (fun hz => hn (congrArg Subtype.val hz))
  exact congrArg Subtype.val (hhe.trans hwe.symm)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
