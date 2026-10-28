module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Action
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Cover
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# The natural A₅ cover of the literal moved subgroup

A natural-module marking retains the original conjugation action on
U=[R₂(N_G(L)),L] and its quotient by C_U(L). The source commutator identity
constructs a central cover; it is not a field in the marking. The resulting
orthogonal covering map commutes with the original LT-action and with the
literal natural projection. Every C_L(u) has a full component Sylow image.

The classification in 13.1.10 supplies the marking. The remaining outer-action
and selected-orbit calculations in 13.1.12 are not assumed or asserted here.
Source: Aschbacher--Smith, printed pp.869--872, and I.2.3, printed p.413.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem moved_le_component (L : Subgroup G) : normalizerMoved L ≤ L := by
  rw [normalizerMoved_eq]
  exact le_normalizer_iff_commutator_le_right.mp (map_subtype_le _)

/-- A genuine natural-quotient marking of the original action, with explicit
compatible normalizing actors. No cover dimension, orbit or stabilizer
conclusion is included. `kernel_fixed` expresses centrality only under L. -/
structure Marking (T : Sylow 2 G) (L : Subgroup G) (W : Type*)
    [AddCommGroup W] [Module (ZMod 2) W] where
  invariant : L ⊔ (T : Subgroup G) ≤ normalizer (normalizerMoved L : Set G)
  coordinates : normalizerMoved L ≃* Multiplicative W
  component : L →* SL
  onto : Function.Surjective component
  representation : Representation (ZMod 2) SL W
  actor : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W
  equivariant : ∀ (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (u : normalizerMoved L),
    (coordinates ((normalizerMoved L).normalizerMonoidHom (inclusion invariant a) u)).toAdd =
      actor a (coordinates u).toAdd
  component_action : ∀ (l : L) (w : W),
    actor (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l) w =
      representation (component l) w
  projection : representation.IntertwiningMap Natural
  projection_onto : Function.Surjective projection
  kernel_fixed : projection.toLinearMap.ker ≤ fixed representation
  conjugation : (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut SL
  naturalActor : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) V
  compatible : ∀ a l w, actor a (representation l w) =
    representation (conjugation a l) (actor a w)
  quotient_action : ∀ a w, projection (actor a w) = naturalActor a (projection w)

namespace Marking
variable {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

/-- The full original moved group, with zero kernel, in its chosen coordinates. -/
def wholeSection : BinaryConjugationSection (L ⊔ (T : Subgroup G))
    (normalizerMoved L) ⊥ d.actor where
  section_le := (moved_le_component L).trans le_sup_left
  kernel_le := bot_le
  normalized := d.invariant
  coordinates := d.coordinates.toMonoidHom
  onto := d.coordinates.surjective
  kernel_eq := by rw [d.coordinates.toMonoidHom.ker_eq_bot d.coordinates.injective, bot_subgroupOf]
  equivariant a u := d.equivariant a u

/-- The group commutator identity supplies the covering hypothesis. -/
@[expose] def naturalCover (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    NaturalCover (L ⊔ (T : Subgroup G) : Subgroup G) W where
  component := d.representation
  actor := d.actor
  conjugation := d.conjugation
  naturalActor := d.naturalActor
  projection := d.projection
  cover := ⟨d.projection_onto, d.kernel_fixed,
    d.wholeSection.coinvariants_eq_top_of_group_generation L le_sup_left
      d.representation d.component d.component_action (by
        rw [sup_bot_eq, commutator_comm, hmoved])⟩
  compatible := d.compatible
  quotient_action := d.quotient_action

/-- Source13.1.8 discharges full movement on the original U. -/
@[expose] def sourceCover (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    NaturalCover (L ⊔ (T : Subgroup G) : Subgroup G) W := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact d.naturalCover (normalizerMoved_commutator_and_card hL.1.1
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1).1

omit [Finite G] in
/-- Literal conjugation fixes u precisely when the marked component fixes its coordinate. -/
theorem component_fixes_iff (l : L) (u : normalizerMoved L) :
    d.representation (d.component l) (d.coordinates u).toAdd = (d.coordinates u).toAdd ↔
      (l : G) ∈ centralizer ({(u : G)} : Set G) := by
  have he : (d.coordinates (componentAction L l u)).toAdd =
      d.representation (d.component l) (d.coordinates u).toAdd :=
    (d.equivariant (inclusion le_sup_left l) u).trans (d.component_action l _)
  rw [← he]
  constructor
  · intro h
    have hu : componentAction L l u = u := d.coordinates.injective h
    have hu' := congrArg Subtype.val hu
    change (l : G) * (u : G) * (l : G)⁻¹ = (u : G) at hu'
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hu')
  · intro h
    apply congrArg (fun x => (d.coordinates x).toAdd)
    apply Subtype.ext
    change (l : G) * (u : G) * (l : G)⁻¹ = (u : G)
    rw [mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]

omit [Finite G] in
/-- The marked component map has exactly the kernel of the actual L-action. -/
theorem component_kernel : d.component.ker = (componentAction L).ker := by
  ext l
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  have he (u : normalizerMoved L) : (d.coordinates (componentAction L l u)).toAdd =
      d.representation (d.component l) (d.coordinates u).toAdd :=
    (d.equivariant (inclusion le_sup_left l) u).trans (d.component_action l _)
  constructor
  · intro hl
    apply MulEquiv.ext
    intro u
    apply d.coordinates.injective
    change (d.coordinates (componentAction L l u)).toAdd = (d.coordinates u).toAdd
    rw [he,hl,map_one]
    rfl
  · intro hl
    apply action_faithful
    rw [map_one]
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := d.projection_onto v
    obtain ⟨u,hu⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    have hf : d.representation (d.component l) w = w := by
      have hh := he u
      rw [hl] at hh
      change (d.coordinates u).toAdd = _ at hh
      rw [hu] at hh
      exact hh.symm
    change Natural (d.component l) (d.projection w) = d.projection w
    rw [← d.projection.isIntertwining,hf]

/-- The model quotient is the original L/O∞(L), with no additional kernel premise. -/
theorem component_kernel_eq_radical
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    d.component.ker = solvableRadical L := by
  rw [d.component_kernel, componentAction_ker_eq_radical h hmany hL hn]

omit [Finite G] in
/-- The natural projection has exactly the actual centralizer kernel. -/
theorem projection_zero_iff (u : normalizerMoved L) :
    d.projection (d.coordinates u).toAdd = 0 ↔
      (u : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro hu l hl
    have hh := (d.component_fixes_iff ⟨l,hl⟩ u).mp (d.kernel_fixed hu (d.component ⟨l,hl⟩))
    exact mem_centralizer_singleton_iff.mp hh
  · intro hu
    change d.projection (d.coordinates u).toAdd ∈ (⊥ : Submodule (ZMod 2) V)
    apply (SL2OrthogonalCover.natural_fixed (F := F)).le
    intro l
    obtain ⟨k,rfl⟩ := d.onto l
    rw [← d.projection.isIntertwining,
      (d.component_fixes_iff k u).mpr (mem_centralizer_singleton_iff.mpr
        (hu k k.property))]

/-- The coordinate homomorphism to the natural quotient, without changing U. -/
def naturalCoordinates : normalizerMoved L →* Multiplicative V :=
  d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp d.coordinates.toMonoidHom

omit [Finite G] in
/-- Its kernel is the literal C_U(L), with the original subgroup inclusion. -/
theorem naturalCoordinates_kernel : d.naturalCoordinates.ker =
    (centralizer (L : Set G)).subgroupOf (normalizerMoved L) := by
  ext u
  exact d.projection_zero_iff u

/-- Identify U/C_U(L), not an unrelated isomorphic module. -/
def centralQuotientEquiv :
    (normalizerMoved L ⧸ d.naturalCoordinates.ker) ≃* Multiplicative V :=
  QuotientGroup.quotientKerEquivOfSurjective d.naturalCoordinates (by
    intro v
    obtain ⟨w,hw⟩ := d.projection_onto v.toAdd
    obtain ⟨u,hu⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    exact ⟨u,by
      change Multiplicative.ofAdd (d.projection (d.coordinates u).toAdd) = v
      rw [hu]
      exact hw⟩)

omit [Finite G] in
/-- The isomorphism commutes with the literal quotient map. -/
theorem centralQuotientEquiv_mk (u : normalizerMoved L) :
    d.centralQuotientEquiv (QuotientGroup.mk' d.naturalCoordinates.ker u) =
      Multiplicative.ofAdd (d.projection (d.coordinates u).toAdd) := by
  simp only [centralQuotientEquiv,naturalCoordinates]
  rfl

omit [Finite G] in
/-- A full Sylow of the marked component occurs in the actual C_L(u) image. -/
theorem centralizer_contains_component_sylow
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (u : normalizerMoved L) :
    ∃ S : Sylow 2 SL, (S : Subgroup SL) ≤
      ((centralizer ({(u : G)} : Set G)).subgroupOf L).map d.component := by
  obtain ⟨S,hS⟩ := (d.naturalCover hmoved).exists_component_sylow_fixed (d.coordinates u).toAdd
  refine ⟨S,?_⟩
  intro l hl
  obtain ⟨k,rfl⟩ := d.onto l
  exact ⟨k,(d.component_fixes_iff k u).mp (hS _ hl),rfl⟩

/-- The source U has the genuine orthogonal covering map with its full LT-action. -/
theorem source_orthogonal_cover
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ (ζ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) CoverSpace)
      (f : CoverAction.IntertwiningMap d.representation),
      Function.Surjective f ∧
      (∀ a l u, ζ a (CoverAction l u) = CoverAction (d.conjugation a l) (ζ a u)) ∧
      (∀ a u, CoverProjection (ζ a u) = d.naturalActor a (CoverProjection u)) ∧
      (∀ u, d.projection (f u) = CoverProjection u) ∧
      (∀ a u, f (ζ a u) = d.actor a (f u)) := by
  let : Finite W := Finite.of_equiv (normalizerMoved L)
    (d.coordinates.toEquiv.trans Multiplicative.toAdd)
  exact (d.sourceCover h hL hn).exists_original_orthogonal_cover

/-- In the rank-two kernel case, the same source map is an isomorphism of
modules, with the original LT-action and natural quotient unchanged. -/
theorem source_orthogonal_equiv
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hk : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2) :
    ∃ (ζ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) CoverSpace)
      (e : CoverAction.Equiv d.representation),
      (∀ a l u, ζ a (CoverAction l u) = CoverAction (d.conjugation a l) (ζ a u)) ∧
      (∀ a u, CoverProjection (ζ a u) = d.naturalActor a (CoverProjection u)) ∧
      (∀ u, d.projection (e u) = CoverProjection u) ∧
      (∀ a u, e (ζ a u) = d.actor a (e u)) := by
  let : Finite W := Finite.of_equiv (normalizerMoved L)
    (d.coordinates.toEquiv.trans Multiplicative.toAdd)
  exact (d.sourceCover h hL hn).exists_original_orthogonal_equiv hk

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
