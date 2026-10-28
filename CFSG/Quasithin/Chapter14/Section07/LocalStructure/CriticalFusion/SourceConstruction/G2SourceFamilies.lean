module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourcePath
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Faithful commutator families on the original G₂ section

The order-two flag point is disjoint from a partner that does not contain it.
Consequently the original section coordinates reflect inclusion and equality
for subgroups lying in both U and that partner. The same observation lifts
fixed spaces to actual centralizers and recovers each commutator subgroup
as Uα ∩ (C V₁). It also preserves subgroup orders and family cardinalities.

Applied to the original critical path, normalization of Uα is proved from
its geodesic. The module-family equality in 14.7.55(8) then lifts to the
ambient equality used in formula (d). This is a conditional lifting step:
the model-family calculation on this action and the noncontainment from
14.7.62(1) are still to be supplied by the G₂ source argument.

The families indexed by all actors contain the trivial subgroup. We delete
that member on both sides when forming the nontrivial four-group family;
this distinguishes the two conventions used in printed formula (d).

Source: Aschbacher–Smith, 14.7.62 and the proof of 14.7.53, formulas
(a)–(d), printed pp.1068–1069.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {V : Subgroup G}
  (F : InvariantFlag T V 3)

/-- The source noncontainment makes the order-two point disjoint from the partner. -/
theorem point_disjoint (A : Subgroup G) (hpoint : ¬ F.Vi 1 ≤ A) :
    Disjoint (F.Vi 1) A := by
  let : Fact (Nat.card (F.Vi 1)).Prime := ⟨by rw [F.card 1 (by decide)]; decide⟩
  rcases (A.subgroupOf (F.Vi 1)).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply disjoint_iff.mpr
    have hh := congrArg (map (F.Vi 1).subtype) hb
    simpa only [subgroupOf_map_subtype, Subgroup.map_bot, inf_comm] using hh
  · exact (hpoint (fun x hx => show (⟨x,hx⟩ : F.Vi 1) ∈ A.subgroupOf (F.Vi 1) from
      ht ▸ mem_top _)).elim

variable {F} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)

/-- The actual quotient coordinates are injective on the partner intersection. -/
theorem coordinates_injective_on_partner (A : Subgroup G)
    (hpoint : ¬ F.Vi 1 ≤ A) :
    Set.InjOn c.coordinates {x : F.U | (x : G) ∈ A} := by
  intro x hx y hy he
  have hz : ((x * y⁻¹ : F.U) : G) ∈ F.Vi 1 := by
    apply (c.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have ha : ((x * y⁻¹ : F.U) : G) ∈ A := A.mul_mem hx (A.inv_mem hy)
  have heq := disjoint_def.mp (point_disjoint F A hpoint) hz ha
  apply Subtype.ext
  exact mul_inv_eq_one.mp heq

/-- On the common intersection, inclusion of coordinate images reflects inclusion. -/
theorem imageSpace_le_iff (A B C : Subgroup G) (hpoint : ¬ F.Vi 1 ≤ A)
    (hBU : B ≤ F.U) (_hCU : C ≤ F.U) (hBA : B ≤ A) (hCA : C ≤ A) :
    c.imageSpace B ≤ c.imageSpace C ↔ B ≤ C := by
  constructor
  · intro hi b hb
    let bU : F.U := ⟨b,hBU hb⟩
    have hm := hi ((c.mem_imageSpace_iff B _).mpr ⟨bU,hb,rfl⟩)
    obtain ⟨x,hx,he⟩ := (c.mem_imageSpace_iff C _).mp hm
    have hxb : x = bU := coordinates_injective_on_partner c A hpoint
      (hCA hx) (hBA hb) (Multiplicative.toAdd.injective he)
    have hxv : (x : G) = b := congrArg Subtype.val hxb
    exact hxv ▸ hx
  · exact c.imageSpace_mono

/-- Two subgroups of the common intersection with the same image are equal. -/
theorem imageSpace_eq_iff (A B C : Subgroup G) (hpoint : ¬ F.Vi 1 ≤ A)
    (hBU : B ≤ F.U) (hCU : C ≤ F.U) (hBA : B ≤ A) (hCA : C ≤ A) :
    c.imageSpace B = c.imageSpace C ↔ B = C := by
  simp only [le_antisymm_iff,
    imageSpace_le_iff c A B C hpoint hBU hCU hBA hCA,
    imageSpace_le_iff c A C B hpoint hCU hBU hCA hBA]

include c in
/-- Centralizing modulo the point is actual centralization when the commutator
lies in the disjoint partner. Normality is relative to U. -/
theorem commutatorPreimage_eq_centralizer (A : Subgroup G)
    (hpoint : ¬ F.Vi 1 ≤ A) (hUA : F.U ≤ normalizer (A : Set G)) :
    commutatorPreimage F.U A (F.Vi 1) = F.U ⊓ centralizer (A : Set G) := by
  have hUZ : F.U ≤ normalizer (F.Vi 1 : Set G) := c.section_le
  have hcomm : ⁅commutatorPreimage F.U A (F.Vi 1), A⁆ ≤ ⊥ := by
    exact (le_inf (commutator_commutatorPreimage_le F.U A (F.Vi 1) hUZ)
      (le_normalizer_iff_commutator_le_right.mp
        ((commutatorPreimage_le F.U A (F.Vi 1)).trans hUA))).trans
      (point_disjoint F A hpoint).le_bot
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le _ _ _) ?_
    exact (commutator_eq_bot_iff_le_centralizer).mp (bot_unique hcomm)
  · apply le_commutatorPreimage inf_le_left
    exact ((commutator_eq_bot_iff_le_centralizer).mpr inf_le_right).le.trans bot_le

/-- The fixed-space lifting used in the proof of 14.7.62(3). -/
theorem fixedSpace_eq_centralizer_image (A : Subgroup G) (hAH : A ≤ F.H)
    (hpoint : ¬ F.Vi 1 ≤ A) (hUA : F.U ≤ normalizer (A : Set G)) :
    fixedSpace ρ (A.subgroupOf F.H) = c.imageSpace (F.U ⊓ centralizer (A : Set G)) := by
  rw [← c.fixed_image_eq A hAH c.section_le,
    commutatorPreimage_eq_centralizer c A hpoint hUA]

/-- Surjectivity of the original coordinates gives the entire section space. -/
theorem imageSpace_U : c.imageSpace F.U = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨x,hx⟩ := c.onto (Multiplicative.ofAdd w)
  exact (c.mem_imageSpace_iff F.U w).mpr
    ⟨x,x.property,congrArg Multiplicative.toAdd hx⟩

/-- Adding the actual section denominator does not change its image. -/
theorem imageSpace_sup_point (R : Subgroup G) (hRU : R ≤ F.U) :
    c.imageSpace (R ⊔ F.Vi 1) = c.imageSpace R := by
  have hk : c.coordinates.ker.map c.coordinates = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  unfold BinaryConjugationSection.imageSpace
  rw [subgroupOf_sup hRU c.kernel_le, Subgroup.map_sup, ← c.kernel_eq, hk, sup_bot_eq]

include c in
/-- Recover the unique lift in the partner from the full quotient preimage. -/
theorem partner_inf_sup_point (A R : Subgroup G) (hpoint : ¬ F.Vi 1 ≤ A)
    (hRU : R ≤ F.U) (hRA : R ≤ A) : A ⊓ (R ⊔ F.Vi 1) = R := by
  have hle : A ⊓ (R ⊔ F.Vi 1) ≤ F.U :=
    inf_le_right.trans (sup_le hRU c.kernel_le)
  apply le_antisymm
  · apply (imageSpace_le_iff c A _ R hpoint hle hRU inf_le_left hRA).mp
    exact (c.imageSpace_mono (show A ⊓ (R ⊔ F.Vi 1) ≤ R ⊔ F.Vi 1 from inf_le_right)).trans_eq
      (imageSpace_sup_point c R hRU)
  · exact le_inf hRA le_sup_left

/-- The quotient does not change the order of a subgroup in the partner. -/
theorem imageSpace_card (A C : Subgroup G) (hpoint : ¬ F.Vi 1 ≤ A)
    (hCU : C ≤ F.U) (hCA : C ≤ A) : Nat.card (c.imageSpace C) = Nat.card C := by
  let f : C → c.imageSpace C := fun x =>
    ⟨(c.coordinates ⟨x,hCU x.property⟩).toAdd,
      (c.mem_imageSpace_iff C _).mpr ⟨⟨x,hCU x.property⟩,x.property,rfl⟩⟩
  have hi : Function.Injective f := by
    intro x y he
    have heq : c.coordinates ⟨x,hCU x.property⟩ = c.coordinates ⟨y,hCU y.property⟩ :=
      Multiplicative.toAdd.injective (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun z : F.U => (z : G))
      (coordinates_injective_on_partner c A hpoint (hCA x.property) (hCA y.property) heq))
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨x,hx,he⟩ := (c.mem_imageSpace_iff C v.val).mp v.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

/-- A two-dimensional nonzero commutator image is an actual four-group,
without adding the point subgroup to its lift. -/
theorem card_four_of_image_finrank [Finite G] (A C : Subgroup G)
    (hpoint : ¬ F.Vi 1 ≤ A) (hCU : C ≤ F.U) (hCA : C ≤ A)
    (hdim : Module.finrank (ZMod 2) (c.imageSpace C) = 2) : Nat.card C = 4 := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  rw [← imageSpace_card c A C hpoint hCU hCA,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
  decide

/-- The faithful quotient also preserves the cardinality of a whole family
of commutator subgroups, as opposed to just each member's order. -/
theorem family_card (A : Subgroup G) (hpoint : ¬ F.Vi 1 ≤ A)
    (family : Set (Subgroup G)) (hU : ∀ C ∈ family, C ≤ F.U)
    (hA : ∀ C ∈ family, C ≤ A) :
    Nat.card family = Nat.card (c.imageSpace '' family) := by
  apply Nat.card_congr
  exact Equiv.Set.imageOfInjOn c.imageSpace family
    (fun C hC D hD he => (imageSpace_eq_iff c A C D hpoint
      (hU C hC) (hU D hD) (hA C hC) (hA D hD)).mp he)

/-- Formula (d) is an equality of actual subgroups, once the module-family
calculation of 14.7.55(8) and the noncontainment of 14.7.62(1) are available.
Both sides include the trivial subgroup; deletion of that member is separate. -/
theorem commutator_families_of_linear_families (A B R : Subgroup G)
    (hAH : A ≤ F.H) (hBA : B ≤ A) (hRU : R ≤ F.U)
    (hUA : F.U ≤ normalizer (A : Set G)) (hpoint : ¬ F.Vi 1 ≤ A)
    (hfamilies :
      {P | ∃ b ∈ B, P = subspaceCommutator ρ ⊤ ((zpowers b).subgroupOf F.H)} =
      {P | ∃ w ∈ R, P = subspaceCommutator ρ (c.imageSpace (zpowers w))
        (A.subgroupOf F.H)}) :
    {C | ∃ b ∈ B, C = ⁅F.U,zpowers b⁆} = {C | ∃ w ∈ R, C = ⁅A,zpowers w⁆} := by
  have left_bounds (b : G) (hb : b ∈ B) : ⁅F.U,zpowers b⁆ ≤ F.U ∧ ⁅F.U,zpowers b⁆ ≤ A := by
    have hbA : zpowers b ≤ A := zpowers_le.mpr (hBA hb)
    exact ⟨le_normalizer_iff_commutator_le_left.mp ((hbA.trans hAH).trans c.normalized),
      (commutator_mono le_rfl hbA).trans (le_normalizer_iff_commutator_le_right.mp hUA)⟩
  have right_bounds (w : G) (hw : w ∈ R) : ⁅A,zpowers w⁆ ≤ F.U ∧ ⁅A,zpowers w⁆ ≤ A := by
    have hwU : zpowers w ≤ F.U := zpowers_le.mpr (hRU hw)
    exact ⟨(commutator_mono le_rfl hwU).trans
        (le_normalizer_iff_commutator_le_right.mp (hAH.trans c.normalized)),
      le_normalizer_iff_commutator_le_left.mp (hwU.trans hUA)⟩
  have left_image (b : G) (hb : b ∈ B) : c.imageSpace ⁅F.U,zpowers b⁆ =
      subspaceCommutator ρ ⊤ ((zpowers b).subgroupOf F.H) := by
    rw [commutator_comm, c.imageSpace_commutator _ _
      ((zpowers_le.mpr (hBA hb)).trans hAH) le_rfl, imageSpace_U c]
  have right_image (w : G) (hw : w ∈ R) : c.imageSpace ⁅A,zpowers w⁆ =
      subspaceCommutator ρ (c.imageSpace (zpowers w)) (A.subgroupOf F.H) :=
    c.imageSpace_commutator _ _ hAH (zpowers_le.mpr (hRU hw))
  ext C
  constructor
  · rintro ⟨b,hb,rfl⟩
    have hm : c.imageSpace ⁅F.U,zpowers b⁆ ∈
        {P | ∃ b ∈ B, P = subspaceCommutator ρ ⊤ ((zpowers b).subgroupOf F.H)} :=
      ⟨b,hb,left_image b hb⟩
    rw [hfamilies] at hm
    obtain ⟨w,hw,he⟩ := hm
    refine ⟨w,hw,(imageSpace_eq_iff c A _ _ hpoint
      (left_bounds b hb).1 (right_bounds w hw).1
      (left_bounds b hb).2 (right_bounds w hw).2).mp ?_⟩
    exact he.trans (right_image w hw).symm
  · rintro ⟨w,hw,rfl⟩
    have hm : c.imageSpace ⁅A,zpowers w⁆ ∈
        {P | ∃ w ∈ R, P = subspaceCommutator ρ (c.imageSpace (zpowers w))
          (A.subgroupOf F.H)} := ⟨w,hw,right_image w hw⟩
    rw [← hfamilies] at hm
    obtain ⟨b,hb,he⟩ := hm
    refine ⟨b,hb,(imageSpace_eq_iff c A _ _ hpoint
      (right_bounds w hw).1 (left_bounds b hb).1
      (right_bounds w hw).2 (left_bounds b hb).2).mp ?_⟩
    exact he.trans (left_image b hb).symm

/-- The nontrivial family used for the four-cycle omits the zero commutator
on both sides of the source symmetry. -/
theorem nontrivial_commutator_families (A B R : Subgroup G)
    (hAH : A ≤ F.H) (hBA : B ≤ A) (hRU : R ≤ F.U)
    (hUA : F.U ≤ normalizer (A : Set G)) (hpoint : ¬ F.Vi 1 ≤ A)
    (hfamilies :
      {P | ∃ b ∈ B, P = subspaceCommutator ρ ⊤ ((zpowers b).subgroupOf F.H)} =
      {P | ∃ w ∈ R, P = subspaceCommutator ρ (c.imageSpace (zpowers w))
        (A.subgroupOf F.H)}) :
    {C | C ≠ ⊥ ∧ ∃ b ∈ B, C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ w ∈ R, C = ⁅A,zpowers w⁆} := by
  have he := commutator_families_of_linear_families c A B R hAH hBA hRU hUA hpoint hfamilies
  ext C
  exact and_congr_right (fun _ => Set.ext_iff.mp he C)

/-- Application of the family lift to the actual source critical path. The
normalizer containment is discharged by the geodesic argument, and every
member is recovered as the partner intersection with its point extension.
This supplies the lifting implication in formula (d); its explicit module
identity and the earlier noncontainment must still be proved by this owner. -/
theorem source_common_family [Finite G] {L : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (B R : Subgroup G) (hBA : B ≤ path.Uα) (hRU : R ≤ F.U)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα)
    (hfamilies :
      {P | ∃ b ∈ B, P = subspaceCommutator ρ ⊤ ((zpowers b).subgroupOf F.H)} =
      {P | ∃ w ∈ R, P = subspaceCommutator ρ (c.imageSpace (zpowers w))
        (path.Uα.subgroupOf F.H)}) :
    ({C | C ≠ ⊥ ∧ ∃ b ∈ B, C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ w ∈ R, C = ⁅path.Uα,zpowers w⁆}) ∧
    (∀ b ∈ B, path.Uα ⊓ (⁅F.U,zpowers b⁆ ⊔ F.Vi 1) = ⁅F.U,zpowers b⁆) ∧
    fixedSpace ρ (path.Uα.subgroupOf F.H) =
      c.imageSpace (F.U ⊓ centralizer (path.Uα : Set G)) := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hn := normalizes_partner h path
  refine ⟨nontrivial_commutator_families c path.Uα B R hAH hBA hRU hn hpoint
    hfamilies, ?_, fixedSpace_eq_centralizer_image c path.Uα hAH hpoint hn⟩
  intro b hb
  have hbA : zpowers b ≤ path.Uα := zpowers_le.mpr (hBA hb)
  exact partner_inf_sup_point c path.Uα _ hpoint
    (le_normalizer_iff_commutator_le_left.mp ((hbA.trans hAH).trans c.normalized))
    ((commutator_mono le_rfl hbA).trans (le_normalizer_iff_commutator_le_right.mp hn))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
