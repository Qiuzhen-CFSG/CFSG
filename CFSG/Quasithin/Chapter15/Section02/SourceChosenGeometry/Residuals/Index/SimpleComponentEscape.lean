module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.MathieuExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition.Core
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.Orbits
public import Theory.GroupTheory.CubicClosureSimple
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Equality-row escape for the remaining simple component models

Solvable cubic closure passes to subgroups and through two-group kernels.
A perfect simple quotient divisible by three therefore excludes containment
in the equality-row partner Mc. We apply this directly to the actual binary
L₄/L₅ components, binary L₃ components, alternating A₅/A₇ blocks and
even-field L₂ blocks. Each block's original Sylow-conjugate span contains
the original block, so its escape follows with the same literal embedding.

The actual model and source hypotheses supply simplicity, perfectness and
the factor three in each quotient order. No orbit-residual equality,
intrinsic-module movement, MS classification or plane-uniqueness packet
is assumed. This supplies the equality-row replacements for the remaining
normal-perfect escape applications in original 15.2.23; it does not prove
the full uniqueness theorem or construct its earlier geometric packet.

Source: Aschbacher--Smith, 15.2.23, printed pp.1114--1117,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChosenGeometry TerminalLinear PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B ZS I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

namespace ChosenGeometry

/-- A perfect simple section with a two-group kernel and a cubic element
cannot occur inside the actual equality-row partner. -/
theorem ResidualInput.no_simple_two_kernel_section_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {A L : Type*} [Group A] [Finite A] [Group L] [Finite L]
    [IsSimpleGroup L] [Group.IsPerfect L]
    (i : A →* Mc) (hi : Function.Injective i)
    (f : A →* L) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hd : 3 ∣ Nat.card L) : False :=
  cubic_closure_not_solvable_of_simple hd
    (solvable_cubic_closure_of_two_kernel f hf hk
      (solvable_cubic_closure_of_injective i hi (r.cubic_closure_solvable_of_eq he)))

/-- The original subgroup of I escapes Mc when its literal two-core
quotient is a perfect simple group of order divisible by three. -/
theorem ResidualInput.nested_simple_component_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (X : Subgroup I) [IsSimpleGroup (X ⧸ pCore 2 X)]
    [Group.IsPerfect (X ⧸ pCore 2 X)]
    (hd : 3 ∣ Nat.card (X ⧸ pCore 2 X)) : ¬ X.map I.subtype ≤ Mc := by
  intro hXM
  let i : X →* Mc := (I.subtype.comp X.subtype).codRestrict Mc
    (fun x => hXM (mem_map_of_mem I.subtype x.property))
  have hi : Function.Injective i := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Mc => (z : G)) hxy))
  exact r.no_simple_two_kernel_section_of_eq he i hi
    (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hd

/-- Both actual binary star rows escape Mc without the preceding
partner-residual equality or the normal-perfect reduction. -/
theorem ResidualInput.binary_linear_component_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup G} {n : ℕ} (b : BinaryBranch M I X n) : ¬ X ≤ Mc := by
  let : IsSimpleGroup (X ⧸ pCore 2 X) := b.coreQuotient_simple
  let : Group.IsPerfect (X ⧸ pCore 2 X) := b.source.quasisimple.toIsPerfect
  obtain ⟨e,_⟩ := b.parabolic
  let a := b.coreStarEquiv.trans (e.trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL
      (by rcases b.degree with rfl | rfl <;> decide)))
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr a.toEquiv,BinaryLinear.card_SL]
    rcases b.degree with rfl | rfl <;>
      norm_num [BinaryLinear.order,Fin.prod_univ_succ]
  intro hXM
  exact r.no_simple_two_kernel_section_of_eq he
    (inclusion hXM) (inclusion_injective hXM)
    (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hd

/-- The actual binary L₃ component escapes already from its core quotient.
No extra MS or intrinsic-movement premise is needed in the equality row. -/
theorem ResidualInput.linear_three_component_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) : ¬ X.map I.subtype ≤ Mc := by
  let : Group.IsPerfect X := hX.perfect
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
  apply r.nested_simple_component_not_le_partner_of_eq he X
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL]
  decide

/-- The original Sylow orbit of the binary L₃ component also escapes. -/
theorem ResidualInput.linear_three_blockOrbit_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) :
    ¬ planeBlockOrbit T ZS X ≤ Mc :=
  fun hXM => r.linear_three_component_not_le_partner_of_eq he hX e
    ((le_conjugateSpanBy _ _).trans hXM)

/-- Both nonsolvable alternating block rows escape using their actual
two-core quotient, with no residual identity or movement assumption. -/
theorem ResidualInput.alternating_block_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup I} {n : ℕ} (hn : n = 5 ∨ n = 7)
    (hb : ChapterC.IsAlternatingBlock X n) : ¬ X.map I.subtype ≤ Mc := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rcases hn with rfl | rfl <;> simp)⟩
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
  let : Group.IsPerfect (X ⧸ pCore 2 X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply r.nested_simple_component_not_le_partner_of_eq he X
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

/-- The full Sylow-conjugate span of an actual A₅ or A₇ block escapes Mc. -/
theorem ResidualInput.alternating_blockOrbit_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup I} {n : ℕ} (hn : n = 5 ∨ n = 7)
    (hb : ChapterC.IsAlternatingBlock X n) : ¬ planeBlockOrbit T ZS X ≤ Mc :=
  fun hXM => r.alternating_block_not_le_partner_of_eq he hn hb
    ((le_conjugateSpanBy _ _).trans hXM)

/-- Every original even-field L₂ block has a perfect simple core quotient
with a cubic element, so it escapes the equality-row partner. -/
theorem ResidualInput.l2_block_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup I} {n : ℕ} (hb : ChapterC.IsL2EvenBlock X n) :
    ¬ X.map I.subtype ≤ Mc := by
  let : IsSimpleGroup (X ⧸ pCore 2 X) :=
    (show ChapterC.IsChiZeroBlock X from Or.inl ⟨n,hb⟩).quotient_simple
  have hq : Group.IsPerfect (X ⧸ pCore 2 X) := by
    rcases hb.2.1.quotient with hp | hc
    · let := hp
      infer_instance
    · obtain ⟨F,_,_,hF,_,hm⟩ := hb.2.2
      obtain ⟨e⟩ := hm.quotient_iso
      rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two] at hc
      have hl : 4 ≤ Nat.card F := by
        rw [hF]
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by have hn := hb.1; omega : 2 ≤ n)
      have hh := Nat.mul_le_mul hl
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hl 2) 1)
      norm_num at hh
      omega
  let := hq
  apply r.nested_simple_component_not_le_partner_of_eq he X
  have hd := ChapterC.RankOne.ChiProduct.three_dvd_card_of_chi (Or.inl ⟨n,hb⟩)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 X)] at hd
  apply (Nat.prime_three.dvd_mul.mp hd).resolve_right
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  apply Nat.prime_three.coprime_iff_not_dvd.mp
  rw [hk]
  exact (by decide : Nat.Coprime 3 2).pow_right k

/-- The full Sylow-conjugate span of the original even-field L₂ block
escapes Mc, without imposing a single-component orbit. -/
theorem ResidualInput.l2_blockOrbit_not_le_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    {X : Subgroup I} {n : ℕ} (hb : ChapterC.IsL2EvenBlock X n) :
    ¬ planeBlockOrbit T ZS X ≤ Mc :=
  fun hXM => r.l2_block_not_le_partner_of_eq he hb
    ((le_conjugateSpanBy _ _).trans hXM)

end ChosenGeometry
end CFSG.Quasithin.Chapter15.Section02
