module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.JankoFourRudvalis.Tools
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.SpecificGroups.Janko4.Model
public import Theory.SpecificGroups.Rudvalis.Model.Basic

/-!
# Separation of the J4 and Rudvalis inner residual rows

We prove the conditional row comparison used in Aschbacher–Smith 16.5.6(4),
printed p.1197 of the combined manuscript of 1 March 2004. The universal
marked table inputs concern the actual Janko4 and Rudvalis carriers and
actual extensions or isomorphisms from 16.1.5(9),(11), printed p.1172.
They remain explicit obligations of the earlier intrinsic-table owners.

For J4, the first row retains its extraspecial kernel of order 2^13 and the
full covering extension 3.M22.2. Its perfect triple-cover section has order
divisible by 27 and survives both residual operations. The other row is an
E2048 extension by the actual Aut(M22), whose order is not divisible by 27.
The input fragment does not need the first kernel's plus type or the outer
action on the triple cover; those further assertions remain with the exact
table owner. In particular no literal MulAut of a triple cover is substituted.

For Ru, the successive E32 and E64 kernels and S5 quotient exclude seven
from the central row. The actual E4 × Sz(8) row contains seven. This prime
survives both operations of Notation 16.5.5.

All central covering kernels are retained: trivial odd core makes them
two-groups. Consequently no additional restriction from 16.1.2, no splitting
premise from I.2.2(7), and no exclusion of an exceptional model are needed
for these comparisons. Ambient actors are only assumed to normalize L;
innerness is a statement about their induced actions.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.Mathieu BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoFourRudvalis

abbrev BinaryElementary (n : ℕ) := Multiplicative (Fin n → ZMod 2)

private theorem binaryElementary_card (n : ℕ) : Nat.card (BinaryElementary n) = 2 ^ n := by
  change Nat.card (Fin n → ZMod 2) = _
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- The extension data used from the first J4 row. The perfect triple cover
is retained as a group, its center, and its actual M22 quotient. The full
quotient is an extension of this cover by C2, never its automorphism group.
The comparison only uses the displayed fragment of the source row; the
extraspecial plus-type assertion belongs to the intrinsic table owner. -/
structure JankoCentralRow (C : Type*) [Group C] where
  Kernel : Type
  [kernelGroup : Group Kernel]
  kernel_extraspecial : IsExtraspecial 2 Kernel
  kernel_card : Nat.card Kernel = 2 ^ 13
  Quotient : Type
  [quotientGroup : Group Quotient]
  Cover : Type
  [coverGroup : Group Cover]
  [coverPerfect : Group.IsPerfect Cover]
  cover_center_card : Nat.card (center Cover) = 3
  cover_quotient : Cover ⧸ center Cover ≃* M22
  outerExtension : GroupExtension Cover Quotient (Multiplicative (ZMod 2))
  extension : GroupExtension Kernel C Quotient

attribute [instance] JankoCentralRow.kernelGroup JankoCentralRow.quotientGroup
  JankoCentralRow.coverGroup JankoCentralRow.coverPerfect

/-- Universal marked table inputs for the comparison, on the actual J4 model.
They are structural inputs, not assertions of the unfinished intrinsic table. -/
structure JankoTable where
  inner : ∀ a : MulAut Janko4.Model, orderOf a = 2 → ∃ x, a = MulAut.conj x
  central : ∀ x : Janko4.Model, orderOf x = 2 → TwoCentral x →
    Nonempty (JankoCentralRow (MulAut.conj x).fixedSubgroup)
  noncentral : ∀ x : Janko4.Model, orderOf x = 2 → ¬ TwoCentral x →
    Nonempty (GroupExtension (BinaryElementary 11) (MulAut.conj x).fixedSubgroup (MulAut M22))

/-- The successive E32 and E64 kernels in the central Ru row; normality is
relative to the indicated group in each genuine short exact sequence. -/
structure RudvalisCentralRow (C : Type*) [Group C] where
  Quotient : Type
  [quotientGroup : Group Quotient]
  extension : GroupExtension (BinaryElementary 5) C Quotient
  quotientExtension : GroupExtension (BinaryElementary 6) Quotient (Equiv.Perm (Fin 5))

attribute [instance] RudvalisCentralRow.quotientGroup

/-- The two inner rows and their actual Sylow markings on the degree-4060 model. -/
structure RudvalisTable where
  inner : ∀ a : MulAut Rudvalis.Model, orderOf a = 2 → ∃ x, a = MulAut.conj x
  central : ∀ x : Rudvalis.Model, orderOf x = 2 → TwoCentral x →
    Nonempty (RudvalisCentralRow (MulAut.conj x).fixedSubgroup)
  noncentral : ∀ x : Rudvalis.Model, orderOf x = 2 → ¬ TwoCentral x →
    Nonempty ((MulAut.conj x).fixedSubgroup ≃* BinaryElementary 2 × SuzukiMatrixGroup 1)

private theorem autM22_card : Nat.card (MulAut M22) = 887040 := by
  rw [← Nat.card_congr (MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩).toEquiv]
  exact m22DesignAut_order

/-- The third factor of three comes from the genuine covering kernel. -/
theorem janko_cover_card {C : Type*} [Group C] (d : JankoCentralRow C) :
    Nat.card d.Cover = 1330560 := by
  rw [card_eq_card_quotient_mul_card_subgroup (center d.Cover),
    Nat.card_congr d.cover_quotient.toEquiv, d.cover_center_card, m22_order]

/-- The second full row has exactly two factors of three in its order. -/
theorem janko_noncentral_not_dvd_27 {C : Type*} [Group C]
    (d : GroupExtension (BinaryElementary 11) C (MulAut M22)) :
    ¬ 27 ∣ Nat.card C := by
  rw [extension_card d, autM22_card, binaryElementary_card]
  norm_num

/-- Seven is absent from the full central Ru row, before either residual. -/
theorem rudvalis_central_not_dvd_seven {C : Type*} [Group C]
    (d : RudvalisCentralRow C) : ¬ 7 ∣ Nat.card C := by
  rw [extension_card d.extension, extension_card d.quotientExtension,
    binaryElementary_card, binaryElementary_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The actual Sz(8) factor supplies seven in the noncentral row. -/
theorem rudvalis_noncentral_dvd_seven {C : Type*} [Group C]
    (e : C ≃* BinaryElementary 2 × SuzukiMatrixGroup 1) : 7 ∣ Nat.card C := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, binaryElementary_card,
    suzukiMatrixGroup_card 1 (by decide)]
  norm_num

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} [IsQuasisimple L]

/-- Conditional comparison for the actual J4 quotient. The central perfect
triple-cover section survives both residuals; odd divisibility through all
central two-kernels excludes that section's third factor of three in the
other row. Neither residual is assumed perfect or identified in advance. -/
theorem janko_no_equiv (table : JankoTable) (hodd : pPrimeCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Janko4.Model) (u v : normalizer (L : Set G))
    (_hu : orderOf u.val = 2) (_hv : orderOf v.val = 2)
    (hu2 : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  obtain ⟨x, hx, hax, hcx⟩ := marked_model_involution e table.inner u hu2
  obtain ⟨y, hy, hay, hcy⟩ := marked_model_involution e table.inner v hv2
  have hc : Nonempty (JankoCentralRow
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup) := by
    rw [hax]
    exact table.central x hx (hcx.mp hu)
  have hn : Nonempty (GroupExtension (BinaryElementary 11)
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup (MulAut M22)) := by
    rw [hay]
    exact table.noncentral y hy (fun h => hv (hcy.mpr h))
  obtain ⟨c⟩ := hc
  obtain ⟨n⟩ := hn
  let : Finite c.Quotient := Finite.of_surjective c.extension.rightHom c.extension.rightHom_surjective
  let : Finite c.Cover := Finite.of_injective c.outerExtension.inl c.outerExtension.inl_injective
  have hcover := perfect_section_dvd_modified hodd e u c.extension.rightHom
    c.extension.rightHom_surjective c.outerExtension.inl c.outerExtension.inl_injective
  have h27 : 27 ∣ Nat.card (modifiedCentralizerResidual L u.val) := by
    apply dvd_trans (b := Nat.card c.Cover) _ hcover
    rw [janko_cover_card c]
    norm_num
  rintro ⟨f⟩
  rw [Nat.card_congr f.toEquiv] at h27
  have hD := h27.trans (card_dvd_of_le (modifiedCentralizerResidual_le L v.val))
  exact janko_noncentral_not_dvd_27 n
    ((odd_dvd_twoResidual_iff_fixed hodd e v 27 (by decide)).mp hD)

/-- Conditional comparison for the actual Rudvalis quotient, including every
central cover with trivial odd core. The prime seven survives both operations
of Notation 16.5.5, so no cover-lifting or residual-identification premise is needed. -/
theorem rudvalis_no_equiv (table : RudvalisTable) (hodd : pPrimeCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Rudvalis.Model) (u v : normalizer (L : Set G))
    (_hu : orderOf u.val = 2) (_hv : orderOf v.val = 2)
    (hu2 : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  obtain ⟨x, hx, hax, hcx⟩ := marked_model_involution e table.inner u hu2
  obtain ⟨y, hy, hay, hcy⟩ := marked_model_involution e table.inner v hv2
  have hc : ¬ 7 ∣ Nat.card
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup := by
    rw [hax]
    obtain ⟨c⟩ := table.central x hx (hcx.mp hu)
    exact rudvalis_central_not_dvd_seven c
  have hn : 7 ∣ Nat.card
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup := by
    rw [hay]
    obtain ⟨c⟩ := table.noncentral y hy (fun h => hv (hcy.mpr h))
    exact rudvalis_noncentral_dvd_seven c
  intro h
  exact no_equiv_of_fixed_prime hodd e v u (by decide : Nat.Prime 7)
    (by decide) (by decide) hn hc (h.map MulEquiv.symm)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoFourRudvalis
