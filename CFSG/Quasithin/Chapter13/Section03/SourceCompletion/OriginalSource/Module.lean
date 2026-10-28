module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalSource
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeNonsplit
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedFreeRows

/-!
# Constructing the original unitary marking from the module theorem

The seven literal module rows leave only the binary G₂ row when L/O₂(L)
has order 6048. The earlier 13.3.2 fixed-space clause rules out a nonzero
fixed space: it would identify the same faithful quotient with A₆. Thus
the central quotient projection is an equivariant isomorphism on the whole
original chosen module. The first isomorphism theorem for the actual
L-action identifies its induced automizer, preserving the quotient map.

The resulting marking is the one consumed by the completed original-source
exclusion in `OriginalSource.Applications`. This proves the adapter, not the
independent earlier 12.2.2 module theorem or 13.3.2 fixed-space clause.
Source: Aschbacher--Smith 12.2.2(3), p.795, and 13.3.2(3),13.3.16, pp.885,894.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterE OriginalPlaneCentralizers
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem unitary_chosen_fixed_bot
    (h : Hypothesis1331 T L) (D : ChosenModule T L V)
    (e₀ : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (fixed : OriginalFixedModule1332At T L) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  classical
  let := D.actionCentralizer_normal
  let := Atlas.G2.isSimple_commutator_binary
  by_contra hn
  obtain ⟨a⟩ := fixed h L h.local_component V D hn
  have he := Nat.card_congr (((D.coreToFaithfulEquiv e₀.isSimpleGroup).trans
    a.groupEquiv).symm.trans e₀).toEquiv
  rw [nat_card_alternatingGroup, Nat.card_fin,
    Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at he
  norm_num [Nat.factorial] at he

private theorem unitary_chosen_g2_row
    (D : ChosenModule T L V) (rows : ModuleAlternatives1222 D)
    (e₀ : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived) :
    Nonempty (ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) := by
  let := D.elementary
  let := D.actionCentralizer_normal
  let := Atlas.G2.isSimple_commutator_binary
  have hc : Nat.card (L ⧸ pCore 2 L) = 6048 :=
    (Nat.card_congr e₀.toEquiv).trans
      (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))
  have hf : Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) = 6048 :=
    (Nat.card_congr (D.coreToFaithfulEquiv e₀.isSimpleGroup).symm.toEquiv).trans hc
  have hl (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    rw [BinaryLinear.card_SL] at he
    rcases hn with rfl | rfl | rfl <;>
      norm_num [BinaryLinear.order, Fin.prod_univ_succ] at he
  cases rows with
  | linear n hn e => exact (hl n hn e.groupEquiv).elim
  | linearThreeExtension e _ _ => exact (hl 3 (by simp) e).elim
  | linearFiveExterior e _ _ => exact (hl 5 (by simp) e).elim
  | alternating n hlo hhi e =>
    have he := (Nat.card_congr e.groupEquiv.toEquiv).symm.trans hf
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_fin] at he <;>
      norm_num [Nat.factorial] at he
  | alternatingSevenFour e _ =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hf
    rw [nat_card_alternatingGroup, Nat.card_fin] at he
    norm_num [Nat.factorial] at he
  | g2 e => exact ⟨e⟩
  | tripleSix e _ _ _ =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    rw [Atlas.Codes.hexEven_card] at he
    norm_num at he

/-- The source module row produces the natural action on the whole original V. -/
theorem unitary_chosen_natural_marking
    [IsElementaryAbelian 2 V]
    (h : Hypothesis1331 T L) (D : ChosenModule T L V)
    (e₀ : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (rows : ModuleAlternatives1222 D) (fixed : OriginalFixedModule1332At T L) :
    ∃ (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
      (E : Additive V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)),
      ∀ (l : inducedAutomizer V L) v,
        E (automizerRepresentation V l v) =
          Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v) := by
  obtain ⟨a⟩ := unitary_chosen_g2_row D rows e₀
  have hc := unitary_chosen_fixed_bot h D e₀ fixed
  let := Atlas.G2.isSimple_commutator_binary
  let d : D.space ≃+ Additive V := D.spaceEquiv.toAdditive
  let c : D.space ≃ₗ[ZMod 2] Additive V :=
    { d with map_smul' := ZMod.map_smul d }
  let E := c.symm.trans ((RecognitionSource.fixedFreeQuotientEquiv D hc).trans a.linearEquiv)
  let q : L →* inducedAutomizer V L :=
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion D.normalizes)).codRestrict _
      (fun x => mem_map_of_mem V.normalizerMonoidHom.rangeRestrict x.property)
  have hq : Function.Surjective q := by
    rintro ⟨x,n,hn,rfl⟩
    exact ⟨⟨n.val,hn⟩,rfl⟩
  have hker : q.ker = pCore 2 L := by
    rw [← D.centralizer_eq_core_of_simple e₀.isSimpleGroup]
    ext l
    change q l = 1 ↔ (l : G) ∈ centralizer (V : Set G)
    constructor
    · intro hl v hv
      have hh := congrArg (fun z : inducedAutomizer V L =>
        ((z.val.val) ⟨v,hv⟩ : G)) hl
      change (l : G) * v * (l : G)⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hl
      apply Subtype.ext
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((hl v.val v.property).symm)
  let b : (L ⧸ pCore 2 L) ≃* inducedAutomizer V L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hb (l : L) : b (QuotientGroup.mk' (pCore 2 L) l) = q l := rfl
  let e := b.symm.trans a.groupEquiv
  refine ⟨e,E,?_⟩
  intro l v
  obtain ⟨x,rfl⟩ := hq l
  have he : e (q x) = a.groupEquiv (QuotientGroup.mk' (pCore 2 L) x) := by
    rw [← hb, MulEquiv.trans_apply, b.symm_apply_apply]
  rw [he]
  have hv : c.symm (automizerRepresentation V (q x) v) = D.chosenAction x (c.symm v) := by
    apply c.injective
    rw [c.apply_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x : G) * (v.toMul : G) * (x : G)⁻¹ =
      (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction x (c.symm v))) : G)
    rw [D.spaceEquiv_apply]
    have hh := D.spaceEquiv_apply (c.symm v)
    have hvv : (c (c.symm v)).toMul = v.toMul := congrArg Additive.toMul (c.apply_symm_apply v)
    change (D.spaceEquiv (Multiplicative.ofAdd (c.symm v))) = v.toMul at hvv
    rw [hvv] at hh
    change _ = (x : G) * ((c.symm v).val.toMul.val : G) * (x : G)⁻¹
    rw [hh]
  change a.linearEquiv (RecognitionSource.fixedFreeQuotientEquiv D hc
      (c.symm (automizerRepresentation V (q x) v))) = _
  rw [hv, RecognitionSource.fixedFreeQuotientEquiv_action]
  exact a.intertwines (QuotientGroup.mk' (pCore 2 L) x)
    (RecognitionSource.fixedFreeQuotientEquiv D hc (c.symm v))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
