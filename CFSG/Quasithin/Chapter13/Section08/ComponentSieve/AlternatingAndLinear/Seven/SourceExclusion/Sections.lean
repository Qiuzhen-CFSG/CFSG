module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.CriticalReciprocity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Transport
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Passing the critical indices and commutators to U_H/V₁

The map from U_H/D to the quotient by the literal image of D is surjective,
so its binary dimension is bounded by log₂|U_H:D|. This discharges the
codimension premise of the three-pairs sieve from 13.8.8.

The inverse endpoint marking keeps |A₁|=2. Hence the image of A₁ in U_H/V₁
is zero or a line. Conjugation compatibility carries [D_H,Uγ] into that
image; in the zero case D_H is fixed. This constructs the full critical-line
alternative, even when A₁ is not contained in U_H. Relative normalization
of A₁ follows from its endpoint vertex, not ambient normality.

Source: Aschbacher–Smith, F.9.13, 13.8.8 and the proof of 13.8.22,
printed pp.322,949,957 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
open CriticalGeometry PairsBranch
variable {G : Type*} [Group G] [Finite G]
  {L T H V V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]

private theorem binary_finrank {F : Type*} [AddCommGroup F] [Module (ZMod 2) F] [Finite F] :
    Module.finrank (ZMod 2) F = Nat.log 2 (Nat.card F) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow Nat.one_lt_two]

/-- Quotienting by V₁ cannot increase the codimension of the image of D. -/
theorem source_codimension_le (D : Subgroup G) (hD : D ≤ Source.UH H V₃) :
    Module.finrank (ZMod 2) ((Additive (Source.Utilde H V₃ V₁)) ⧸
      sourceImage H V₃ V₁ D) ≤ Nat.log 2 (D.relIndex (Source.UH H V₃)) := by
  let U := Source.UH H V₃
  let q := QuotientGroup.mk' (V₁.subgroupOf U)
  let f : Additive U →ₗ[ZMod 2] Additive (Source.Utilde H V₃ V₁) :=
    { q.toAdditive with map_smul' := ZMod.map_smul q.toAdditive }
  let B : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 (D.subgroupOf U).toAddSubgroup
  let C := sourceImage H V₃ V₁ D
  have hBC : B ≤ C.comap f := fun x hx => ⟨x.toMul, hx, rfl⟩
  let F := B.mapQ C f hBC
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨v, rfl⟩ := C.mkQ_surjective y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) v.toMul
    exact ⟨B.mkQ (Additive.ofMul x), congrArg C.mkQ (congrArg Additive.ofMul hx)⟩
  have hB : Module.finrank (ZMod 2) B = Nat.log 2 (Nat.card D) := by
    rw [binary_finrank]
    change Nat.log 2 (Nat.card (D.subgroupOf U)) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv]
  have hU : Module.finrank (ZMod 2) (Additive U) = Nat.log 2 (Nat.card U) := binary_finrank
  have hd := B.finrank_quotient_add_finrank
  rw [hB, hU] at hd
  have hb : Module.finrank (ZMod 2) (Additive U ⧸ B) = Nat.log 2 (D.relIndex U) := by
    rw [← log_card_sub_log_card_eq_log_relIndex U D hD]
    omega
  exact (LinearMap.finrank_le_finrank_of_surjective hF).trans_eq hb

/-- The literal image of any subgroup has dimension at most its binary log-order. -/
theorem source_image_rank_le (A : Subgroup G) :
    Module.finrank (ZMod 2) (sourceImage H V₃ V₁ A) ≤ Nat.log 2 (Nat.card A) := by
  rw [binary_finrank]
  change Nat.log 2 (Nat.card ((A.subgroupOf (Source.UH H V₃)).map
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))))) ≤ _
  apply Nat.log_monotone
  have hm : Nat.card ((A.subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))) ≤
      Nat.card (A.subgroupOf (Source.UH H V₃)) := by
    exact Nat.card_le_card_of_surjective _
      ((QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))).subgroupMap_surjective _)
  apply hm.trans
  apply Nat.card_le_card_of_injective
    (fun a : A.subgroupOf (Source.UH H V₃) => (⟨a.val.val, a.property⟩ : A))
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : A => z.val) h

/-- The critical commutators descend to zero or the actual image of A₁,
which is a line when nonzero. No dimension-one seed assumption is used. -/
theorem source_critical_line
    (c : CriticalPair L T H V) (L₁ K : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (d : CriticalReciprocity.Earlier c L₁ K V₃ V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ) :
    sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)) ≤
      fixedSpace ρ (Source.starImage H (c.Ugamma V₃)) ∨
    IsAtom (sourceImage H V₃ V₁ (c.Aone V₁)) ∧
      ∀ x ∈ Source.starImage H (c.Ugamma V₃),
        ∀ u ∈ sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)),
          ρ x u - u ∈ sourceImage H V₃ V₁ (c.Aone V₁) := by
  let A := c.Aone V₁
  let D := Source.DH (Source.UH H V₃) (c.Ugamma V₃) A
  let C := sourceImage H V₃ V₁ A
  have hAcard : Nat.card A = 2 := by
    rw [show A = V₁.map (MulAut.conj (c.gb : G)).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj (c.gb : G)).injective, d.line_card]
  have hdim : Module.finrank (ZMod 2) C ≤ 1 := by
    have h := source_image_rank_le (H := H) (V₃ := V₃) (V₁ := V₁) A
    simpa only [hAcard, show Nat.log 2 2 = 1 from by decide] using h
  have hn : Source.UH H V₃ ≤ normalizer (A : Set G) :=
    (d.UH_le_terminal_core.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans
      (SectionActions.CriticalPair.normalizes_Aone c V₁ d.line_normalized)
  have hcomm : ⁅c.Ugamma V₃, D⁆ ≤ A := by
    rw [commutator_comm]
    exact commutator_commutatorPreimage_le _ _ _ hn
  have hdisp : ∀ x ∈ Source.starImage H (c.Ugamma V₃),
      ∀ u ∈ sourceImage H V₃ V₁ D, ρ x u - u ∈ C := by
    rintro x ⟨h, hh, rfl⟩ u ⟨v, hv, rfl⟩
    change ρ (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v)) -
      Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v) ∈ C
    rw [hρ]
    change (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) _) /
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v) ∈
      ((A.subgroupOf (Source.UH H V₃)).map
        (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))))
    rw [← map_div]
    apply mem_map_of_mem
    change (h.val * v.val * h.val⁻¹) / v.val ∈ A
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      hcomm (commutator_mem_commutator
        (show h.val ∈ c.Ugamma V₃ from hh) (show v.val ∈ D from hv))
  by_cases hz : C = ⊥
  · left
    intro u hu x
    have he := hdisp x x.property u hu
    rw [hz] at he
    exact sub_eq_zero.mp he
  · right
    refine ⟨Submodule.isAtom_iff_finrank_eq_one.mpr ?_, hdisp⟩
    have hp : 0 < Module.finrank (ZMod 2) C := by
      exact Nat.pos_of_ne_zero (fun he => hz (Submodule.finrank_eq_zero.mp he))
    change Module.finrank (ZMod 2) C = 1
    omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
