module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Basic
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import GorensteinWalter.PSL2KleinFourCentralizerEqSelf

/-!
# Rigidity from involution displacement

In SL₃(2), every elementary two-subgroup has rank at most two, and every
four-group is self-centralizing. If involutions displace at least two
dimensions, offenders therefore have rank and fixed codimension two.
Two offenders in one two-subgroup intersect; their common fixed space makes
their actions commute, so faithfulness and self-centrality identify them.

The final adapter uses the literal marked X action and the already constructed
offender on each actual edge. The displacement premise is still explicit.
Source: Meierfrankenfeld–Stellmacher (1993), printed p.877.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models

private theorem pGroup_card_le_eight (P : Subgroup SL) (hP : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have h := Subgroup.card_le_of_le hS
  have hc : Nat.card (S : Subgroup SL) = 8 := by
    rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  exact hc ▸ h

private theorem rank_two_card (A : Subgroup SL) (hA : IsElementaryAbelian 2 A)
    (hr : rank A = 2) : Nat.card A = 4 := by
  let := hA
  have hc : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) :=
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A) |>.trans (by simp)
  have hd : Module.finrank (ZMod 2) (Additive A) = 2 := by
    simpa only [rank, hc, Nat.log_pow (by decide : 1 < 2)] using hr
  rw [hc, hd]
  decide

private theorem rank_two_centralizer (A : Subgroup SL) (hA : IsElementaryAbelian 2 A)
    (hr : rank A = 2) : centralizer (A : Set SL) = A := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let e : SL ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.trans Matrix.PSL3Two.equiv.symm).symm
  let := hA
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr (by
    intro h; simp [h, rank] at hr)
  have hK : IsKleinFour A := ⟨rank_two_card A hA hr, IsElementaryAbelian.exponent_eq_prime⟩
  have hmap := GorensteinWalter.isKleinFour_map_of_injective A hK e.toMonoidHom e.injective
  have hC := GorensteinWalter.psl2_kleinFour_centralizer_eq_self (ZMod 7)
    ⟨7, 1, by decide, by decide, by decide, by simp⟩ (A.map e.toMonoidHom) hmap
  apply le_antisymm
  · intro g hg
    have he : e g ∈ centralizer ((A.map e.toMonoidHom) : Set _) := by
      rintro _ ⟨a, ha, rfl⟩
      exact (e.map_mul _ _).symm.trans ((congrArg e (hg a ha)).trans (e.map_mul _ _))
    rw [hC] at he
    exact (Subgroup.mem_map_iff_mem e.injective).mp he
  · intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hb⟩ : A) ⟨a,ha⟩)


private theorem common_involution (P A B : Subgroup SL) (hP : IsPGroup 2 P)
    (hAP : A ≤ P) (hBP : B ≤ P) (hA : Nat.card A = 4) (hB : Nat.card B = 4) :
    ∃ t, t ∈ A ∧ t ∈ B ∧ t ≠ 1 := by
  by_contra! h
  let f : A × B → P := fun x => ⟨x.1.val * x.2.val, P.mul_mem (hAP x.1.property) (hBP x.2.property)⟩
  have hf : Function.Injective f := by
    rintro ⟨a,b⟩ ⟨c,d⟩ he
    have heq : a.val * b.val = c.val * d.val := congrArg Subtype.val he
    have hx : a.val⁻¹ * c.val = b.val * d.val⁻¹ := by
      calc
        _ = a.val⁻¹ * (c.val * d.val) * d.val⁻¹ := by group
        _ = _ := by rw [← heq]; group
    have hone := h (a.val⁻¹ * c.val) (A.mul_mem (A.inv_mem a.property) c.property)
      (hx ▸ B.mul_mem b.property (B.inv_mem d.property))
    have hac : a = c := Subtype.ext (inv_mul_eq_one.mp hone)
    subst c
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hA, hB] at hc
  have hp := pGroup_card_le_eight P hP
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem codim_mono (ρ : Representation (ZMod 2) SL V)
    {A B : Subgroup SL} (hAB : A ≤ B) : fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hd := Submodule.finrank_mono (fixedSpace_antitone ρ hAB)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private theorem offender_data (ρ : Representation (ZMod 2) SL V)
    (hm : ∀ a : SL, a ^ 2 = 1 → a ≠ 1 → 2 ≤ fixedCodim ρ (zpowers a))
    (A : Subgroup SL) (hA : IsOffender ρ A) :
    rank A = 2 ∧ fixedCodim ρ A = 2 ∧
      ∀ a ∈ A, a ≠ 1 → fixedSpace ρ A = fixedSpace ρ (zpowers a) := by
  let := hA.1.2
  obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  have hlow := (hm a (elemPow_eq_one_of_isElementaryAbelian a ha) hne).trans
    (codim_mono ρ (zpowers_le.mpr ha))
  have hhigh := AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two A hA.1.2
  have hc := hA.2
  have hr : rank A = 2 := by omega
  have hd : fixedCodim ρ A = 2 := by omega
  refine ⟨hr, hd, ?_⟩
  intro a ha hne
  have he := hm a (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hm' := codim_mono ρ (zpowers_le.mpr ha)
  exact fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr ha) (by omega)

/-- A faithful binary SL₃(2) action with no transvection has at most one
nontrivial elementary offender in a two-subgroup. Every such offender is
self-centralizing and has equal rank and fixed codimension. -/
theorem offender_rigidity (ρ : Representation (ZMod 2) SL V)
    (hf : Function.Injective ρ)
    (hm : ∀ a : SL, a ^ 2 = 1 → a ≠ 1 → 2 ≤ fixedCodim ρ (zpowers a))
    (P A : Subgroup SL) (hP : IsPGroup 2 P) (hAP : A ≤ P) (hA : IsOffender ρ A) :
    (∀ B ≤ P, IsOffender ρ B → B = A) ∧ fixedCodim ρ A = rank A ∧
      P ⊓ centralizer (A : Set SL) = A := by
  obtain ⟨hrA, hdA, hfixA⟩ := offender_data ρ hm A hA
  have hCA := rank_two_centralizer A hA.1.2 hrA
  refine ⟨?_, hdA.trans hrA.symm, by rw [hCA, inf_eq_right.mpr hAP]⟩
  intro B hBP hB
  obtain ⟨hrB, hdB, hfixB⟩ := offender_data ρ hm B hB
  obtain ⟨t, htA, htB, ht1⟩ := common_involution P A B hP hAP hBP
    (rank_two_card A hA.1.2 hrA) (rank_two_card B hB.1.2 hrB)
  have hfix : fixedSpace ρ A = fixedSpace ρ B := (hfixA t htA ht1).trans (hfixB t htB ht1).symm
  have hqA : IsQuadratic ρ A := by
    let := hA.1.2
    exact isQuadratic_of_common_fixedSpace ρ hfixA
  have hqB : IsQuadratic ρ B := by
    let := hB.1.2
    exact isQuadratic_of_common_fixedSpace ρ hfixB
  have hBA : B ≤ A := by
    rw [← hCA]
    intro b hb a ha
    apply hf
    rw [map_mul, map_mul]
    apply LinearMap.ext
    intro v
    have haD : ρ a v - v ∈ fixedSpace ρ A := fun c => hqA c.val c.property a ha v
    have hbD : ρ b v - v ∈ fixedSpace ρ B := fun c => hqB c.val c.property b hb v
    rw [hfix] at haD
    rw [← hfix] at hbD
    change ρ a (ρ b v) = ρ b (ρ a v)
    calc
      _ = (ρ b v - v) + ρ a v := sub_eq_iff_eq_add.mp (by simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub] using hbD ⟨a, ha⟩)
      _ = (ρ a v - v) + ρ b v := by abel
      _ = _ := (sub_eq_iff_eq_add.mp (by simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub] using haD ⟨b, hb⟩)).symm
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [rank_two_card A hA.1.2 hrA, rank_two_card B hB.1.2 hrB])

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
open Stellmacher.PushingUp.AmalgamGraph

/-- The actual marked X action has no nontrivial transvection. -/
@[expose] def InvolutionBound (source : LocalSource L R) : Prop :=
  letI := X_elementary R (alpha R)
  ∀ a : SL, a ^ 2 = 1 → a ≠ 1 →
    2 ≤ fixedCodim (Offenders.linearize (xAction source)) (zpowers a)

/-- The actual edge image is a two-group, without requiring a module alternative. -/
theorem edgeActor_isPGroup (source : LocalSource L R) (t : Vertex R) :
    IsPGroup 2 (edgeActor source t) := by
  exact (kernel_isPGroup source t).comap_subtype.map (baseProjection source)

/-- Displacement on the genuine X action supplies every clause of the source
edge-offender predicate. No critical endpoint is assumed to be an offender. -/
theorem edgeOffenderUniqueness_of_involutionBound
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (hm : InvolutionBound source) : EdgeOffenderUniqueness source := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  intro t ht
  obtain ⟨A, hAedge, hA⟩ := edgeActor_has_offender source geometry hb t ht
  have h := offender_rigidity (Offenders.linearize (xAction source))
    (xAction_injective source geometry hb) hm (edgeActor source t) A
    (edgeActor_isPGroup source t) hAedge hA
  exact ⟨A, hAedge, hA, h⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
