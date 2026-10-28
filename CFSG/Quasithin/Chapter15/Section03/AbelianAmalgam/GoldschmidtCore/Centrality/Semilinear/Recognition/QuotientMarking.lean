module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Marking
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Marking the two local images of a recognized Goldschmidt quotient

The local symmetric-three quotients imply that neither local image is a
two-group. Neither is the whole quotient: lifting that equality would make
its local core quotient simultaneously S₃ and PSL₃(2), of orders six and 168.
The source common Sylow then descends and the compatible marking theorem
orients both local images under one isomorphism.

The PSL₃(2) identification remains an explicit input. This module does not
replace the full F.6.18/B.5.6 comparison needed to establish it.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.1 and
the terminal Goldschmidt configuration on printed pp.1154–1155.
-/

public section

open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

private theorem not_two_of_symmetric_quotient {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : ¬ IsPGroup 2 A := by
  intro h
  have hp := (h.of_surjective (QuotientGroup.mk' (pCore 2 A))
    (QuotientGroup.mk'_surjective _)).of_equiv e
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hc] at hn
  have hcop := (by decide : Nat.Coprime 2 3).pow_left n
  rw [← hn] at hcop
  norm_num at hcop

private theorem local_ne_top {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* PSL) (A : Subgroup H)
    (ha : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))) : A ≠ ⊤ := by
  intro h
  subst A
  obtain ⟨ha⟩ := ha
  let t : (⊤ : Subgroup H) ≃* H := Subgroup.topEquiv
  let c := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (IsPGroup.ker_isPGroup_of_injective t.injective) (p := 2)
  have hc := Nat.card_congr (c.symm.trans ha).toEquiv
  have he := Nat.card_congr e.toEquiv
  rw [card_PSL] at he
  rw [he] at hc
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm, Nat.factorial] at hc

/-- A recognized actual Goldschmidt quotient has one compatible marking of
both actual local images and their common Sylow image. Properness and the
non-two-group conditions are proved from the local S₃ quotients. -/
theorem mark_goldschmidt_quotient {H : Type*} [Group H] [Finite H]
    (G₁ G₂ : Subgroup H) (c : CFSG.Quasithin.ChapterF.IsGoldschmidtTriple G₁ G₂)
    (e₀ : (H ⧸ pCore 2 H) ≃* PSL) :
    ∃ (S : Sylow 2 H) (e : (H ⧸ pCore 2 H) ≃* SL),
      G₁ ⊓ G₂ = (S : Subgroup H) ∧
      ((S : Subgroup H).map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = borelSL ∧
      (G₁.map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = lineParabolicSL ∧
      (G₂.map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = pointParabolicSL := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hQ := c.twoCore_isGreatest.1.1
  have hA (A : Subgroup H) (hQA : pCore 2 H ≤ A)
      (ha : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))) :
      A.map q ≠ ⊤ ∧ ¬ IsPGroup 2 (A.map q) := by
    have hkA : q.ker ≤ A := by rwa [QuotientGroup.ker_mk']
    constructor
    · intro ht
      have he := congrArg (Subgroup.comap q) ht
      rw [comap_map_eq_self hkA,comap_top] at he
      exact local_ne_top e₀ A ha he
    · intro ht
      have hn := ht.comap_of_ker_isPGroup q hker
      rw [comap_map_eq_self hkA] at hn
      exact not_two_of_symmetric_quotient ha.some hn
  obtain ⟨S,hS⟩ := c.intersection_sylow
  let T := S.mapSurjective hq
  obtain ⟨e,he,h₁,h₂⟩ := mark_both_parabolics e₀ T (G₁.map q) (G₂.map q)
    (map_mono (hS.symm.le.trans inf_le_left))
    (map_mono (hS.symm.le.trans inf_le_right))
    (hA G₁ (hQ.trans inf_le_left) c.quotient_left).1
    (hA G₂ (hQ.trans inf_le_right) c.quotient_right).1
    (hA G₁ (hQ.trans inf_le_left) c.quotient_left).2
    (hA G₂ (hQ.trans inf_le_right) c.quotient_right).2
    (by rw [← Subgroup.map_sup,c.generated,map_top_of_surjective q hq])
  exact ⟨S,e,hS,he,h₁,h₂⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
