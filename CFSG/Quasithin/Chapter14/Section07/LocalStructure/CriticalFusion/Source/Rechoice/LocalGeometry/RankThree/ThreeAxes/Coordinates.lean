module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes.Linear
public import Theory.ElementaryAbelian.MarkedEightCoordinates


/-!
# Coordinates on the three actual rank-three axes

Three order-two subgroups in an elementary abelian group of order eight form
coordinate axes when the first two are distinct and the third is outside their
join. Choosing their nonidentity elements gives a basis and a multiplicative
coordinate equivalence carrying each standard axis to its literal subgroup.

Source: Aschbacher–Smith, proof of 14.7.70, printed pp.1073–1074.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
noncomputable section
open Linear

variable {G : Type*} [Group G] [Finite G]

theorem coordinates (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hcA : Nat.card A = 8) (P : Fin 3 → Subgroup G)
    (hPA : ∀ i, P i ≤ A) (hcP : ∀ i, Nat.card (P i) = 2)
    (h01 : Disjoint (P 0) (P 1)) (h2 : ¬ P 2 ≤ P 0 ⊔ P 1) :
    ∃ e : Model ≃* A, ∀ i, ((axis i).map e.toMonoidHom).map A.subtype = P i := by
  classical
  have hne (i : Fin 3) : P i ≠ ⊥ := by intro hb; have := hcP i; rw [hb,card_bot] at this; omega
  have hex (i : Fin 3) : ∃ x ∈ P i, x ≠ 1 := by
    by_contra! hh
    exact hne i ((P i).eq_bot_iff_forall.mpr hh)
  choose x hx hx1 using hex
  have hxgen (i : Fin 3) : zpowers (x i) = P i := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr (hx i))
    rw [hcP i]
    have hn : zpowers (x i) ≠ ⊥ := by
      intro hh
      have hxbot : x i ∈ (⊥ : Subgroup G) := by
        rw [← hh]
        exact mem_zpowers _
      exact hx1 i (by simpa using hxbot)
    exact (one_lt_card_iff_ne_bot _).mpr hn
  let v : Fin 3 → Additive A := fun i => Additive.ofMul ⟨x i,hPA i (hx i)⟩
  let U : Submodule (ZMod 2) (Additive A) := AddSubgroup.toZModSubmodule 2 ((P 0).subgroupOf A).toAddSubgroup
  let D : Submodule (ZMod 2) (Additive A) := AddSubgroup.toZModSubmodule 2 ((P 0 ⊔ P 1).subgroupOf A).toAddSubgroup
  have h0 : v 0 ≠ 0 := fun hh => hx1 0 (congrArg (fun a : Additive A => (a.toMul : G)) hh)
  have h1 : v 1 ∉ U := by
    intro hh
    have hz := h01.le_bot ⟨hh,hx 1⟩
    exact hx1 1 hz
  have hv2 : v 2 ∉ D := by
    intro hh
    apply h2
    rw [← hxgen 2]
    exact zpowers_le.mpr hh
  have hli2 : LinearIndependent (ZMod 2) ![v 0,v 1] := by
    apply (LinearIndependent.pair_iff' h0).mpr
    intro a he
    exact h1 (he ▸ U.smul_mem a (hx 0))
  have hspan : Submodule.span (ZMod 2) (Set.range ![v 0,v 1]) ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact mem_sup_left (hx 0)
    · exact mem_sup_right (hx 1)
  have hli : LinearIndependent (ZMod 2) v := by
    have h := hli2.finSnoc (x := v 2) (fun hh => hv2 (hspan hh))
    have he : v = Fin.snoc ![v 0,v 1] (v 2) := by ext i; fin_cases i <;> rfl
    rw [he]
    exact h
  have hdim : Module.finrank (ZMod 2) (Additive A) = 3 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    change Nat.card A = _ at hc
    rw [hcA,Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hdim.symm)
  let e : Model ≃* A := b.equivFun.symm.toAddEquiv.toMultiplicativeLeft
  have he (i : Fin 3) : e (standard i) = ⟨x i,hPA i (hx i)⟩ := by
    change b.equivFun.symm (Pi.single i 1) = v i
    rw [Module.Basis.equivFun_symm_apply]
    simp [b]
  refine ⟨e,fun i => ?_⟩
  rw [axis,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  change zpowers ((e (standard i) : A) : G) = P i
  rw [he i]
  exact hxgen i
end
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
