module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceMaximalCore

/-!
# The actual A₆/S₆ alternatives and Sylow orders after 13.5.15(7)

The six-letter action of the original M has kernel its original two-core,
of order sixteen, and the image of L is exactly A₆. Since A₆ has index two
in S₆, either M=L or the action induces the actual S₆ quotient. The order
formula then gives the original Sylow subgroup order 128 or 256, respectively.

Source: Aschbacher–Smith 13.5.15, printed p.921, the local alternatives
following clause (7) and used in the final clause (9).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceMaximalCore
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- The two quotient alternatives refer to the original maximal local M. -/
theorem maximal_quotient_alternatives (hQ : D.LT.pCoreIn 2 = D.V)
    (hmax : IsMaximalTwoLocal M) :
    M = D.L ∨ Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)) := by
  have hLM : D.L ≤ M := by rw [d.local_normalizer]; exact D.L.le_normalizer
  have hVL : D.V ≤ D.L := by
    rw [←(SourceSixBlock.source13_5_15_four d h e hseed hn hU).2.1]
    exact map_subtype_le _
  obtain ⟨hc,_,_⟩ := maximal_core_normalizer d h e hseed hn hU hQ hmax
  obtain ⟨f,hfL,hfk⟩ := maximal_permutation_extension d h e hseed hn hU hQ hmax
  have hkL : f.ker ≤ D.L.subgroupOf M := by
    rw [hfk]
    exact subgroupOf_mono M hVL
  have hLf : (D.L.subgroupOf M).map f = alternatingGroup (Fin 6) := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have he := hfL ⟨l.val,hl⟩
      change f l = _ at he
      rw [he]
      exact (SourceSixBlock.actor d ⟨l.val,hl⟩).property
    · intro a ha
      obtain ⟨l,hl⟩ := SourceSixBlock.actor_surjective d ⟨a,ha⟩
      exact ⟨inclusion hLM l,l.property,(hfL l).trans (congrArg Subtype.val hl)⟩
  have hA : alternatingGroup (Fin 6) ≤ f.range := hLf ▸ (D.L.subgroupOf M).map_le_range f
  have hd : f.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hA
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with ht | ht
  · right
    have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp (index_eq_one.mp ht)
    have hk : f.ker = pCore 2 M := by
      rw [hfk]
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le (hVL.trans hLM)]
      exact hc.symm
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩
  · left
    have hr : f.range = alternatingGroup (Fin 6) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two ht
    have he : D.L.subgroupOf M = ⊤ := map_injective_of_ker_le f hkL le_top (by
      rw [hLf,←MonoidHom.range_eq_map,hr])
    apply le_antisymm ?_ hLM
    intro x hx
    exact (show (⟨x,hx⟩ : M) ∈ D.L.subgroupOf M from by rw [he]; trivial)

/-- Exact local model and Sylow-order alternatives needed in source clause (9). -/
theorem maximal_model_and_sylow_order (hQ : D.LT.pCoreIn 2 = D.V)
    (hmax : IsMaximalTwoLocal M) :
    (M = D.L ∧ Nat.card D.T = 128) ∨
      (Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)) ∧ Nat.card D.T = 256) := by
  have hTM : (D.T : Subgroup G) ≤ M := by
    rw [d.local_normalizer]
    exact d.normalizes_L
  have hcore : Nat.card (pCore 2 M) = 16 := by
    have hc := (maximal_core_normalizer d h e hseed hn hU hQ hmax).1
    have hh : Nat.card (M.pCoreIn 2) = Nat.card (pCore 2 M) :=
      card_map_of_injective M.subtype_injective
    rw [hc,ReturningPlane.module_card d] at hh
    exact hh.symm
  have hSylow := (D.T.subtype hTM).card_eq_multiplicity
  have heq : Nat.card (D.T.subtype hTM) = Nat.card D.T :=
    Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv
  rw [heq] at hSylow
  rcases maximal_quotient_alternatives d h e hseed hn hU hQ hmax with he | ha
  · left
    refine ⟨he,?_⟩
    have hquot : Nat.card (M ⧸ pCore 2 M) = 360 := by
      rw [he,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num
    have hc : Nat.card M = 5760 := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 M),hquot,hcore]
    rw [hc] at hSylow
    exact hSylow.trans (by decide +kernel)
  · right
    obtain ⟨a⟩ := ha
    refine ⟨⟨a⟩,?_⟩
    have hquot : Nat.card (M ⧸ pCore 2 M) = 720 := by
      rw [Nat.card_congr a.toEquiv,Nat.card_perm,Nat.card_fin]
      decide
    have hc : Nat.card M = 11520 := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 M),hquot,hcore]
    rw [hc] at hSylow
    exact hSylow.trans (by decide +kernel)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceMaximalCore
end
