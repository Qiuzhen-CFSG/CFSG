module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.SourceMiddle

/-!
# Detecting Dγ outside H_C on the actual core section

When H is the centralizer of the source line, the centralizer of A₁ is
its actual endpoint conjugate. It therefore normalizes Uγ. Consequently
[Uγ,C_{Q_H}(A₁)] lies in Uγ∩Q_H=Dγ. A moved vector in the original
Q_H/H_C section proves that this commutator is not contained in H_C,
and hence Dγ is not contained in H_C.

This is the group-theoretic transfer of the 13.7.4(2) module comparison;
the nonzero displacement on its line-centralizer image remains a separate
model calculation. Source: Aschbacher–Smith, 13.8.27, printed p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry

variable {G W X : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

/-- A moved vector of C_{Q_H}(A₁)/H_C detects the original Dγ, without
choosing a new subgroup in place of the critical kernel. -/
theorem source_Dgamma_not_le_of_core_movement
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ) (hUg : c.Ugamma V₃ ≤ H)
    (hH : H = centralizer (V₁ : Set G))
    (τ : Representation (ZMod 2) (Source.Hstar H) X)
    (t : BinaryConjugationSection H (Source.QH H) (Source.HC H V₃)
      (τ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hmove : ∃ a ∈ Source.starImage H (c.Ugamma V₃),
      ∃ v ∈ t.imageSpace (Source.QH H ⊓ centralizer (c.Aone V₁ : Set G)), τ a v ≠ v) :
    ¬ Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ≤ Source.HC H V₃ := by
  let e := MulAut.conj (c.gb : G)
  have hcentralizer : centralizer (c.Aone V₁ : Set G) ≤ H.map e.toMonoidHom := by
    intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [hH]
    apply mem_centralizer_iff.mpr
    intro z hz
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact mem_centralizer_iff.mp hx (e z) (mem_map_of_mem e.toMonoidHom hz)
  have hnorm : centralizer (c.Aone V₁ : Set G) ≤ normalizer (c.Ugamma V₃ : Set G) := by
    have hm := map_mono (f := e.toMonoidHom) s.normalizes
    rw [map_equiv_normalizer_eq] at hm
    exact hcentralizer.trans hm
  have hcomm : ⁅c.Ugamma V₃, Source.QH H ⊓ centralizer (c.Aone V₁ : Set G)⁆ ≤
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ := by
    rw [s.Dgamma_eq_inf_core _ hUg hfaith]
    refine le_inf (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hnorm)) ?_
    exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hUg.trans t.normalized))
  intro hD
  obtain ⟨_, ⟨a, ha, rfl⟩, v, hv, hne⟩ := hmove
  exact hne (t.fixed_on_imageSpace_of_commutator_le _ _ (hcomm.trans hD) a ha v hv)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
