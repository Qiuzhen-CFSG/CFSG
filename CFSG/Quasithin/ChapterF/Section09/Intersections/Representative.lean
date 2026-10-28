module

public import CFSG.Quasithin.ChapterF.Section09.Intersections

/-!
# Square-stabilizing representatives in F.9.6

The existence assumption in printed F.9.6(2) supplies an exchanging
representative of the displaced point. We retain that representative in the
conclusion. Its square normalizes every H-invariant subgroup, so both
intersection exchanges are reversible. An element whose image in LT/O₂(LT)
has square one satisfies the required condition, since O₂(LT) is contained
in T. This is the precise form used in Section 13.7.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.6,
printed pp.320–321, and the choice preceding 13.7.10, printed p.941.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

/-- A square stabilizing the original point acts twice trivially on each H-invariant subgroup. -/
theorem conjugate_twice_eq_of_square {A : Subgroup G} {g : G}
    (hA : D.H ≤ normalizer (A : Set G))
    (hs : g ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G)) :
    conjugate (conjugate A g) g = A := by
  have he : conjugate (conjugate A g) g = conjugate A (g ^ 2) := by
    unfold conjugate ChapterG.Section02.Setup.conjugate
    rw [map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, pow_two, mul_inv_rev, mul_assoc]
  rw [he]
  exact mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (A : Set G)).inv_mem (hA (h.local_le hs)))

/-- The exchanging representative acts in both directions on the two intersections. -/
theorem intersection_exchange_both_of_square {g : G}
    (hs : g ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G)) :
    conjugate (D.DH g) g = D.DHg g ∧
    conjugate (D.DHg g) g = D.DH g ∧
    conjugate (D.EH g) g = D.EHg g ∧
    conjugate (D.EHg g) g = D.EH g := by
  obtain ⟨hD, hE⟩ := h.intersection_exchange_of_square hs
  refine ⟨hD, ?_, hE, ?_⟩
  · unfold DHg DH conjugate ChapterG.Section02.Setup.conjugate
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
    change conjugate (conjugate D.UH g) g ⊓ conjugate D.QH g = _
    rw [h.conjugate_twice_eq_of_square (A := D.UH) (le_normalizer_conjugateSpanBy D.Vplus D.H) hs]
    rfl
  · unfold EHg EH conjugate ChapterG.Section02.Setup.conjugate
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
    change conjugate (conjugate D.VH g) g ⊓ conjugate D.QH g = _
    rw [h.conjugate_twice_eq_of_square (A := D.VH) (le_normalizer_conjugateSpanBy D.V D.H) hs]
    rfl

/-- The original existence premise of F.9.6(2) gives an exchanging representative.
The witness itself, rather than an arbitrary representative, conjugates D_H and E_H. -/
theorem exists_intersection_exchange {g : G} (hg : g ∈ D.L)
    (hex : ∃ g₀ ∈ D.L, conjugate D.V₁ g = conjugate D.V₁ g₀ ∧
      g₀ ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G)) :
    ∃ g₀ ∈ D.L, conjugate D.V₁ g = conjugate D.V₁ g₀ ∧
      g₀ ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G) ∧
      conjugate (D.DH g) g₀ = D.DHg g ∧
      conjugate (D.EH g) g₀ = D.EHg g := by
  obtain ⟨g₀, hg₀, he, hs⟩ := hex
  exact ⟨g₀, hg₀, he, hs, h.intersection_exchange_chosen hg hg₀ he hs⟩

/-- The source condition ḡ²=1 in LT/O₂(LT) places g² in L₁T. -/
theorem square_mem_local_of_core_quotient_square (g : D.LT)
    (hs : (QuotientGroup.mk' (pCore 2 D.LT) g) ^ 2 = 1) :
    (g : G) ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G) := by
  have hc : g ^ 2 ∈ pCore 2 D.LT :=
    (QuotientGroup.eq_one_iff (g ^ 2)).mp (by
      change QuotientGroup.mk' (pCore 2 D.LT) (g ^ 2) = 1
      rw [map_pow]
      exact hs)
  have hT : D.LT.pCoreIn 2 ≤ (D.T : Subgroup G) := by
    rw [← h.sylow_centralizer]
    exact inf_le_left
  exact mem_sup_right (hT (mem_map_of_mem D.LT.subtype hc))

/-- All four literal intersection exchanges for the original core-quotient choice. -/
theorem intersection_exchange_of_core_quotient_square (g : D.LT)
    (hs : (QuotientGroup.mk' (pCore 2 D.LT) g) ^ 2 = 1) :
    conjugate (D.DH (g : G)) (g : G) = D.DHg (g : G) ∧
    conjugate (D.DHg (g : G)) (g : G) = D.DH (g : G) ∧
    conjugate (D.EH (g : G)) (g : G) = D.EHg (g : G) ∧
    conjugate (D.EHg (g : G)) (g : G) = D.EH (g : G) :=
  h.intersection_exchange_both_of_square (h.square_mem_local_of_core_quotient_square g hs)

end Hypothesis
end CFSG.Quasithin.ChapterF.Section09.Setup
