module
public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# Separating disjoint supports in a ratio-indecomposable action

If each starred actor fixes one of two invariant complementary spaces, the
starred family partitions according to which space it can move. A nonempty
partition on both sides is precisely the source D.2.16 decomposition. With
no global fixed vectors, a nonzero first support therefore fills the module.
This is the common step in D.2.23–25, on the original module and inclusions.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem fixed_by_join (W : Submodule (ZMod 2) V) (Q : Set (Subgroup G))
    (h : ∀ A ∈ Q, W ≤ fixedSpace ρ A) : W ≤ fixedSpace ρ (sSup Q) := by
  rw [sSup_eq_iSup',fixedSpace_iSup_family]
  exact le_iInf fun A => h A A.property

private theorem moved_le_of_fixed_complement
    (W C : Submodule (ZMod 2) V) (hcompl : IsCompl W C)
    (hstable : ∀ g w, w ∈ W → ρ g w ∈ W)
    (A : Subgroup G) (hfix : C ≤ fixedSpace ρ A) : subspaceCommutator ρ ⊤ A ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,_,rfl⟩
  obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ W ⊔ C from hcompl.sup_eq_top ▸ Submodule.mem_top)
  have he : ρ g c = c := hfix hc ⟨g,hg⟩
  rw [map_add,he,add_sub_add_right_eq_sub]
  exact W.sub_mem (hstable g w hw) hw

/-- Literal source support separation, preserving the original starred family. -/
theorem support_eq_top_of_starred_dichotomy
    (hgen : Jhat ρ = ⊤) (hind : IsRatioIndecomposable ρ)
    (hfixed : fixedSpace ρ ⊤ = ⊥)
    (W C : Submodule (ZMod 2) V) (hcompl : IsCompl W C)
    (hW : ∀ g w, w ∈ W → ρ g w ∈ W)
    (hC : ∀ g w, w ∈ C → ρ g w ∈ C)
    (hne : W ≠ ⊥)
    (hdich : ∀ A ∈ QhatStar ρ, W ≤ fixedSpace ρ A ∨ C ≤ fixedSpace ρ A) :
    W = ⊤ ∧ C = ⊥ := by
  classical
  let Q₁ : Set (Subgroup G) := {A | A ∈ QhatStar ρ ∧ C ≤ fixedSpace ρ A}
  let Q₂ : Set (Subgroup G) := {A | A ∈ QhatStar ρ ∧ ¬ C ≤ fixedSpace ρ A}
  have hsplit : Q₁ ∪ Q₂ = QhatStar ρ := by
    ext A
    change (A ∈ QhatStar ρ ∧ C ≤ fixedSpace ρ A) ∨
      (A ∈ QhatStar ρ ∧ ¬ C ≤ fixedSpace ρ A) ↔ A ∈ QhatStar ρ
    tauto
  have hfix₁ : C ≤ fixedSpace ρ (sSup Q₁) := fixed_by_join ρ C Q₁ (fun _ h => h.2)
  have hfix₂ : W ≤ fixedSpace ρ (sSup Q₂) := fixed_by_join ρ W Q₂
    (fun A hA => (hdich A hA.1).resolve_right hA.2)
  have hne₁ : Q₁.Nonempty := by
    by_contra hn
    have he : Q₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have he₂ : Q₂ = QhatStar ρ := by simpa only [he,Set.empty_union] using hsplit
    have hb : W ≤ fixedSpace ρ ⊤ := by
      rw [he₂] at hfix₂
      change W ≤ fixedSpace ρ (Jhat ρ) at hfix₂
      simpa only [hgen] using hfix₂
    exact hne (le_bot_iff.mp (hb.trans_eq hfixed))
  have hempty : Q₂ = ∅ := by
    by_contra hn
    have hne₂ : Q₂.Nonempty := Set.nonempty_iff_ne_empty.mpr hn
    have hn₁ : sSup Q₁ ≠ ⊥ := by
      obtain ⟨A,hA⟩ := hne₁
      exact fun he => hA.1.1.2.1.1 (le_bot_iff.mp ((le_sSup hA).trans_eq he))
    have hn₂ : sSup Q₂ ≠ ⊥ := by
      obtain ⟨A,hA⟩ := hne₂
      exact fun he => hA.1.1.2.1.1 (le_bot_iff.mp ((le_sSup hA).trans_eq he))
    apply hind
    refine ⟨sSup Q₁,sSup Q₂,W,C,hn₁,hn₂,hgen,Q₁,Q₂,hne₁,hne₂,?_,hsplit,
      rfl,rfl,hcompl,?_,?_,?_,?_⟩
    · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => h₂.2 h₁.2)
    · exact moved_le_of_fixed_complement ρ W C hcompl hW _ hfix₁
    · exact moved_le_of_fixed_complement ρ C W hcompl.symm hC _ hfix₂
    · exact (subspaceCommutator_eq_bot_iff _ _ _).mpr hfix₁
    · exact (subspaceCommutator_eq_bot_iff _ _ _).mpr hfix₂
  have he₁ : Q₁ = QhatStar ρ := by simpa only [hempty,Set.union_empty] using hsplit
  have hc : C = ⊥ := by
    have hb : C ≤ fixedSpace ρ ⊤ := by
      rw [he₁] at hfix₁
      change C ≤ fixedSpace ρ (Jhat ρ) at hfix₁
      simpa only [hgen] using hfix₁
    exact le_bot_iff.mp (hb.trans_eq hfixed)
  exact ⟨by simpa only [hc,sup_bot_eq] using hcompl.sup_eq_top,hc⟩

end CFSG.Quasithin.ChapterD.CyclicSource
