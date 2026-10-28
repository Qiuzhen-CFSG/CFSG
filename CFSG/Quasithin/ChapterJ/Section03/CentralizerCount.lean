module
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Local
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients

/-!
# The four-layer z-class count inside the source centralizer H

The actual chain U ≤ Q ≤ K ≤ H partitions the z-class intersection.
The proved source fusion gives640 elements outside K,240 in Q outside U,
and31 in U. The earlier J.2.7(8) count480 in K outside Q then gives1391.
The H-centralizer equality retains the original chosen involution z.

Only the displayed middle-layer count remains an earlier-source premise.
No claim of K-transitivity is used; the source's valid H-fusion suffices.
Source: Aschbacher--Smith J.3.4, printed p.439.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

private def classIn (z : G) (A : Subgroup G) : Set G := {x | IsConj z x ∧ x ∈ A}
private def classOutside (z : G) (A B : Subgroup G) : Set G :=
  {x | IsConj z x ∧ x ∈ A ∧ x ∉ B}

private theorem class_card_split (z : G) (A B : Subgroup G) (hBA : B ≤ A) :
    Nat.card (classIn z A) = Nat.card (classOutside z A B) + Nat.card (classIn z B) := by
  classical
  have he : classIn z A = classOutside z A B ∪ classIn z B := by
    ext x
    simp only [classIn, classOutside, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hz,hx⟩
      by_cases hb : x ∈ B
      · exact .inr ⟨hz,hb⟩
      · exact .inl ⟨hz,hx,hb⟩
    · rintro (⟨hz,hx,_⟩ | ⟨hz,hx⟩)
      · exact ⟨hz,hx⟩
      · exact ⟨hz,hBA hx⟩
  have hd : Disjoint (classOutside z A B) (classIn z B) :=
    Set.disjoint_left.mpr (fun _ hx hy => hx.2.2 hy.2)
  rw [he, Nat.card_congr (Equiv.Set.union hd), Nat.card_sum]

omit [Finite G] in
private theorem outside_eq_involutions (z : G) (hz : orderOf z = 2) (A B : Subgroup G)
    (hf : ∀ x ∈ Fusion.involutionsOutside A B, IsConj x z) :
    classOutside z A B = Fusion.involutionsOutside A B := by
  ext x
  constructor
  · rintro ⟨hc,ha,hb⟩
    have ho : orderOf x = 2 := by
      obtain ⟨g,rfl⟩ := isConj_iff.mp hc
      exact ((MulAut.conj g).orderOf_eq z).trans hz
    exact ⟨ha,hb,ho⟩
  · intro hx
    exact ⟨(hf x hx).symm,hx.1,hx.2.1⟩

/-- J.3.4 from the already proved fusion on H\K, Q\U and U, and the
precise earlier J.2.7(8) count in K\Q. -/
theorem count_commuting_z_of_middle_count (c : Choices d)
    (h480 : Nat.card {x : G // IsConj c.z x ∧ x ∈ d.toTypeRuSetup.K ∧
      x ∉ d.toTypeRuSetup.Q} = 480) :
    Nat.card {u : G // IsConj c.z u ∧ Commute u c.z} = 1391 := by
  classical
  obtain ⟨_,_,h26,h28⟩ := SourceCompletion.fusion c
  have hz : orderOf c.z = 2 := SourceCompletion.z_order c
  have hH : Nat.card (classOutside c.z d.toTypeRuSetup.H d.toTypeRuSetup.K) = 640 := by
    rw [outside_eq_involutions _ hz _ _ h26.1.2.2]
    exact h26.1.2.1
  have hQ : Nat.card (classOutside c.z d.toTypeRuSetup.Q d.toTypeRuSetup.U) = 240 := by
    rw [outside_eq_involutions _ hz _ _ h28.1.2.2]
    exact h28.1.2.1
  have hU : Nat.card (classIn c.z d.toTypeRuSetup.U) = 31 := by
    have hu : classIn c.z d.toTypeRuSetup.U ∪ {1} = (d.toTypeRuSetup.U : Set G) := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hx.2
        · exact hx ▸ d.toTypeRuSetup.U.one_mem
      · intro hx
        by_cases he : x = 1
        · exact .inr he
        · exact .inl ⟨(h26.2.2.2.2.2 x hx he).symm,hx⟩
    have hn : (1:G) ∉ classIn c.z d.toTypeRuSetup.U := by
      rintro ⟨hc,_⟩
      have hh : c.z = 1 := isConj_one_left.mp hc
      simp [hh] at hz
    have hd := Set.disjoint_singleton_right.mpr hn
    have hh := Nat.card_congr (Equiv.Set.union hd)
    rw [hu, Nat.card_sum] at hh
    have hc := d.ru2.card_U d.card_Z
    change Nat.card d.toTypeRuSetup.U = _ at hc
    simp only [Nat.card_unique] at hh
    change Nat.card d.toTypeRuSetup.U = Nat.card (classIn c.z d.toTypeRuSetup.U) + 1 at hh
    rw [hc] at hh
    omega
  have h480' : Nat.card (classOutside c.z d.toTypeRuSetup.K d.toTypeRuSetup.Q) = 480 := h480
  have hc : Nat.card (classIn c.z d.toTypeRuSetup.H) = 1391 := by
    rw [class_card_split _ _ _ d.toTypeRuSetup.K_le_H,
      class_card_split _ _ _ d.Q_le_K,
      class_card_split _ _ _ d.ru2.six.kernel_le,hH,h480',hQ,hU]
  have he : {u : G | IsConj c.z u ∧ Commute u c.z} = classIn c.z d.toTypeRuSetup.H := by
    ext x
    rw [classIn,c.H_eq_centralizer_z]
    simp only [Set.mem_ofPred_eq, mem_centralizer_singleton_iff, Commute, SemiconjBy]
  exact (Nat.card_congr (Equiv.setCongr he)).trans hc

end CFSG.Quasithin.ChapterJ.Section03
