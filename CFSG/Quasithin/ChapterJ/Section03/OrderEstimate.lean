module

public import CFSG.Quasithin.ChapterA.Section05To06.Bounds
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients

/-!
# Applying the two-class order estimate to the source Ru configuration

The literal centralizer of the chosen z is H. With J.3.2 closure and the
J.3.3--4 class counts, A.6.5 gives the exact numerical index bound needed
by the Sylow-thirteen congruence argument. The class properties and counts
are exposed here for their separate source constructions; this is not
an order theorem for an arbitrary group of type Ru by itself.

Source: Aschbacher--Smith J.3.2--5, printed pp.438--439.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open ChapterA.Section05To06 Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

theorem index_bound_of_class_counts (c : Choices d)
    (h : TwoInvolutionClasses c.z c.s)
    (closed : ∀ u v : G, IsConj c.z u → IsConj c.z v → Commute u v →
      u*v ≠ 1 → IsConj c.z (u*v))
    (hs : Nat.card {u : G // IsConj c.z u ∧ Commute u c.s} = 455)
    (hz : Nat.card {u : G // IsConj c.z u ∧ Commute u c.z} = 1391) :
    d.toTypeRuSetup.H.index ≤ 455*1846 ∧
      d.toTypeRuSetup.H.index < (3^2*5^2*7*13)*42 := by
  have hb := lemma_A_6_5 h closed
  rw [← c.H_eq_centralizer_z, hs, hz] at hb
  norm_num at hb ⊢
  exact ⟨hb, by omega⟩

end CFSG.Quasithin.ChapterJ.Section03
