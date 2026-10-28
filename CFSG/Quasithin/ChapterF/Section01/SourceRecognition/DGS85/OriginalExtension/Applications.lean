module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.MarkedRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.ReducedBorel

/-!
# Original F.1.11–12 applications of reduced extension data

In the mixed A₅/S₃ case the existing local quotient calculation bounds
[B:B₀] by two. The common extension index then turns the reduced Sylow
bound 128 into the original bound 256. An alternative consumes an actual
marked reduced amalgam and a bound on its compatible automorphisms.
These remove only original-versus-reduced transport premises; the
reduced structural bounds and marked recognition retain their producers.

For the quintic solvability branch, solvability of either literal reduced
endpoint passes to the original endpoint and its original local factor.
No global Sylow hypothesis or full Hypothesis B is added. In particular
this transport applies to either D₁₀ or Sz(2) source route once the reduced
opposite solvability has been established.

Sources: DGS, Groups and Graphs (1985), (15.1)–(15.3), pp.226–231;
Aschbacher–Smith F.1.12 and 9.3.1, printed pp.262–264 and 732.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}

/-- The literal common extension index of the mixed source pair is at most two. -/
theorem mixed_extension_index_le_two (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (commonBorel ![K,U] (reducedSylow ![K,U] S)).relIndex
      (commonBorel ![K,U] S) ≤ 2 := by
  rw [reduced_borel_product h]
  exact h.mixedReducedBorel_index_le_two eK eU

/-- The reduced U₄(2)/J₂ order input bounds the original S in the mixed tensor consumer. -/
theorem mixed_original_sylow_le_256_of_reduced_order
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (hred : Nat.card (reducedSylow ![K,U] S) ≤ 128) : Nat.card S ≤ 256 := by
  rw [original_sylow_card h]
  exact (Nat.mul_le_mul hred (mixed_extension_index_le_two h eK eU)).trans (by decide)

/-- A marked model automorphism bound acts on the original full Borel, whose order is 3|S|. -/
theorem mixed_original_sylow_le_256_of_automorphisms
    {A D C : Type*} [Group A] [Group D] [Group C]
    {α : RankTwoAmalgam A D C} [Finite (RankTwoAmalgam.Iso α α)]
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (e : RankTwoAmalgam.Iso (reducedAmalgam ![K,U] S) α)
    (hbound : Nat.card (RankTwoAmalgam.Iso α α) ≤ 768) : Nat.card S ≤ 256 := by
  have hc := (original_borel_card_le_model_automorphisms h e).trans hbound
  rw [(h.mixed_local_orders eK eU).1] at hc
  omega

omit [Finite G] in
/-- Opposite reduced solvability restores the literal original parabolic and local factor.
This discharges only the extension step of the D₁₀/Sz(2) quintic source branch. -/
theorem original_opposite_solvable_of_reduced
    {L : Fin 2 → Subgroup G} (h : HypothesisF11 L S) (i : Fin 2)
    (hs : Group.IsSolvable (parabolic L (reducedSylow L S) (other i))) :
    Group.IsSolvable (parabolic L S (other i)) ∧ Group.IsSolvable (L (other i)) := by
  have hP := (parabolic_solvable_iff_reduced h (other i)).mpr hs
  let := hP
  refine ⟨hP, Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show L (other i) ≤ parabolic L S (other i) from
      le_sup_left.trans le_sup_left)) (inclusion_injective _)⟩

omit [Finite G] in
/-- A soluble marked reduced starred quotient suffices for the original opposite
endpoint; the inclusion-induced F.1.9 quotient marking is retained. -/
theorem original_opposite_solvable_of_reduced_starred_quotient
    {L : Fin 2 → Subgroup G} (h : HypothesisF11 L S) (i : Fin 2)
    {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (e : (starredParabolic L (reducedSylow L S) (other i) ⧸
      pCore 2 (starredParabolic L (reducedSylow L S) (other i))) ≃* Q) :
    Group.IsSolvable (parabolic L S (other i)) ∧ Group.IsSolvable (L (other i)) := by
  let f := ((reduced_hypothesis h).starredQuotientEquiv (other i)).trans e
  have hq : Group.IsSolvable (L (other i) ⧸ pCore 2 (L (other i))) :=
    Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  exact original_opposite_solvable_of_reduced h i
    (((reduced_hypothesis h).parabolic_solvable_iff_local_quotient (other i)).mpr hq)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
