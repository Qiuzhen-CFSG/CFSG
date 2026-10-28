module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Normal
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SeedFusion

/-!
# Sylow size and quaternion fusion in the Chapter 14 source branch

The genuine source-local configuration now determines the order of the
original ambient Sylow T: it is 64. It also supplies a normal quaternion
central product in an involution centralizer, with an elementary subgroup
of order at least four whose nonidentity points are all ambient-conjugate.
In particular the central involution fuses to a noncentral involution of
that quaternion product. Normality remains relative to the centralizer.

These are applications to the selected counterexample and its original
SourceLocalData, without a recognition callback. They do not discharge the
I.4.5 isomorphism in `recognition_of_source_local`. The remaining recognition
belongs to `qt-i45-g2-recognition`; the source-local premise and final
Chapter 14 assembly belong to `qt-d-14414-g2-source`.
Source: Aschbacher–Smith 14.4.3–5, printed pp.1007–1008, and I.4.5, p.417;
Fong–Wong §2B and §2F, Nagoya Math. J.36 (1969), pp.151,153–154.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_ambient_sylow_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) : Nat.card T = 64 := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  exact ambient_sylow_card c T

theorem source_quaternion_fused_four (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (H : Subgroup G) (Q A : Subgroup H) (z : H), Q.Normal ∧
      Nonempty (QuaternionCentralProductData Q) ∧ Nat.card H = 576 ∧
      Nat.card Q = 32 ∧ orderOf z = 2 ∧ H = centralizer ({(z : G)} : Set G) ∧
      (center Q).map Q.subtype = zpowers z ∧ A ≤ Q ∧
      IsElementaryAbelian 2 A ∧ 4 ≤ Nat.card A ∧ z ∈ A ∧
      ∀ x : A, x ≠ 1 → IsConj (z : G) ((x : H) : G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨z,A,hz,hH,hgen,hAQ,he,hc,hzA,hf⟩ := exists_fused_four_in_quaternionCore c
  exact ⟨c.H, quaternionCore c, A, z, inferInstance, ⟨quaternionCoreData c⟩,
    H_card c, quaternionCore_card c, hz, hH,
    (quaternionCore_center c).trans hgen.symm, hAQ, he, hc, hzA, hf⟩

theorem source_quaternion_core_fusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (H : Subgroup G) (Q : Subgroup H) (z : G) (t : Q), Q.Normal ∧
      Nonempty (QuaternionCentralProductData Q) ∧ Nat.card H = 576 ∧
      orderOf z = 2 ∧ H = centralizer ({z} : Set G) ∧ orderOf t = 2 ∧
      t ∉ center Q ∧ IsConj z ((t : H) : G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨z,t,hz,hH,ht,htZ,hf⟩ := exists_distinguished_fusion_in_quaternionCore c
  exact ⟨c.H, quaternionCore c, z, t, inferInstance, ⟨quaternionCoreData c⟩,
    H_card c, hz, hH, ht, htZ, hf⟩

/-- The source data produce an actual pair over a common ambient Sylow,
with the indices required for the subsequent amalgam analysis. -/
theorem source_local_pair_indices (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (H M : Subgroup G) (S : Sylow 2 G),
      (S : Subgroup G) ≤ H ⊓ M ∧ Nat.card H = 576 ∧ Nat.card M = 1344 ∧
      Nat.card (H ⊓ M : Subgroup G) = 192 ∧
      (H ⊓ M).relIndex H = 3 ∧ (H ⊓ M).relIndex M = 7 := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  let R : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨g,hRM,hI,hIH,hIM⟩ := exists_local_pair c R
  obtain ⟨S,hS⟩ := H_sylow_is_ambient c R
  refine ⟨c.H,c.M.map (MulAut.conj g).toMonoidHom,S,?_,H_card c,?_,hI,hIH,hIM⟩
  · rw [hS]
    exact le_inf (map_subtype_le _) hRM
  · rw [card_map_of_injective (MulAut.conj g).injective,M_card c]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
