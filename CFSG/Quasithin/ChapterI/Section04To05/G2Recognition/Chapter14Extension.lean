module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Sylow
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AmbientFusion

/-!
# The split involution centralizer in the Chapter 14 source branch

The actual source-local configuration supplies a self-centralizing normal
quaternion product Q. The conjugation-induced quotient H/Q is exactly the
equal-sign subgroup of S₃ × S₃. The original product of the two normal
SL₂(3) factors has an involution complement acting outerly on both
quaternion factors, and this complement is ambient-conjugate to the marked
central involution. Every ambient involution is in that one class and has
centralizer order 576. The elementary eight and intersection two-core
retain the literal conjugation maps of the aligned local pair.

These statements apply the proved extension and fusion calculations to
`SourceLocalData`; they introduce no recognition callback. The equivalence
with Atlas.G2.Model and the discharge of `recognition_of_source_local`
remain with `qt-i45-g2-recognition`. The independent source-local producer
is `qt-d-14414-g2-local-source`, with final Chapter 14 assembly owned by
`qt-d-14414-g2-source`.

Source: Aschbacher–Smith I.4.5, printed p.417, and 14.4.3–5, pp.1007–1008;
Fong–Wong, Nagoya Math. J.36 (1969), §2F, pp.153–154.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked extension and its quotient action, derived from the source data. -/
theorem source_split_extension (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (z : G) (n : c.H),
      centralizer (quaternionCore c : Set c.H) = c.H₁ ⊓ c.H₂ ∧
      Nonempty ((c.H ⧸ quaternionCore c) ≃* diagonalSign) ∧
      orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) ∧
      orderOf n = 2 ∧ n ∉ c.H₁ ⊔ c.H₂ ∧
      (c.H₁ ⊔ c.H₂).IsComplement' (zpowers n) ∧ IsConj z (n:G) ∧
      (quaternionCoreData c).BothOuter (MulAut.conjNormal n) ∧
      (∀ i : BinaryFourPlus.C2, orderOf ((coreOuterAction c n).left i) = 2 ∧
        Equiv.Perm.sign ((coreOuterAction c n).left i) ≠ 1) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨z,n,hz,hH,hn,hout,hcomp,hf,ho,ha⟩ :=
    exists_fused_involution_complement_with_action c
  exact ⟨c,z,n,core_centralizer c,⟨coreQuotientEquiv c⟩,hz,hH,hn,hout,hcomp,hf,ho,ha⟩

/-- The original ambient group has a single involution class. -/
theorem source_involutions_conjugate (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) (x y : G) (hx : orderOf x=2) (hy : orderOf y=2) :
    IsConj x y := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  exact involutions_conjugate c x y hx hy

/-- Every involution centralizer in the original group has order 576. -/
theorem source_involution_centralizer_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) (x : G) (hx : orderOf x=2) :
    Nat.card (centralizer ({x} : Set G)) = 576 := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  exact involution_centralizer_card c x hx

/-- The two-core of the actual aligned overlap is the quaternion product;
its elementary eight is normalized and self-centralizing in the common Sylow. -/
theorem source_aligned_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (R : Sylow 2 c.H) (E : Subgroup c.H) (g : G),
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ E ≤ quaternionCore c ∧
      (R : Subgroup c.H) ≤ normalizer (E : Set c.H) ∧
      (R : Subgroup c.H) ⊓ centralizer (E : Set c.H) = E ∧
      E.map c.H.subtype = (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom ∧
      (R : Subgroup c.H).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).pCoreIn 2 =
        (quaternionCore c).map c.H.subtype := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  let R : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨E,g,he,hc,hEQ,hn,hcent,hE,hRM,hcore⟩ := exists_seed_in_quaternionCore c R
  exact ⟨c,R,E,g,he,hc,hEQ,hn,hcent,hE,hRM,hcore⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
