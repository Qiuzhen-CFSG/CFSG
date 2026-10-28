module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Simplicity
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalGeneration

/-!
# Generating local pairs in the dimension-four source branch

The source-local data now yield a generating pair H,Mᵍ over the same
ambient Sylow two-subgroup, with intersection order 192 and indices three
and seven. The second application retains the actual conjugate elementary
eight and the identity of the intersection two-core with Q₁Q₂. The
original subgroup embeddings and conjugation map remain in each statement.

This discharges generation for the I.4.5 recognition argument. It does not
discharge `recognition_of_source_local`'s model-recognition callback.
That remains with `qt-i45-g2-recognition`; `qt-d-14414-g2-local-source`
produces SourceLocalData and `qt-d-14414-g2-source` owns final assembly.

Source: Aschbacher–Smith I.4.5, printed p.417, and 14.4.3–5, pp.1007–1008.
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

/-- The aligned local pair generated from the source data generates the original group. -/
theorem source_generating_local_pair (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (R : Sylow 2 c.H) (g : G),
      (R : Subgroup c.H).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom ∧
      Nat.card (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom : Subgroup G) = 192 ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).relIndex c.H = 3 ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).relIndex
        (c.M.map (MulAut.conj g).toMonoidHom) = 7 ∧
      c.H ⊔ c.M.map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  let R : Sylow 2 c.H := Classical.choice inferInstance
  exact ⟨c,R,exists_generating_local_pair c R⟩

/-- Generation retains the same seed embedding and overlap-core identity. -/
theorem source_generating_seed_pair (d : Counterexample T L)
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
        (quaternionCore c).map c.H.subtype ∧
      c.H ⊔ c.M.map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨c,R,E,g,he,hc,hEQ,hn,hcent,hE,hRM,hcore⟩ :=
    source_aligned_core d earlier hq chosen structural alternatives F hne hZ hcard localData
  exact ⟨c,R,E,g,he,hc,hEQ,hn,hcent,hE,hRM,hcore,conjugate_local_pair_generates c g⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
