module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14MarkedCubic
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MarkedNormalizer

/-!
# Full elementary-eight normalizers in the dimension-four source branch

The marked M in the genuine SourceLocalData configuration is the full
ambient normalizer of its elementary eight, and that eight is ambient
self-centralizing. The same identities hold for the actual conjugate
aligned with an H-Sylow. This conjugate remains inside the product of
the two original quaternion cores, which is the two-core of the overlap.
All subgroup inclusions and the conjugating element are retained.

This discharges the full-normalizer and ambient-centralizer premises
needed to use the marked M as a two-local group in Aschbacher–Smith I.4.5,
printed p.417. It supplies no recognition callback. The exceptional
prime-three exclusions and Atlas model equivalence remain with
`qt-i45-g2-recognition`. The existing owner `qt-d-14414-g2-source` supplies
SourceLocalData and discharges that premise in final Chapter14 assembly.
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

/-- The full normalizers and centralizers, with the actual common-Sylow
alignment and the original quaternion factors retained. -/
theorem source_marked_eight_normalizers (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (R : Sylow 2 c.H) (E : Subgroup c.H) (g : G),
      centralizer (c.V.map c.M.subtype : Set G) = c.V.map c.M.subtype ∧
      normalizer (c.V.map c.M.subtype : Set G) = c.M ∧
      normalizer (c.M : Set G) = c.M ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ E ≤ quaternionCore c ∧
      E.map c.H.subtype = (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom ∧
      (R : Subgroup c.H).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).pCoreIn 2 =
        (quaternionCore c).map c.H.subtype ∧
      centralizer (E.map c.H.subtype : Set G) = E.map c.H.subtype ∧
      normalizer (E.map c.H.subtype : Set G) = c.M.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  let R : Sylow 2 c.H := default
  obtain ⟨E,g,he,hc,hEQ,_,_,hE,hRM,hcore⟩ := exists_seed_in_quaternionCore c R
  refine ⟨c,R,E,g,V_ambient_centralizer c,M_seed_normalizer c,M_self_normalizing c,
    he,hc,hEQ,hE,hRM,hcore,?_,?_⟩
  · rw [hE]
    exact conjugate_seed_centralizer c g
  · rw [hE]
    exact conjugate_seed_normalizer c g

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
