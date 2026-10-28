module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Model

/-!
# Core-by-natural extension equations in the eight-letter model

The augmentation core uses the seven vectors e_i+e_7. The quotient natural
module uses the six classes e_i+e_6, as in SelfExtension.Model. The rectangular
off-diagonal blocks of an extension obey the same Coxeter relations with
these two different diagonal actions.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/
@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
abbrev CoreV := Fin 7 → ZMod 2
abbrev CoreMat := Matrix (Fin 7) (Fin 7) (ZMod 2)
abbrev CoreRect := Matrix (Fin 7) (Fin 6) (ZMod 2)

def coreRows : Fin 7 → Fin 7 → BitVec 7 :=
  ![![2,1,4,8,16,32,64], ![1,4,2,8,16,32,64], ![1,2,8,4,16,32,64],
    ![1,2,4,16,8,32,64], ![1,2,4,8,32,16,64], ![1,2,4,8,16,64,32],
    ![1,2,4,8,16,32,127]]

def CoreA (i : Fin 7) : CoreMat := fun r c =>
  if (coreRows i r).getLsbD c.val then 1 else 0

structure CoreRelations (B : Fin 7 → CoreRect) : Prop where
  square : ∀ i, CoreA i * B i + B i * A i = 0
  commute : ∀ i j, i.val + 1 < j.val →
    CoreA i * B j + B i * A j = CoreA j * B i + B j * A i
  braid : ∀ i j, j.val = i.val + 1 →
    CoreA i * CoreA j * B i + CoreA i * B j * A i + B i * A j * A i =
      CoreA j * CoreA i * B j + CoreA j * B i * A j + B j * A i * A j

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
