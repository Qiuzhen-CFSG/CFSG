module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.Fibers
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.QuaternionFiber

/-!
# The 480 involutions of the z-class in K outside Q

Select an actual z-class inverter in K outside Q. The two natural binary
sections give a factor16, while the original quaternion coset has exactly
two z-class involutions. All fifteen even-involution fibers of H/Q are
conjugate under H. Thus the literal ambient z-class subset has order480.
All inputs come from the original type-Ru setup and its source choices.

Source: Aschbacher–Smith J.2.7(8), printed p.437 (PDF p.448).
-/

open Subgroup Representation Representation.BinaryConjugationSection
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)

public theorem middle_z_class_card_source :
    Nat.card {x:G//IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}=480 := by
  obtain ⟨i,hiK,hiQ,hi,hbi,hzi⟩:=c.exists_middle_inverter_source
  have hi2:(i:G)^2=1:=hi ▸ pow_orderOf_eq_one (i:G)
  have hc:Nat.card (c.zFiber (d.ru2.quotientMap i))=32 := by
    rw [Nat.card_congr (c.zFiberEquivInverting i hi2),
      c.card_Q_z_filter i hiK hiQ hi2 hbi,
      c.quaternion_inverting_z_class_card i hiK hiQ hi hbi hzi]
  exact c.card_middle_of_one_fiber i hiK hiQ hi2 32 hc

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
