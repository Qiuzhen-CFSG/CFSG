module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Geometry
public import Theory.GroupTheory.CubicNormalizerSupplement

/-!
# The original second cubic normalizer order

Frattini supplies A N = F₂. The exact fixed-eight intersection and the
source endpoint orders give 48 elements, retained by the faithful action.

Source: Aschbacher–Smith J.4.4–5 and F.1.12.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
open Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}
    {B5:Sylow 5 d.toTypeRuSetup.H} (m:SecondCubicMarking (p:=p) B5)
    (s:SourceChoice p) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)

include s hi
 theorem supplement : p.A B5⊔secondCubicNormalizer B5 m.X=p.F₂ B5 m.X := by
  let F:=p.F₂ B5 m.X
  let A:Subgroup F:=(p.A B5).subgroupOf F
  let P:Subgroup F:=(p.cubicSubgroup m.X).subgroupOf F
  have hPF:p.cubicSubgroup m.X≤F:=le_sup_right.trans le_sup_left
  have hG:Nat.card F=12288:=s.card_F₂ p B5 hi m.X m.quotient
  have hA:Nat.card A=2048:=(Nat.card_congr (subgroupOfEquivOfLe (p.A_le_F₂ B5 m.X)).toEquiv).trans (s.card_A p B5 hi)
  have hP:Nat.card P=3:=(Nat.card_congr (subgroupOfEquivOfLe hPF).toEquiv).trans (p.card_cubicSubgroup m.X)
  have hh:=cubic_normalizer_supplement_of_orders A P hG hA hP
  have he:(normalizer (P:Set F)).map F.subtype=secondCubicNormalizer B5 m.X:=by
    rw [←subgroupOf_normalizer_eq hPF,subgroupOf_map_subtype]
    exact inf_comm _ _
  have hh':=(congrArg (fun S:Subgroup F=>S.map F.subtype) hh)
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (p.A_le_F₂ B5 m.X),he,←MonoidHom.range_eq_map,F.range_subtype] at hh'
  exact hh'

 theorem normalizer_card : Nat.card (secondCubicNormalizer B5 m.X)=48 := by
  have hn:secondCubicNormalizer B5 m.X≤normalizer (p.A B5:Set G):=
    inf_le_left.trans ((p.F₂_le_parabolic B5 m.X).trans (p.A_normalized B5))
  have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (p.A B5) (secondCubicNormalizer B5 m.X) hn
  rw [inf_comm,m.normalizer_inf_core,m.fixed_card,m.supplement s hi,s.card_A p B5 hi,
    s.card_F₂ p B5 hi m.X m.quotient] at hh
  omega

 theorem image_card : Nat.card (secondCubicNormalizerAction B5 m.X m.coordinates).range=48 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective m.action_injective).toEquiv,m.normalizer_card s hi]
end CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
