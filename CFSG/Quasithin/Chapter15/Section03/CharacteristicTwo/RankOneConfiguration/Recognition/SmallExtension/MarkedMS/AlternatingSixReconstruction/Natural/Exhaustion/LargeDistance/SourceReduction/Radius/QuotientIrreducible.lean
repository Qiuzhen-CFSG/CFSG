module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.ChiefBudget

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions

/-!
# Irreducibility of the nonabelian moving central quotient

The normal-layer dichotomy forces every invariant subgroup of P/Z(P) to
be trivial or whole. This uses the actual conjugation quotient and lifts
invariant subgroups through its projection; nonabelianness supplies the
nonzero quotient. Source: MS93 (3.8), printed pp.878--879.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.AlternatingBudget
variable {H : Type*} [Group H]

/-- The actual action on the center quotient is irreducible as a group
module whenever the moving subgroup is nonabelian and its normal layers
satisfy the proved unique-chief dichotomy. -/
theorem quotient_group_irreducible
    (P : Subgroup H) [P.Normal]
    (hdich : ∀ Y : Subgroup H, Y.Normal → Y ≤ P →
      Y ≤ P ⊓ centralizer (P : Set H) ∨ P ≤ Y ⊔ (P ⊓ centralizer (P : Set H)))
    (ρ : H →* MulAut (P ⧸ center P))
    (hρ : ∀ g (x : P), ρ g (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center P) (MulAut.conjNormal g x))
    (D : Subgroup (P ⧸ center P))
    (hD : ∀ g x, x ∈ D → ρ g x ∈ D) : D = ⊥ ∨ D = ⊤ := by
  let q := QuotientGroup.mk' (center P)
  let Y := (D.comap q).map P.subtype
  have hYP : Y ≤ P := map_subtype_le _
  have hCY : P ⊓ centralizer (P : Set H) ≤ Y := by
    intro x hx
    let v : P := ⟨x,hx.1⟩
    refine ⟨v,?_,rfl⟩
    have hv : v ∈ center P := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hx.2 y y.property)
    change q v ∈ D
    rw [show q v = 1 from (QuotientGroup.eq_one_iff v).mpr hv]
    exact D.one_mem
  have hYn : Y.Normal := by
    constructor
    intro x hx g
    obtain ⟨x,hx,rfl⟩ := hx
    refine ⟨MulAut.conjNormal g x,?_,rfl⟩
    change q (MulAut.conjNormal g x) ∈ D
    rw [←hρ]
    exact hD g (q x) hx
  rcases hdich Y hYn hYP with hc | hc
  · left
    apply bot_unique
    intro v hv
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    have hx : (x : H) ∈ Y := ⟨x,hv,rfl⟩
    apply mem_bot.mpr
    apply (QuotientGroup.eq_one_iff x).mpr
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((hc hx).2 y y.property)
  · right
    rw [sup_eq_left.mpr hCY] at hc
    apply top_unique
    intro v _
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    obtain ⟨y,hy,he⟩ := hc x.property
    have heq : y = x := Subtype.ext he
    exact heq ▸ hy

/-- The literal binary linearization of that same conjugation action is
irreducible. Nonabelianness is used only for its nonzero-space clause. -/
theorem quotient_linear_irreducible
    (P : Subgroup H) [P.Normal] [IsElementaryAbelian 2 (P ⧸ center P)]
    (hn : ¬ IsMulCommutative P)
    (hdich : ∀ Y : Subgroup H, Y.Normal → Y ≤ P →
      Y ≤ P ⊓ centralizer (P : Set H) ∨ P ≤ Y ⊔ (P ⊓ centralizer (P : Set H)))
    (ρ : H →* MulAut (P ⧸ center P))
    (hρ : ∀ g (x : P), ρ g (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center P) (MulAut.conjNormal g x)) :
    IsIrreducible (Offenders.linearize ρ) := by
  let : Nontrivial (P ⧸ center P) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply hn
    constructor
    constructor
    intro x y
    have hx : x ∈ center P := (QuotientGroup.eq_one_iff x).mp (hs.elim _ _)
    exact (mem_center_iff.mp hx y).symm
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,?_⟩
  intro U
  let D : Subgroup (P ⧸ center P) := AddSubgroup.toSubgroup' U.toSubmodule.toAddSubgroup
  rcases quotient_group_irreducible P hdich ρ hρ D
    (fun g x hx => U.apply_mem_toSubmodule g hx) with hd | hd
  · left
    apply bot_unique
    intro v hv
    have hh : v.toMul ∈ D := hv
    rw [hd,mem_bot] at hh
    exact hh
  · right
    apply top_unique
    intro v _
    have hv : v.toMul ∈ D := by rw [hd]; trivial
    exact hv

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.AlternatingBudget
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
