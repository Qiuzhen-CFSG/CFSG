module

public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.GroupTheory.SolvableRadical
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Sylow images in the J₁ involution centralizer

A Sylow two-subgroup containing the standard involution lies in its centralizer,
since the certified Sylow subgroup is elementary abelian of order eight.
The involution is central in that centralizer and therefore lies in its solvable
radical. The Sylow image in the radical quotient consequently has order at most
four and generator rank at most two. These facts need no centralizer recognition.

`ProductModel` specifies the actual C₂ × A₅ product expected by the source;
no isomorphism with it is asserted here.

Source: GLS3, Table 5.3f, and Aschbacher–Smith, E.1.2 and E.1.14(5),
printed pp.209–210 and 214. The ATLAS matrix provenance is in `Model.Basic`.
-/

public section
open Subgroup
namespace Janko1.InvolutionCentralizer

/-- The centralizer of the standard involution in the actual matrix model. -/
abbrev subgroup : Subgroup Model := centralizer ({a} : Set Model)

/-- The concrete product appearing in GLS3 Table 5.3f. -/
abbrev ProductModel := Multiplicative (ZMod 2) × alternatingGroup (Fin 5)

/-- Every Sylow two-subgroup containing `a` centralizes it. -/
theorem sylow_le (T : Sylow 2 Model) (ha : a ∈ (T : Subgroup Model)) :
    (T : Subgroup Model) ≤ subgroup := by
  let := SylowTwo.elementary T
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (isMulCommutative_iff.mp
    (inferInstance : IsMulCommutative T) (⟨x, hx⟩ : T) (⟨a, ha⟩ : T))

/-- Killing the central involution already drops the generator rank of the
Sylow image to at most two, without identifying the whole centralizer. -/
theorem image_rank_le_two (T : Sylow 2 Janko1.Model)
    (ha : Janko1.a ∈ (T : Subgroup Janko1.Model)) :
    Group.rank (((T : Subgroup Janko1.Model).subgroupOf subgroup).map
      (QuotientGroup.mk' (solvableRadical subgroup))) ≤ 2 := by
  let U := (T : Subgroup Janko1.Model).subgroupOf subgroup
  let R := solvableRadical subgroup
  let f := (QuotientGroup.mk' R).comp U.subtype
  have hU : Nat.card U = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (sylow_le T ha)).toEquiv).trans
      (Janko1.SylowTwo.card T)
  have haC : Janko1.a ∈ subgroup := by
    exact mem_centralizer_singleton_iff.mpr rfl
  let z : U := ⟨⟨Janko1.a, haC⟩, ha⟩
  have hz : (z : subgroup) ∈ center subgroup := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  let : CommGroup (center subgroup) := IsMulCommutative.instCommGroup
  have hzR : (z : subgroup) ∈ R :=
    le_solvableRadical (center subgroup) inferInstance inferInstance hz
  have hzf : z ∈ f.ker := (QuotientGroup.eq_one_iff _).mpr hzR
  have hzne : (⟨z, hzf⟩ : f.ker) ≠ 1 := by
    intro he
    apply Janko1.a_ne_one
    exact congrArg (fun x : f.ker => (((x : U) : subgroup) : Janko1.Model)) he
  let : Nontrivial f.ker := ⟨⟨⟨z, hzf⟩, 1, hzne⟩⟩
  have hk : 2 ≤ Nat.card f.ker := Finite.one_lt_card
  have hc := f.ker.card_mul_index
  rw [index_ker, hU] at hc
  have hb : Nat.card f.range ≤ 4 := by nlinarith
  let := Janko1.SylowTwo.elementary T
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (sylow_le T ha)
  let : IsElementaryAbelian 2 (U.map (QuotientGroup.mk' R)) := IsElementaryAbelian.map _
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
  simpa [f, MonoidHom.range_comp] using hb

end Janko1.InvolutionCentralizer
