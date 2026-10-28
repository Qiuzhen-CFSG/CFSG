module
public import Theory.GroupTheory.SylowElementaryCenterLifting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesDiagram

/-!
# The full original Baumann center is elementary

The Niles quotient has elementary Sylow center. Squares of the full original
center lie in the central-chief kernel, and characteristic-normal exclusion
kills them because the residual centralizes that kernel. Transport through
the literal F₀ Sylow inclusion retains every original central attachment.

Source: Niles (1979), pp.46,62, in the MS93 (5.1) application on p.913.
This supplies the center premise in RootProductCommutator.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit NilesRankOneKernel
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_root_product_baumann_center
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    omegaCenterIn (Glauberman.baumannSubgroup (Q d.radical t)) =
      centerIn (Glauberman.baumannSubgroup (Q d.radical t)) := by
  obtain ⟨E,hE,I,hI,C,hCI,hCn,hgen,he,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hformula,α,s,hcentral,hNQ,hcentralizes,
    ⟨eQ⟩,hecore,hfitQ,huniqueQ,β,hβ,hdiagram,hbranch⟩ :=
    h.replacement_root_product_F0_niles_diagram d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion (hCI.trans hI)) (inclusion_injective _)
  let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
  let q := QuotientGroup.mk' N
  obtain ⟨x,hx,hpair,hinter,hnum,homega,homegaT,hcenter,hcenterT,hcenterQ,hrest⟩ := hdiagram
  have hz : omegaCenterIn (P : Subgroup C) = centerIn (P : Subgroup C) :=
    omegaCenterIn_eq_centerIn_of_image P hno q
      (by simpa only [q,QuotientGroup.ker_mk'] using hcentralizes) hcenter
  apply le_antisymm
  · intro x hx
    exact ⟨((mem_omegaCenterIn_iff _ _).mp hx).1,
      ((mem_omegaCenterIn_iff _ _).mp hx).2.1⟩
  · intro z hzB
    obtain ⟨y,hy,rfl⟩ := hP.symm ▸ hzB.1
    have hyc : y ∈ centerIn (P : Subgroup C) := by
      refine ⟨hy,?_⟩
      intro u hu
      apply Subtype.val_injective
      exact hzB.2 u.val (hP ▸ mem_map_of_mem C.subtype hu)
    rw [←hz] at hyc
    have hm := mem_map_of_mem C.subtype hyc
    rwa [Glauberman.omegaCenterIn_map_injective _ C.subtype C.subtype_injective,hP] at hm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
