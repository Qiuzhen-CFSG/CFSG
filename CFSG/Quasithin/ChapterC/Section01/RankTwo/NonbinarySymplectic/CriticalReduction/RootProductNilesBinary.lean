module
public import Glauberman.PushingUpSL2DegreeBinary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesReduction

/-!
# Class two for the original Baumann Sylow

The characteristic-two natural-extension argument excludes the reduced
class-three quotient at every original nonbinary degree. Its class-two
bound lifts through the central-chief kernel, which the original residual
centralizes. The literal F₀ Sylow map then gives the bound for the original
Baumann subgroup of the replacement edge, retaining all central layers.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem B, p.28,
Theorem 6.9, p.58, and the final kernel lift on p.62; MS93 (5.1), p.913.
The original commutator conclusion, root-product contradiction, selected
paths, terminal exclusions and distance-two assembly are subsequent steps.
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

theorem Input.replacement_root_product_baumann_class_two
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
    (Glauberman.baumannSubgroup (Q d.radical t)).lowerCentralSeries 2 = ⊥ ∧
      Group.nilpotencyClass (Glauberman.baumannSubgroup (Q d.radical t)) ≤ 2 := by
  obtain ⟨E,hE,I,hI,C,hCI,hCn,hgen,he,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hformula,α,s,hcentral,hNQ,hcentralizes,
    ⟨eQ⟩,hecore,hfitQ,huniqueQ,β,hβ,hdiagram,hfull,hinterval,hpoint,hgap,hlayers,hparams,
    ⟨e0,hcenter,hnatural,hpower⟩,hclassZero,hclassBound,hcover,hiQ,hiS,hbranch⟩ :=
    h.replacement_root_product_F0_niles_power_reduction d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion (hCI.trans hI)) (inclusion_injective _)
  let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
  let q := QuotientGroup.mk' N
  let P' := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hEc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hclass := Glauberman.original_sl2_class_two e0 h.nonbinary hEc P' β huniqueQ hfitQ hβ
  have htop := lowerCentralSeries_eq_bot_of_image P hno q
    (by simpa only [q,QuotientGroup.ker_mk'] using hcentralizes) 2 hclass.1
  have hPtwo : (P : Subgroup C).lowerCentralSeries 2 = ⊥ := by
    rw [←top_subtype_lowerCentralSeries,htop,Subgroup.map_bot]
  have hBtwo : (Glauberman.baumannSubgroup (Q d.radical t)).lowerCentralSeries 2 = ⊥ := by
    rw [←hP,←Subgroup.map_lowerCentralSeries,hPtwo,Subgroup.map_bot]
  let B := Glauberman.baumannSubgroup (Q d.radical t)
  let : Group.IsNilpotent B := (Subgroup.isNilpotent_iff_lowerCentralSeries B).mpr ⟨2,hBtwo⟩
  refine ⟨hBtwo,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp ?_⟩
  apply map_injective (f := B.subtype) Subtype.val_injective
  rw [top_subtype_lowerCentralSeries,Subgroup.map_bot]
  exact hBtwo

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
