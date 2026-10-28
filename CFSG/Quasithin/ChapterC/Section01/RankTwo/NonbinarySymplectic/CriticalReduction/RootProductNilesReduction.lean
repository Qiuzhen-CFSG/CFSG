module
public import Glauberman.PushingUpSL2DegreeReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesNaturalLayers

/-!
# Power reduction of the same original F₀ quotient

The original F₀ central-chief quotient now admits the source half-period
reduction. Either its Baumann Sylow image has class at most two, or a
literal power of its given automorphism produces a further quotient
retaining exact class three, diagram parameter two and the original SL₂ marking. The removed
kernel has only central chief factors and is centralized by the residual.
Both previously constructed natural factors and all central attachments
remain in the same original witness.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 6.4--6.6,
pp.53--55, used in MS93 (5.1), p.913. The nonabelian exclusion,
original commutator argument and distance-two
assembly remain to be proved.
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

theorem Input.replacement_root_product_F0_niles_power_reduction
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
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        generalizedFitting C = pCore 2 C ∧
        (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype ∧
        ∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Glauberman.baumannSubgroup (Q d.radical t) ∧
          Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ ∧
          NoCharacteristicNormal (P : Subgroup C) ∧
          (pCore 2 C).map C.subtype = C ⊓ Q d.radical a ∧
          U d.radical a ≤ C ∧
          (U d.radical a).subgroupOf C ≤ omegaCenterIn (pCore 2 C) ∧
          Nonempty ((P ⧸ (pCore 2 C).subgroupOf (P : Subgroup C)) ≃* Multiplicative E.Carrier) ∧
          (pCore 2 C).relIndex (P : Subgroup C) = Nat.card F ∧
          (∀ α : MulAut P,
            (omegaCenterIn (pCore 2 C)).subgroupOf (P : Subgroup C) ≤
              invariantNormalKernel (P : Subgroup C) α →
            invariantNormalKernel (P : Subgroup C) α =
              ⨅ m : ℤ, ((pCore 2 C).subgroupOf (P : Subgroup C)).map ((α ^ m).toMonoidHom)) ∧
          ∃ α : MulAut P,
            let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
            let q := QuotientGroup.mk' N
            ∃ s : NoncentralChiefRefinement.SeriesOn N, (∀ i, s.Central i) ∧
              N ≤ pCore 2 C ∧
              pResidual 2 C ≤ centralizer (N : Set C) ∧
              Nonempty (((C ⧸ N) ⧸ pCore 2 (C ⧸ N)) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
              Nonempty (((C ⧸ N) ⧸ (pCore 2 C).map q) ≃* (C ⧸ pCore 2 C)) ∧
              generalizedFitting (C ⧸ N) = pCore 2 (C ⧸ N) ∧
              Order.HasUniqueMaximalOver ((P : Subgroup C).map q) ⊤ ∧
              ∃ β : MulAut ((P : Subgroup C).map q),
                NoInvariantNormal ((P : Subgroup C).map q) β ∧
                Glauberman.NilesIntersectionDiagram (Nat.card F) ((P : Subgroup C).map q) β ∧
                Glauberman.NilesFullIntersectionDiagram (Nat.card F) ((P : Subgroup C).map q) β ∧
                Glauberman.NilesIntervalDiagram ((P : Subgroup C).map q) β ∧
                Glauberman.NilesPointDiagram (Nat.card F) ((P : Subgroup C).map q) β ∧
                Glauberman.NilesGapDiagram (Nat.card F) ((P : Subgroup C).map q) β ∧
                Glauberman.NilesNormalLayerDiagram (Nat.card F) ((P : Subgroup C).map q) β ∧
                Glauberman.NilesExactLayerDiagram (Nat.card F) ((P : Subgroup C).map q) β ∧
                (∃ e : ((C ⧸ N) ⧸ pCore 2 (C ⧸ N)) ≃*
                  Matrix.SpecialLinearGroup (Fin 2) E.Carrier,
                  Glauberman.NilesCenterCoordinates e ∧ Glauberman.NilesNaturalFiltration e ∧
                    Glauberman.NilesPowerReduction e ((P : Subgroup C).map q) β) ∧
                ((P : Subgroup C).map q).lowerCentralSeries 3 = ⊥ ∧
                Group.nilpotencyClass ((P : Subgroup C).map q) ≤ 3 ∧
                ⁅centerIn (pCore 2 (C ⧸ N)),((P : Subgroup C).map q)⁆ ⊔
                  center (C ⧸ N) = centerIn ((P : Subgroup C).map q) ∧
                (center (C ⧸ N)).relIndex (centerIn (pCore 2 (C ⧸ N))) = Nat.card F ^ 2 ∧
                (center (C ⧸ N)).relIndex (centerIn ((P : Subgroup C).map q)) = Nat.card F ∧
                (IsMulCommutative (pCore 2 (C ⧸ N)) →
                  Group.nilpotencyClass P ≤ 2 ∧
                    Group.nilpotencyClass ((P : Subgroup C).map q) ≤ 2) := by
  obtain ⟨E,hE,I,hI,C,hCI,hCn,hgen,he,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hformula,α,s,hcentral,hNQ,hcentralizes,
    ⟨eQ⟩,hecore,hfitQ,huniqueQ,β,hβ,hdiagram,hfull,hinterval,hpoint,hgap,hlayers,hparams,⟨e0,hcenter,hnatural⟩,hclassZero,hclassBound,hcover,hiQ,hiS,hbranch⟩ :=
    h.replacement_root_product_F0_niles_natural_layers d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion (hCI.trans hI)) (inclusion_injective _)
  let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
  let P' := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hEc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hpower := Glauberman.original_sl2_power_reduction e0 h.nonbinary hEc P' β huniqueQ hfitQ hβ
  exact ⟨E,hE,I,hI,C,hCI,hCn,hgen,he,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hformula,α,s,hcentral,hNQ,hcentralizes,
    ⟨eQ⟩,hecore,hfitQ,huniqueQ,β,hβ,hdiagram,hfull,hinterval,hpoint,hgap,hlayers,hparams,⟨e0,hcenter,hnatural,hpower⟩,
    hclassZero,hclassBound,hcover,hiQ,hiS,hbranch⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
