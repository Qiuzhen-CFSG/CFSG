module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.CubicObstruction
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneRadical
public import Theory.Representation.BinaryParabolicExteriorSquare.MarkedCubic

/-!
# The common cubic and the literal radical section

Lift the specified natural cubic into L₀ through the original two-group
kernel. Its cyclic subgroup has order three and maps onto the same normal
cubic in the chief-count quotient. The natural and exterior matrices then
supply both actions of that one actor; the dual action is inherited.

The upper radical coordinates come from its image under the original
matrix quotient. Conjugation of the two upper-right columns proves the
paired cubic action. The terminal application therefore needs neither an
independently marked radical representation nor separately chosen cubic
actors on the four strata. It applies the resulting six-factor accounting
to the actual H-chief-series exclusion on H_C/V_H.

The original natural/exterior and dual markings, the local matrix images,
the nine-factor tensor bound and the critical-pair geometry remain explicit
obligations of qt-d-138-linear-four-source. Earlier 13.8.27(b) belongs to
qt-d-138-six-g2-source; qt-d-1381-source owns final source assembly. These
conditional results do not complete 13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.29–31 and the terminal argument, printed pp.964–966.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- Construct one common cubic in the original L₀, with its exact natural matrix. -/
theorem source_common_cubic
    (H D QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hcubic : cubicElement ∈ (D.subgroupOf H).map π) :
    ∃ (A : Subgroup G) (hAD : A ≤ D) (a : A), Nat.card A = 3 ∧
      (∀ b, b ∈ zpowers a) ∧ (π (inclusion (hAD.trans hDH) a)).val = planeCubic := by
  let πD := π.comp (inclusion hDH)
  have hk : πD.ker = QH.subgroupOf D := by
    ext x
    change inclusion hDH x ∈ π.ker ↔ (x:G) ∈ QH
    rw [hker]
    rfl
  have hc : cubicElement ∈ πD.range := by
    obtain ⟨x,hx,he⟩ := hcubic
    exact ⟨⟨x,hx⟩,he⟩
  obtain ⟨B,b,hB,hb,hmat⟩ := exists_marked_cubic πD
    (by rw [hk]; exact hQH.comap_subtype) hc
  let A := B.map D.subtype
  have hAD : A ≤ D := map_subtype_le B
  let E : B ≃* A := B.equivMapOfInjective D.subtype D.subtype_injective
  have hA : Nat.card A = 3 := (Nat.card_congr E.toEquiv).symm.trans hB
  refine ⟨A,hAD,E b,hA,?_,congrArg Subtype.val hmat⟩
  intro x
  obtain ⟨n,hn⟩ := hb (E.symm x)
  refine ⟨n,?_⟩
  change E b ^ n = x
  change b ^ n = E.symm x at hn
  exact (map_zpow E b n).symm.trans ((congrArg E hn).trans (E.apply_symm_apply x))

/-- The common actor and radical action are derived from the original matrix quotient. -/
theorem source_linear_four_exclusion_of_matrix_sections
    {K : Type*} [Group K] [Finite K]
    (H D UH V1 VH HC QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (hQHD : QH ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h v, ρ h v = Matrix.mulVec (π h).val v)
    (hexterior : ∀ h v, ξ h v = exteriorMap (π h).val v)
    (hcubic : cubicElement ∈ (D.subgroupOf H).map π)
    (f : D →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X))
    (Z U V C Q R : NormalNode D)
    (hZdef : Z.val = V1.subgroupOf D) (hUdef : U.val = UH.subgroupOf D)
    (hVdef : V.val = VH.subgroupOf D) (hCdef : C.val = HC.subgroupOf D)
    (hQdef : Q.val = QH.subgroupOf D)
    (hZ : IsCentral ⊥ Z) (hterminal : HasNoTwoChiefFactors (D ⧸ R.val))
    (Rg : Subgroup G) (hRdef : R.val = Rg.subgroupOf D) (hRg : IsPGroup 2 Rg)
    (hRD : Rg ≤ D) (hQR : QH ⊓ D ≤ Rg)
    (hradical : (Rg.subgroupOf H).map π = PlaneRadical.radical)
    (hnine : ∀ t : ChiefSeries D, t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (Kc Uγ : Subgroup G) (hKcH : Kc ≤ H) (hDK : D ≤ Kc)
    [IsElementaryAbelian 2 Uγ]
    (hQHdef : QH = H.pCoreIn 2)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC,Uγ⁆ ≤ HC ⊓ Uγ) (hUγH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* BinaryLinear.OuterCyclic.LinearGroup 4)
    (hKc : IsPPerfect 2 Kc)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (Kc.subgroupOf H).subtype)) : False := by
  obtain ⟨A,hAD,a,hA,ha,hmat⟩ := source_common_cubic H D QH hDH hQH π hker hcubic
  have hAc : Nat.card (A.subgroupOf D) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv).trans hA
  have hAX := cubic_image_eq_normal_three f hp (A.subgroupOf D) hAc X hX hq
  have hDR : D ≤ normalizer (Rg : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hRD).mp
    rw [←hRdef]
    exact R.property
  obtain ⟨τ,dradical,_,hτ⟩ := PlaneRadical.exists_section H D Rg QH hDH hRD hDR hQR π hker hradical
  exact source_linear_four_exclusion_of_cubic_sections
    H D UH V1 VH HC QH A hDH hAD hA hQH hVC hQHD ρ d ddual ξ dexterior
    a ha (fun v => (hnatural _ v).trans (by rw [hmat]))
    (fun v => (hexterior _ v).trans (by rw [hmat]))
    f hf hp X hX hq hAX Z U V C Q R hZdef hUdef hVdef hCdef hQdef hZ hterminal
    Rg hRdef hRg τ dradical (hτ (inclusion hAD a) hmat) hnine
    Kc Uγ hKcH hDK hQHdef hU hstar hintersection hcomm hUγH hcover e hKc hKonto

end CFSG.Quasithin.Chapter13.Section08.LinearFour
