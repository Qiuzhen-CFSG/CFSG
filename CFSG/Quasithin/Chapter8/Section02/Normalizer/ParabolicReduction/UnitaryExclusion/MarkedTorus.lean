module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus.QuotientPlacement
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus.CenterPlacement
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Constructing the marked order-five subgroup in H/O₂(H)

The concrete norm-one torus is transported through an actual equivalence
O²(H/O₂(H)) ≃ PSU₃(4) and then through the residual's subtype map.
Its order, centralization of the marked pair, and placement in the image
of H ∩ M are all proved for these literal maps. The last containment
uses HStar's proper-overgroup property on the preimage of the root normalizer.
The final export applies the existing lifting and coprime-action consumer.

These are conditional coordinate reductions, not the completed marked
placement in Lemma 8.2.9. The source must still provide the simultaneous
root-center coordinates for I⁺ = ⟨V⁺,(Vʰ)⁺⟩ and the alignment of the first
root with T⁺ ∩ O²(H⁺). Those premises are
displayed explicitly, rather than replaced by an abstract A₅ or an
assumed five-subgroup upstairs. The corrected cocode layer premise belongs
to the independent representation calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 8.2.9,
the cocode paragraph, printed p.720 (PDF p.737).
-/

public section
open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus
open HermitianForm.BorelTorus HermitianForm.EvenInner HermitianForm.MarkedFiveTorus

variable {H E : Type*} [Group H] [Field E]
  (J : HermitianForm 3 E)

/-- The model is embedded in the literal two-core quotient via its two-residual. -/
@[expose] def residualModelMap
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveSpecialUnitaryMatrixGroup J →* (H ⧸ pCore 2 H) :=
  (pResidual 2 (H ⧸ pCore 2 H)).subtype.comp e.symm.toMonoidHom

theorem residualModelMap_injective
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Function.Injective (residualModelMap J e) :=
  Subtype.coe_injective.comp e.symm.injective

variable [Finite H] [Finite E] [CharP E 2]
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

omit [CharP E 2] in
/-- The root normalizer is proper in H/O₂(H): a normal root image would
be a nontrivial two-subgroup of the trivial two-core of this quotient. -/
theorem residual_root_normalizer_ne_top
    (hcard : Nat.card E = 16) (hconj : ∀ x : E, J.conj x = x ^ 4)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    normalizer
      ((projectiveRoot J hJ).map (residualModelMap J e) : Set (H ⧸ pCore 2 H)) ≠ ⊤ := by
  let R := (projectiveRoot J hJ).map (residualModelMap J e)
  have hfixed : Nat.card {x : E // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  have hR : Nat.card R = 64 := by
    rw [card_map_of_injective (residualModelMap_injective J e)]
    exact HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card
      J hJ 4 hcard hfixed
  intro hn
  have hnormal : R.Normal := normalizer_eq_top_iff.mp hn
  have htwo : IsPGroup 2 R := IsPGroup.of_card (n := 6) hR
  have hle : R ≤ pCore 2 (H ⧸ pCore 2 H) := le_sSup ⟨hnormal, htwo⟩
  rw [pCore_quotient_pCore_eq_bot] at hle
  have hc := card_eq_one.mpr (le_bot_iff.mp hle)
  rw [hR] at hc
  norm_num at hc

/-- Construct all three quotient premises of the lifting consumer from
marked coordinates and a proper root normalizer. No subgroup of order five
is supplied as an input. -/
theorem exists_quotient_five_of_coordinates
    (hcard : Nat.card E = 16) (hconj : ∀ x : E, J.conj x = x ^ 4)
    (T : Subgroup H) (M I : Subgroup H)
    (hlocal : ∀ Y : Subgroup H, T ≤ Y → Y ≠ ⊤ → Y ≤ M)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hpair : (standardPair J hJ).map (residualModelMap J e) =
      I.map (QuotientGroup.mk' (pCore 2 H)))
    (hT : T.map (QuotientGroup.mk' (pCore 2 H)) ≤ normalizer
      ((projectiveRoot J hJ).map (residualModelMap J e) : Set (H ⧸ pCore 2 H))) :
    ∃ D : Subgroup (H ⧸ pCore 2 H), Nat.card D = 5 ∧
      D ≤ M.map (QuotientGroup.mk' (pCore 2 H)) ∧
      D ≤ centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
  let f := residualModelMap J e
  let D := (normOneImage J hJ).map f
  obtain ⟨hsize, hfix, hnorm⟩ := standard_five J hJ hcard hconj
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [card_map_of_injective (residualModelMap_injective J e)]
    exact hsize
  · have hDN : D ≤ normalizer ((projectiveRoot J hJ).map f : Set _) :=
      (map_mono hnorm).trans (le_normalizer_map f)
    exact hDN.trans (quotient_normalizer_le_local_image T M hlocal _
      (QuotientGroup.mk'_surjective _) _ hT (residual_root_normalizer_ne_top J hJ hcard hconj e))
  · rw [← hpair]
    rintro _ ⟨d, hd, rfl⟩ _ ⟨i, hi, rfl⟩
    exact (map_mul f i d).symm.trans ((congrArg f (hfix hd i hi)).trans (map_mul f d i))

variable {G : Type*} [Group G] [Finite G]

/-- Application to the actual source HStar member. The local image is
precisely the image of H ∩ M in H/O₂(H). -/
theorem exists_quotient_five_of_HStar_coordinates
    (hcard : Nat.card E = 16) (hconj : ∀ x : E, J.conj x = x ^ 4)
    (T : Sylow 2 G) (M H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (I : Subgroup H)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hpair : (standardPair J hJ).map (residualModelMap J e) =
      I.map (QuotientGroup.mk' (pCore 2 H)))
    (hT : (T.subtype hH.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer ((projectiveRoot J hJ).map (residualModelMap J e) : Set (H ⧸ pCore 2 H))) :
    ∃ D : Subgroup (H ⧸ pCore 2 H), Nat.card D = 5 ∧
      D ≤ (M.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ∧
      D ≤ centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) :=
  exists_quotient_five_of_coordinates J hJ hcard hconj _ _ I
    (proper_overgroups_of_HStar T M H hH) e hpair hT

open scoped commutatorElement

/-- Actual application to the built lifting consumer: the marked coordinate
calculation discharges its order-five quotient witness, centralizer, and
local-image premises. The independent cocode layer calculation remains explicit. -/
theorem exists_five_centralizing_pair_of_coordinates
    (hcard : Nat.card E = 16) (hconj : ∀ x : E, J.conj x = x ^ 4)
    (T : Sylow 2 H) (M V I U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (h : H) (hh : h ∈ I)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hUV : U ≤ V) (hU : Nat.card U = 8)
    (hlocal : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y ≠ ⊤ → Y ≤ M)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hpair : (standardPair J hJ).map (residualModelMap J e) =
      I.map (QuotientGroup.mk' (pCore 2 H)))
    (hT : (T : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ≤ normalizer
      ((projectiveRoot J hJ).map (residualModelMap J e) : Set (H ⧸ pCore 2 H)))
    (hlayer : ∀ X : Subgroup H, X ≤ M → Nat.card X = 5 →
      X ≤ normalizer (I : Set H) →
      X.map (QuotientGroup.mk' (pCore 2 H)) ≤ centralizer
        (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) →
      ⁅I.pCoreIn 2, X⁆ ≤ U) :
    ∃ X : Subgroup H, X ≤ M ∧ Nat.card X = 5 ∧
      X ≤ normalizer (V : Set H) ∧ X ≤ normalizer (I.pCoreIn 2 : Set H) ∧
      X ≤ centralizer (U : Set H) ∧ X ≤ centralizer (I : Set H) := by
  obtain ⟨D, hD, hDM, hDC⟩ := exists_quotient_five_of_coordinates
    J hJ hcard hconj (T : Subgroup H) M I hlocal e hpair hT
  obtain ⟨X, hXM, hX, _, hXV, hXP, hXU, hXI⟩ :=
    UnitaryExclusion.exists_five_centralizing_pair T M V I U h hh hTV hgen
      hTI hUV hU D hD hDM hDC hlayer
  exact ⟨X, hXM, hX, hXV, hXP, hXU, hXI⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus
