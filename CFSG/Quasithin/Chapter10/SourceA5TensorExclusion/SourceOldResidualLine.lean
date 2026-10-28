module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognition
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldCartanOrbit

/-!
# Cartan normalization fixes the original tensor line

The original H-star subgroup fixes the center involutions of the original
Sylow subgroup. If the Cartan normalizes its old residual, it also normalizes
the residual's centralizer. The Cartan orbit of a center involution spans the
original tensor line, so the old residual centralizes that entire line.

The second theorem applies this to the actual Cartan of order nine and its
line-centralizing Hall subgroup of order three. Their different orders
supply the required noncentral cubic action. Cartan normalization remains
the independent input supplied by the source model analysis.

Source: Aschbacher--Smith Proposition 9.3.1, first reduction, printed p.732.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- A normalizing cubic Cartan carries a fixed Sylow-center involution
to generators of the original tensor line. -/
theorem old_residual_centralizes_tensorLine_of_cubic_normalizes
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A : Subgroup G) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (a : G) (haA : a ∈ A) (ha3 : a ^ 3 = 1)
    (haC : a ∉ centralizer (m.tensorLine : Set G))
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  obtain ⟨z,hz2,hzU,hzT⟩ := m.exists_central_involution_tensorLine
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz,orderOf_one] at hz2
    omega
  have hzΩ : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨m.tensorLine_le_sylow hzU,hz2 ▸ pow_orderOf_eq_one z,hzT⟩
  have hzK : z ∈ centralizer (K : Set G) := by
    intro k hk
    exact ((m.hstar_centralizes_sylowOmega hH) ((map_subtype_le _) hk) z hzΩ).symm
  apply le_centralizer_iff.mpr
  rw [←m.tensorLine_cartan_orbit A hAU a haA ha3 haC z hzU hz1]
  exact iSup_conjugates_le_of_le_normalizer (zpowers z) A (centralizer (K : Set G))
    (zpowers_le.mpr hzK) (hAK.trans (normalizer_le_normalizer_centralizer K))

/-- Apply the first reduction of 9.3.1 to the actual order-nine Cartan
and its order-three line-centralizing subgroup. -/
theorem old_residual_centralizes_tensorLine_of_cartan_normalizes
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  have hnA : ¬ A ≤ centralizer (m.tensorLine : Set G) := by
    intro hc
    have he : B = A := hBC.trans (inf_eq_left.mpr hc)
    rw [he,hA9] at hB3
    omega
  obtain ⟨a,haA,haC⟩ := Set.not_subset.mp hnA
  let := hAe
  exact m.old_residual_centralizes_tensorLine_of_cubic_normalizes hH A
    (hAB.trans m.borel_normalizes_tensorLine) a haA
    (elemPow_eq_one_of_isElementaryAbelian a haA) haC hAK

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
