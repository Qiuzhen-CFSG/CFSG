module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationCases
public import Theory.GroupTheory.CComponent.A5PlaneCenter

/-!
# Excluding three-centers in the original Cartan-container reduction

The original line normalizer is a two-local subgroup, so its three-rank is
at most two. The marked intersection A ∩ J = B lies in the old A₅ residual.
Apply the cubic-plane center theorem inside this actual normalizer, using
the literal subgroup inclusions and two-core quotients. Consequently the
center of J/O₂(J) has order prime to three; this excludes the triple-cover
possibilities while retaining the same containing component J.

The final consumer starts with the original tensor and nonzero Cartan-core
hypotheses and discharges A₅ recognition internally. The other established
normalization cases are retained from the preceding extension. No containing
model shortlist or Cartan-normalization callback is assumed.

Source: Aschbacher–Smith, Proposition 9.3.1, second reduction, printed
p.732 of the combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original line normalizer supplies the ambient three-rank bound, so
the literal containing quotient has center of order prime to three. -/
theorem cartan_container_center_coprime_three
    {H : Subgroup G}
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hAJB : A ⊓ J = B)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J) :
    Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) := by
  let N := normalizer (m.tensorLine : Set G)
  let K0 := (pResidual 2 H).map H.subtype
  let K := K0.subgroupOf N
  let I := J.subgroupOf N
  let C := A.subgroupOf N
  have hKN : K0 ≤ N := hKJ.trans hJU
  let b : K ≃* K0 := subgroupOfEquivOfLe hKN
  let ec : C ≃* A := subgroupOfEquivOfLe hAU
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.of_injective ec.toMonoidHom ec.injective
  have hC9 : Nat.card C = 9 := (Nat.card_congr ec.toEquiv).trans hA9
  let ek : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eK
  have hCIK : C ⊓ I ≤ K := by
    intro x hx
    apply hBK
    rw [←hAJB]
    exact hx
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  let := hnJ
  have hc := Theory.GroupTheory.A5PlaneCenter.center_twoCore_quotient_coprime_three
    I K C hJ (hN.stronglyQuasithin 3 (by decide) (by decide)) hC9 (comap_mono hKJ) hCIK ek
  let j : I ≃* J := subgroupOfEquivOfLe hJU
  let ej : (I ⧸ pCore 2 I) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  rwa [Nat.card_congr (centerCongr ej).toEquiv] at hc

/-- Retain the actual containing component and exclude all three-divisible
centers, with the original A₅ recognition discharged. -/
theorem nonzero_core_cartan_normalization_remaining_cases_center_three
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ (IsQuasisimple (J ⧸ pCore 2 J) ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) ∧
      ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∧
      Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hout,hpsl⟩ :=
    m.nonzero_core_cartan_normalization_remaining_cases hH hlarge A B hAB
      hA9 hAe hB3 hBK hBC hcore
  · exact Or.inl hAK
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  let := hAe
  exact Or.inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hout,hpsl,
    m.cartan_container_center_coprime_three eK A B J hA9
      (hAB.trans m.borel_normalizes_tensorLine) hBK hAJB hJU hJ hnJ hKJ.le⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
