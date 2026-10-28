module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedAmbientCoreEquality
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedBorelAction
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedResidualFactors
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedResidualCore
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingPairIntersection
/-!
# Original source assembly from the remaining paired geometry

The source Borel action supplies the literal section E₀/Z₀, its order,
and normalization. The source radical and Sylow configuration supply
Q₁ ≤ Rz, TI normal in T, and the omega-center containment. The same C.5
conjugator has a rank-four intersection, so its comparison with the
rank-six E₀ supplies the escaping conjugate used in (l). Finally the
source residual product turns the resulting core equality into the
built paired contradiction.

The remaining premises are the point-core center and commutator geometry,
the center bound in TI/Z₀, and irreducibility of Rz/A. Their independent
source producers use D = 1. This module performs all source and carrier
assembly around those geometric inputs.

Source: Aschbacher--Smith, proof of 14.6.9(k)--(n), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] omegaCore_normal
theorem source_paired_exclusion_of_endgame_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) (hΛT : Λ ≤ (T : Subgroup G)) :
    let R := (T : Subgroup G) ⊓ I
    let B := I ⊓ Mc
    let K := (pResidual 2 I).map I.subtype
    let A := K.pCoreIn 2
    let C := B.pCoreIn 2
    let Kz := (pResidual 2 B).map B.subtype
    let N := Kz.pCoreIn 2
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    let E := (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2)
    let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
    Z₀ ≤ omegaOneCenterAmbient C →
    (∀ r ∈ R, (∀ s ∈ R, ⁅s,r⁆ ∈ Z₀) → r ∈ E) →
    IsIrreducibleSection B A C →
    ⁅A,Kz⁆ ≤ E → ⁅C,Kz⁆ = N →
    C ⊓ centralizer (N : Set G) ≤ Z₀ →
    (∀ c ∈ C, (∀ n ∈ N, ⁅n,c⁆ ∈ Z₀) → c ∈ N) → False := by
  dsimp only
  let R := (T : Subgroup G) ⊓ I
  let B := I ⊓ Mc
  let K := (pResidual 2 I).map I.subtype
  let A := K.pCoreIn 2
  let C := B.pCoreIn 2
  let Kz := (pResidual 2 B).map B.subtype
  let N := Kz.pCoreIn 2
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
  let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
  let E := (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2)
  let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
  intro hZ₀ hcenter hirrC hsmall hcomm hcent hmod
  have hrad := source_paired_point_radical hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex
  have hnormR := (source_paired_point_sylow_configuration hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex hΛT).2
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hMcOver : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩
  have hRB : R ≤ B := le_inf inf_le_right (inf_le_left.trans hTMc)
  obtain ⟨PB,hPB⟩ := c.sylow.exists_map_subtype_eq_of_le
    (show B ≤ I from inf_le_left) (by rw [c.sylow_image]; exact hRB)
  have hCR : C ≤ R := (pCoreIn_le_sylow B PB).trans_eq (hPB.trans c.sylow_image)
  have hQC : Mc.pCoreIn 2 ≤ C := hrad.2.2.1
  have hZ₀Q : Z₀ ≤ omegaOneCenterAmbient (Mc.pCoreIn 2) := hZ₀.trans hrad.2.2.2.2
  obtain ⟨hU₁,hU₂⟩ := source_paired_cores_eq_modules c b i j hij hs hi
  have hgeom := source_paired_irreducible_section hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi
  dsimp only at hgeom
  rw [←hU₁,←hU₂] at hgeom
  obtain ⟨hEcard,_,hBE,hBZ,hirrE⟩ := hgeom
  obtain ⟨hd,hc,_,_⟩ := source_paired_point_centralizer_product
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hA : A = K₁.pCoreIn 2 ⊔ K₂.pCoreIn 2 := by
    change K.pCoreIn 2 = _
    have hjoin : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
    rw [←hjoin]
    exact pCoreIn_sup_of_disjoint_of_commuting 2 K₁ K₂ hd hc
  have hEA : E ≤ A := by
    rw [hA]
    exact sup_le_sup inf_le_left inf_le_left
  have hZS : Z₀ ≤ R := hirrE.1.trans (hEA.trans (hirrC.1.trans hCR))
  let : (Z₀.subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZS).mpr (hRB.trans hBZ)
  have hBA : B ≤ normalizer (A : Set G) :=
    (inf_le_left.trans c.normalizes_residual).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hBC : B ≤ normalizer (C : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨x,hx,_,hfamily⟩ := c.alternating_pair_family_intersection b i j hij hs hi hpairIndex
  have hcardA : Nat.card (A ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) = 16 :=
    hfamily.2.2.2.2.2.2.2.1
  have hcardAE : Nat.card (A ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) < Nat.card E := by
    rw [hcardA,hEcard]
    decide
  have hQ : Mc.pCoreIn 2 = N := source_omegaCore_eq_of_ambient_paired_sections
    hG T hempty hMcOver hMc.le R B A C Kz E N Z₀ inf_le_right
    ((map_subtype_le _).trans inf_le_right) inf_le_left
    ((normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mpr hnormR)
    hCR hQC hEA hZ₀Q hBE hirrE
    ((quotient_center_preimage_le_iff R Z₀ E).mpr hcenter)
    hBA hBC hirrC hsmall hcomm x⁻¹ (hTMc ((T : Subgroup G).inv_mem (hΛT hx)))
    hcardAE hcent hmod
  have hN := source_paired_residual_core_product hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi
  exact source_paired_residual_core_exclusion hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi (hQ.trans hN)
end CFSG.Quasithin.Chapter14.Section06
