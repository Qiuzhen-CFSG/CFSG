module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import Theory.GroupTheory.CComponent.Structure
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Commutator generation on the actual section

Perfectness lifts generation through the solvable two-core kernel. The
component commutator dichotomy then turns a nontrivial component action into
`L = [L,A]`, the identity needed for the symmetric-cover argument in (n).
After the reduction to `H = LT`, nontriviality follows from the vanishing
two-core of the star quotient: a two-subgroup centralizing the two-residual
lies in the two-core, as one sees by taking its conjugate span in a Sylow
subgroup. No separate noncommutation witness is needed in this case.
All actions below are the conjugation representation of `SectionAction` on
the literal quotient, and all subnormality is relative to `H`.

The seed-centralization test is also available for the larger-field exclusion:
a normal component centralizing `Z_S` centralizes `⟨Z_S^H⟩`, contradicting a
nontrivial star image in the faithful action. Model-specific module arguments
must still establish the required seed containment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(k)–(n), printed p.1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G]

private theorem pGroup_centralizing_residual_le_core [Finite G]
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) (hA : IsPGroup p A)
    (hcent : A ≤ centralizer (pResidual p G : Set G)) : A ≤ pCore p G := by
  obtain ⟨T, hAT⟩ := hA.exists_le_sylow
  let X := localSpan A (T : Subgroup G)
  have hXT : X ≤ T := conjugateSpanBy_le_self hAT
  have hXC : X ≤ centralizer (pResidual p G : Set G) := by
    apply conjugateSpanBy_le hcent
    rw [normalizer_eq_top]
    exact le_top
  have hRX : pResidual p G ≤ normalizer (X : Set G) :=
    (le_centralizer_iff.mp hXC).trans (Subgroup.centralizer_le_normalizer _)
  have hn : X.Normal := by
    rw [← normalizer_eq_top_iff]
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top T]
    exact sup_le hRX (le_normalizer_conjugateSpanBy A _)
  exact (le_conjugateSpanBy A _).trans (le_sSup ⟨hn, T.isPGroup'.to_le hXT⟩)

private theorem not_centralizes_of_pGroup_supplement [Finite G]
    {p : ℕ} [Fact p.Prime] (L R A : Subgroup G) [L.Normal]
    (hR : IsPGroup p R) (hgen : L ⊔ R = ⊤)
    (hA : IsPGroup p A) (hne : A ≠ ⊥) (hcore : pCore p G = ⊥) :
    ¬ A ≤ centralizer (L : Set G) := by
  intro hcent
  have hres : pResidual p G ≤ L :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top L R hR hgen⟩
  exact hne (le_bot_iff.mp ((pGroup_centralizing_residual_le_core A hA
    (hcent.trans (centralizer_le hres))).trans_eq hcore))

private theorem perfect_le_of_map_le
    [Finite G] {D : Type*} [Group D] (f : G →* D) [Group.IsSolvable f.ker]
    (P K : Subgroup G) [Group.IsPerfect P] (hK : K.IsSubnormal)
    (hmap : P.map f ≤ K.map f) : P ≤ K := by
  have hPS : P ≤ K ⊔ f.ker := le_sup_left.trans ((map_le_map_iff').mp hmap)
  let : Group.IsSolvable (f.ker.subgroupOf (K ⊔ f.ker)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show f.ker ≤ K ⊔ f.ker from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show f.ker ≤ K ⊔ f.ker from le_sup_right)).injective
  have hR : solvableResidual ↥(K ⊔ f.ker) ≤ K.subgroupOf (K ⊔ f.ker) := by
    let : (f.ker.subgroupOf (K ⊔ f.ker)).Normal := inferInstance
    exact hK.subgroupOf.solvableResidual_le_of_sup_eq_top
      (f.ker.subgroupOf (K ⊔ f.ker)) (codisjoint_subgroupOf_sup K f.ker).eq_top
  exact (le_map_solvableResidual_of_isPerfect P (K ⊔ f.ker) hPS).trans (by
    simpa only [map_subgroupOf_eq_of_le le_sup_left] using map_mono (f := (K ⊔ f.ker).subtype) hR)

/-- Lift commutator generation from the two-core quotient using perfectness and relative subnormality. -/
theorem commutator_eq_of_star_eq [Finite G]
    (H L A : Subgroup G) (hLH : L ≤ H) (hAH : A ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    (hAL : A ≤ normalizer (L : Set G))
    (hstar : starImage H L = ⁅starImage H L, starImage H A⁆) : L = ⁅L, A⁆ := by
  let P := L.subgroupOf H
  let B := A.subgroupOf H
  let f := QuotientGroup.mk' (pCore 2 H)
  let := hL.perfect
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable f.ker := by
    dsimp [f]
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hC : ⁅P, B⁆ ≤ P := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    simpa only [P, B, map_commutator, map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hAH] using le_normalizer_iff_commutator_le_left.mp hAL
  have hn : (⁅P, B⁆.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hC).mpr (normalizer_commutator_ge_left P B)
  have hs : (⁅P, B⁆ : Subgroup H).IsSubnormal := by
    have hh := hn.isSubnormal.trans' hL.subnormal
    rwa [map_subgroupOf_eq_of_le hC] at hh
  have he : P = ⁅P, B⁆ := le_antisymm
    (perfect_le_of_map_le f P ⁅P, B⁆ hs (by
      rw [map_commutator]
      exact hstar.le)) hC
  have hh := congrArg (map H.subtype) he
  simpa only [P, B, map_commutator, map_subgroupOf_eq_of_le hLH,
    map_subgroupOf_eq_of_le hAH] using hh

theorem starImage_eq_bot_of_centralizes
    (H U Z A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hAU : A ≤ centralizer (U : Set G)) :
    starImage H A = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨a, ha, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) a = 1
  apply action.faithful
  ext w
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
  have huw : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) = w :=
    congrArg Additive.ofMul hu
  rw [← huw]
  rw [action.on_representatives]
  have hc : (a : G) * (u : G) = (u : G) * (a : G) :=
    (mem_centralizer_iff.mp (hAU ha) u u.property).symm
  have he : (⟨(a : G) * (u : G) * (a : G)⁻¹,
      le_normalizer_iff.mp action.normalizes a a.property u u.property⟩ : U) = u := by
    apply Subtype.ext
    simp only [hc, mul_inv_cancel_right]
  rw [he]
  simp

theorem starImage_eq_bot_of_seed_centralized
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hHL : H ≤ normalizer (L : Set G)) (hseed : ZS ≤ centralizer (L : Set G)) :
    starImage H L = ⊥ := by
  have hHU : localSpan ZS H ≤ centralizer (L : Set G) := by
    apply conjugateSpanBy_le hseed
    exact hHL.trans (normalizer_le_normalizer_centralizer _)
  exact starImage_eq_bot_of_centralizes H (localSpan ZS H) Z L action
    (le_centralizer_iff.mp hHU)

theorem starImage_commutator
    (H L A : Subgroup G) (hLH : L ≤ H) (hAH : A ≤ H) :
    starImage H ⁅L, A⁆ = ⁅starImage H L, starImage H A⁆ := by
  have hCH : ⁅L, A⁆ ≤ H := (Subgroup.commutator_le_sup L A).trans (sup_le hLH hAH)
  have he : ⁅L.subgroupOf H, A.subgroupOf H⁆ = (⁅L, A⁆).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le hCH]
  simp only [starImage, ← he, map_commutator]

/-- Noncommuting operators on the actual section force commutator generation of a normalized component with quasisimple star image. -/
theorem commutator_eq_of_noncommuting_section_action [Finite G]
    (H U Z L A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z)
    (hLH : L ≤ H) (hAH : A ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    (hquasi : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hAL : A ≤ normalizer (L : Set G))
    (hmoves : ∃ l : starImage H L, ∃ a : starImage H A,
      ∃ u : Additive (U ⧸ Z.subgroupOf U),
        action.representation l (action.representation a u) ≠
          action.representation a (action.representation l u)) : L = ⁅L, A⁆ := by
  have hc : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) (starImage H L) :=
    ⟨hL.subnormal.map (QuotientGroup.mk'_surjective _), hquasi⟩
  have hne : ⁅starImage H L, starImage H A⁆ ≠ ⊥ := by
    intro hb
    obtain ⟨l, a, u, h⟩ := hmoves
    have he : (a : H ⧸ pCore 2 H) * l = l * a :=
      mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hb l.property) a a.property
    apply h
    change (action.representation l * action.representation a) u =
      (action.representation a * action.representation l) u
    rw [← map_mul, ← map_mul, he]
  have hle : ⁅starImage H L, starImage H A⁆ ≤ starImage H L := by
    rw [← starImage_commutator H L A hLH hAH]
    exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp hAL))
  rcases hc.commutator_dichotomy (starImage H A) with hb | he
  · exact (hne hb).elim
  · apply commutator_eq_of_star_eq H L A hLH hAH hL hAL
    exact le_antisymm (he ▸ le_iSup_conjugates _ _) hle

/-- In a reduced local group `H = LT`, a nontrivial elementary two-subgroup
of `H/O₂(H)` cannot centralize the quasisimple component image. The residual
and Sylow argument puts any such centralizing subgroup in `O₂(H/O₂(H)) = 1`;
the component dichotomy and perfect lifting then give `L = [L,A]`. -/
theorem commutator_eq_of_reduced_two_subgroup [Finite G] (H L T A : Subgroup G)
    (hgen : H = L ⊔ T) (hn : H ≤ normalizer (L : Set G))
    (hT : IsPGroup 2 T) (hAH : A ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    (hquasi : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hA : IsElementaryTwo (starImage H A)) : L = ⁅L, A⁆ := by
  have hLH : L ≤ H := hgen ▸ le_sup_left
  have hTH : T ≤ H := hgen ▸ le_sup_right
  have hnorm : (L.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLH).mpr hn
  let := hnorm
  let : (starImage H L).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  have hjoin : starImage H L ⊔ starImage H T = ⊤ := by
    have hi : L.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLH, map_subgroupOf_eq_of_le hTH,
        ← MonoidHom.range_eq_map, range_subtype, ← hgen]
    rw [starImage, starImage, ← Subgroup.map_sup, hi,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hTp : IsPGroup 2 (starImage H T) :=
    hT.comap_subtype.map (QuotientGroup.mk' (pCore 2 H))
  let := hA.2
  have hne : ⁅starImage H L, starImage H A⁆ ≠ ⊥ := by
    intro hb
    have haC : starImage H A ≤ centralizer (starImage H L : Set (H ⧸ pCore 2 H)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)
    exact not_centralizes_of_pGroup_supplement (starImage H L) (starImage H T)
      (starImage H A) hTp hjoin (IsElementaryAbelian.isPGroup 2 _)
      hA.1 (pCore_quotient_pCore_eq_bot 2) haC
  have hc : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) (starImage H L) :=
    ⟨hL.subnormal.map (QuotientGroup.mk'_surjective _), hquasi⟩
  have hle : ⁅starImage H L, starImage H A⁆ ≤ starImage H L := by
    rw [← starImage_commutator H L A hLH hAH]
    exact map_mono (comap_mono
      (le_normalizer_iff_commutator_le_left.mp (hAH.trans hn)))
  rcases hc.commutator_dichotomy (starImage H A) with hb | he
  · exact (hne hb).elim
  · apply commutator_eq_of_star_eq H L A hLH hAH hL (hAH.trans hn)
    exact le_antisymm (he ▸ le_iSup_conjugates _ _) hle

/-- The commutator-generation input for `strong_from_symmetric_cover`,
derived after (k)–(l) from the actual best-offender assertion of (h).
The component normality and quasisimple star image belong to that reduction. -/
theorem commutator_eq_of_reduced_bestOffender [Finite G]
    (H L Y0 T ZS Z A : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hgen : H = L ⊔ (Y0 ⊔ T)) (hYL : Y0 ≤ L)
    (hn : H ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T) (hAH : A ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    (hquasi : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hA : IsBestOffender action.representation (starImage H A)) : L = ⁅L, A⁆ := by
  rw [← sup_assoc, sup_eq_left.mpr hYL] at hgen
  exact commutator_eq_of_reduced_two_subgroup H L T A hgen hn hT hAH hL hquasi hA.1

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
