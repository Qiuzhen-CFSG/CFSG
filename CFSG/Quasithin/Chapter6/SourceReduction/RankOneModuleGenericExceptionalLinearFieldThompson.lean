module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinear
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreSupplement

/-!
# The actual KS quotient in the field-size argument

In 5.1.20, K is the embedded O²(H) and S is a subgroup of T. Thus K is
normal in KS, and KS/K is a two-group. The original K/O₂(K) ≅ PSL₃(4)
marking identifies the relative K-image modulo O₂(KS) with a quasisimple
group. It follows that this image is F*(KS/O₂(KS)) and that the quotient
above F* is a two-group. This discharges the documented extra premise of
the proved E.5.4 variant at its actual source use.

The application below retains characteristic two, quotient rank and the
faithful FF-module exclusion as explicit inputs. It proves that the
literal K centralizes the higher Thompson center in KS when J(S) is not
normal. Constructing the source S and proving those remaining inputs is
part of the numerical branch, not asserted here.

Source: Aschbacher--Smith, 5.1.20, printed p.644, and E.5.4, p.244.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H S : Subgroup G}

/-- The source group KS with K = O²(H) embedded in G. -/
abbrev linearSupplement (H S : Subgroup G) : Subgroup G := residual H ⊔ S

/-- The literal S = (T∩L)O₂(LT) in 5.1.20. Its Sylow property in KS is a
separate consequence of the normalizing-cubic branch. -/
abbrev linearFieldSylow (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2

omit [Finite G] in
/-- The two factors of the source S both lie in T. -/
theorem linearFieldSylow_le (T : Sylow 2 G) (L : Subgroup G) :
    linearFieldSylow T L ≤ (T : Subgroup G) := by
  apply sup_le inf_le_left
  have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hh

omit [Finite G] in
private theorem residual_normal_in_linearSupplement
    (hTH : (T : Subgroup G) ≤ H) (hST : S ≤ (T : Subgroup G)) :
    ((residual H).subgroupOf (linearSupplement H S)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le (residual H).le_normalizer
      (hST.trans (hTH.trans (le_normalizer_residual H))))

private def residualInSupplementEquiv :
    pResidual 2 H ≃* (residual H).subgroupOf (linearSupplement H S) :=
  ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe (show residual H ≤ linearSupplement H S from le_sup_left)).symm

omit [Finite G] in
/-- The linear-three marking passes through the actual relative inclusion. -/
theorem linearSupplement_residual_quotient_isQuasisimple
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    IsQuasisimple (((residual H).subgroupOf (linearSupplement H S)) ⧸
      pCore 2 ((residual H).subgroupOf (linearSupplement H S))) := by
  obtain ⟨F, _, _, _, ⟨f⟩⟩ := hlinear
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv f.symm
  let e := residualInSupplementEquiv (H := H) (S := S)
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

/-- The outer two-group condition in E.5.4 holds in the literal KS quotient.
The subgroup S need only lie in T; no ambient normality of K is required. -/
theorem linearSupplement_core_quotient_structure
    (hTH : (T : Subgroup G) ≤ H) (hST : S ≤ (T : Subgroup G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    IsQuasisimple (generalizedFitting
      (linearSupplement H S ⧸ pCore 2 (linearSupplement H S))) ∧
    IsPGroup 2 ((linearSupplement H S ⧸ pCore 2 (linearSupplement H S)) ⧸
      generalizedFitting (linearSupplement H S ⧸ pCore 2 (linearSupplement H S))) := by
  let K := (residual H).subgroupOf (linearSupplement H S)
  let : K.Normal := residual_normal_in_linearSupplement hTH hST
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    linearSupplement_residual_quotient_isQuasisimple hlinear
  exact quasisimple_and_outer_two_group_of_two_supplement K
    (S.subgroupOf (linearSupplement H S)) ((T.isPGroup'.to_le hST).comap_subtype)
    (codisjoint_subgroupOf_sup (residual H) S).eq_top

/-- Adjoining the source S preserves the actual residual, not merely its
image modulo the two-core. -/
theorem linearSupplement_residual_eq
    (hTH : (T : Subgroup G) ≤ H) (hST : S ≤ (T : Subgroup G)) :
    pResidual 2 (linearSupplement H S) =
      (residual H).subgroupOf (linearSupplement H S) := by
  let K := (residual H).subgroupOf (linearSupplement H S)
  let : K.Normal := residual_normal_in_linearSupplement hTH hST
  let e := residualInSupplementEquiv (H := H) (S := S)
  exact pResidual_eq_of_isPPerfect_sup K (S.subgroupOf (linearSupplement H S))
    ((isPPerfect_pResidual 2).of_surjective e.toMonoidHom e.surjective)
    ((T.isPGroup'.to_le hST).comap_subtype)
    (codisjoint_subgroupOf_sup (residual H) S).eq_top

/-- The outer premise is discharged for the specific S used in 5.1.20,
before any faithful FF-module exclusion or Thompson normality argument. -/
theorem linearFieldSylow_core_quotient_structure
    {L : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    let J := linearSupplement H (linearFieldSylow T L)
    IsQuasisimple (generalizedFitting (J ⧸ pCore 2 J)) ∧
      IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ generalizedFitting (J ⧸ pCore 2 J)) :=
  linearSupplement_core_quotient_structure hTH (linearFieldSylow_le T L) hlinear

/-- E.5.4 applied to the source KS, with its outer premise discharged.
All centralizers and normality assertions are relative to KS. -/
theorem linearSupplement_higherThompsonCenter
    (hTH : (T : Subgroup G) ≤ H) (hST : S ≤ (T : Subgroup G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (P : Sylow 2 (linearSupplement H S))
    (hchar : generalizedFitting (linearSupplement H S) = pCore 2 (linearSupplement H S))
    (hrank : primeRank 2 (linearSupplement H S ⧸ pCore 2 (linearSupplement H S)) ≤ 4)
    (hno : ChapterE.NoFFAlternative.HasNoFFQuotients (linearSupplement H S))
    (hJ : ¬ (ChapterB.thompsonJ (P : Subgroup (linearSupplement H S)) 0).Normal) :
    (residual H).subgroupOf (linearSupplement H S) ≤
      centralizer (ChapterE.higherThompsonCenter
        (P : Subgroup (linearSupplement H S)) 4 : Set (linearSupplement H S)) ∧
    (ChapterE.higherThompsonCenter (P : Subgroup (linearSupplement H S)) 4).Normal := by
  obtain ⟨hq, ho⟩ := linearSupplement_core_quotient_structure hTH hST hlinear
  have hh := (ChapterE.NoFFAlternative.noFF_alternative_of_outer_two_group
    P 4 (by decide) hchar hq hrank hno ho).resolve_left hJ
  rwa [linearSupplement_residual_eq hTH hST] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
