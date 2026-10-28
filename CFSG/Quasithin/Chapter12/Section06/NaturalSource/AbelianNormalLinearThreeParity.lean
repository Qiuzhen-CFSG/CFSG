module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalCubic
public import Theory.SpecificGroups.PSL3.OddDegreeInnerSupplement
/-!
# Even degree for the original normal projective linear-three component

In odd degree the genuine PSL₃ outer group is abelian. The original
identity L₁=[L₁,T intersect L] therefore makes its star action inner.
The original Sylow E₉ and intrinsic quotient L₁-star/O₂(L₁-star) are
retained under H → H/O₂(H). The normal centralizer and ambient
three-rank bound let the intrinsic inner-supplement obstruction apply.
It contradicts the three-prime Borel through the actual Sylow intersection.
Thus the original projective linear-three parameter is even.

Relative normality in H and the full O₂(H) kernel are preserved. The
result uses only the displayed original point and invariance hypotheses;
no Borel marking or inner-action premise is added to the source input.
AbelianEvenLinearSieve applies it to the original reduced-actor catalogue.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
The remaining signed degree-three restrictions, module exclusions and
universal NaturalReduction remain with the source assembly.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


include hz hTV hTz hH hKH hK hgen in
/-- Odd-degree projective linear three cannot be the original normal component. -/
theorem SourceHypothesis.original_abelian_normal_linearThree_not_odd
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (ho : Odd n) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^n)) : False := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let q := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let Q := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hTA : (Q : Subgroup (H ⧸ pCore 2 H)) ≤ normalizer (A : Set (H ⧸ pCore 2 H)) := by
    have ht : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
      (le_inf hTH hTV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
    rintro _ ⟨x,hx,rfl⟩
    apply (E.L₁.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq hLH]
    exact ht hx
  have hstar : B ⊔ A ⊔ (Q : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    have hg := hgen
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hg
    change actorImage H K ⊔ actorImage H E.L₁ ⊔ actorImage H T = ⊤
    unfold actorImage
    rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hKH hLH,
      ←subgroupOf_sup (sup_le hKH hLH) hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨_,_,_,d,_⟩ := S.original_point_star_core_quotient D hZ z hz hTz hH
  let : IsElementaryAbelian 3 (A ⧸ pCore 2 A) :=
    IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  have hnC : (A ⊓ centralizer (B : Set (H ⧸ pCore 2 H)) : Subgroup (H ⧸ pCore 2 H)).Normal := by
    have hh := S.original_abelian_residual_centralizer_normal D hZ z hz hTV hH hKH hK hgen
    rwa [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hh
  let _ := hnC
  let R : Sylow 3 E.L₁ := Classical.choice inferInstance
  let R₀ := (R : Subgroup E.L₁).map E.L₁.subtype
  let P := actorImage H R₀
  obtain ⟨hP,hc,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH R
  let : IsElementaryAbelian 3 P := hP
  have hmstar := hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  let : IsMulCommutative (MulAut.Outer B) :=
    Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.OuterAutomorphisms.linearThree_outer_isMulCommutative
      (by omega : 1 < n) ho hmstar
  have hi := S.original_point_residual_inner_of_outer_abelian D hZ z hz hTz hH hn
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hmstar
  let := hF
  let := hfin
  exact Matrix.PSL3.BinaryCubicRankParity.no_inner_elementary_plane_supplement
    Q A B P e hn2 ho hcard (pCore_quotient_pCore_eq_bot 2)
    (S.original_star_three_rank D hZ z hz hH) hi hTA hstar
    (map_mono (comap_mono (map_subtype_le _))) hc

include hz hTV hTz hH hKH hK hgen in
/-- The field exponent of the original normal PSL₃ row is even. -/
theorem SourceHypothesis.original_abelian_normal_linearThree_even
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^n)) : Even n := by
  exact Nat.not_odd_iff_even.mp (fun ho =>
    S.original_abelian_normal_linearThree_not_odd D hZ z hz hTV hTz hH hKH hK hgen hn hn2 ho hm)
end CFSG.Quasithin.Chapter12.Section06
