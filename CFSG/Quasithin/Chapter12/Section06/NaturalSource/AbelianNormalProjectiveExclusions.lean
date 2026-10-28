module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalLargeUnitary
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective.QuadraticActor
/-!
# Excluding the original exceptional projective components

The original edge-core actor acts faithfully and quadratically on the literal
U_H/V₁ and has displacement ratio at most two. Normality of K identifies
its Sylow orbit with K, so the same actor is faithful on K-star. The native
PSU₃(8) quadratic obstruction now applies with no new source assumptions.
The intrinsic component quotient equivalence preserves the full O₂ kernels.
Together with the existing parameter restriction, this removes every normal
projective-unitary row in the original reduced-component catalogue. The
same actual section also supplies the native PSL₃(4) quadratic obstruction.

Source: Aschbacher--Smith 12.6.30--31, printed pp.835--837, using the
quadratic-section recognition of B.4.5 and K.3.3, pp.87 and 456.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The same original faithful quadratic section excludes PSU₃(8) in K-star. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEight_star_excluded
    (hn : (K.subgroupOf H).Normal) :
    ¬ ClassicalGroup.IsPSU (actorImage H K) 3 8 := by
  intro hm
  obtain ⟨_,hU,a,B,_,_,hE,hquad,hcodim,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  let _ := hU
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  rw [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn] at hfaith
  exact Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective.no_quadratic_actor
    a.representation (actorImage H K) (B.map (QuotientGroup.mk' (pCore 2 H)))
    (S.original_star_sqtk D hZ z hz hH) hm a.faithful hE hquad hcodim hfaith

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The literal intrinsic two-core quotient cannot be PSU₃(8). -/
theorem SourceHypothesis.original_abelian_normal_unitaryEight_excluded
    (hn : (K.subgroupOf H).Normal) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 8 := by
  intro hm
  exact S.original_abelian_normal_unitaryEight_star_excluded D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn (hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- No normal projective-unitary row survives in the original reduced actor. -/
theorem SourceHypothesis.original_abelian_normal_unitaryThree_excluded
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2^n) := by
  intro hm
  have hn3 := S.original_abelian_normal_unitaryThree_degree_eq_three D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hgen hn hout hn2 hm
  subst n
  exact S.original_abelian_normal_unitaryEight_excluded D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn hm

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The same original faithful quadratic section excludes PSL₃(4) in K-star. -/
theorem SourceHypothesis.original_abelian_normal_linearThreeFour_star_excluded
    (hn : (K.subgroupOf H).Normal) :
    ¬ ClassicalGroup.IsPSL (actorImage H K) 3 4 := by
  intro hm
  obtain ⟨_,hU,a,B,_,_,hE,hquad,hcodim,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  let _ := hU
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  rw [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn] at hfaith
  exact Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective.no_quadratic_actor
    a.representation (actorImage H K) (B.map (QuotientGroup.mk' (pCore 2 H)))
    (S.original_star_sqtk D hZ z hz hH) hm a.faithful hE hquad hcodim hfaith

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The literal intrinsic two-core quotient cannot be PSL₃(4). -/
theorem SourceHypothesis.original_abelian_normal_linearThreeFour_excluded
    (hn : (K.subgroupOf H).Normal) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
  intro hm
  exact S.original_abelian_normal_linearThreeFour_star_excluded D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn (hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm)

end CFSG.Quasithin.Chapter12.Section06
