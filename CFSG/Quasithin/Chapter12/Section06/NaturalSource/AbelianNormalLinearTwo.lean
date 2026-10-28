module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidualCommutator
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiCentralizer
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalMovement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.GroupGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.OuterAutomorphisms.Linear
public import Theory.GroupTheory.RankOneInnerCentralizer
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
/-!
# Inner point action and its centralizing factor in the normal PSL₂ branch

The original identity L₁=[L₁,T ∩ L] forces the action of L₁-star on a
normal component with abelian outer group to be inner. Binary PSL₂ has
cyclic outer group by the proved semilinear coverage, so this applies
without an outer-action premise. Its three-rank is one, while the
original Sylow E₉ survives the full O₂(H) kernel. Consequently
C=L₁-star ∩ C_H-star(K-star) is nontrivial.

On the actual reduced actor H=K₀L₁T, normality of K gives K₀=K.
The previously proved relative centralizer normality and F.9 seed
irreducibility then give [U_H/V₁,C]=U_H/V₁. The consumer constructs the
literal quotient action and retains the original point, module, Sylow,
intersection bound, TI and nonsingular-centralizer hypotheses.

No centralizer order, field parity or field-order-four conclusion is
asserted. Those restrictions, the remaining normal Lie rows and the
universal NaturalReduction remain for the final source assembly.
Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
variable {G : Type*} [Group G] [Finite G]
  {catalog : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis catalog T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : (K.subgroupOf H).Normal)

include hz hTz hH hn in
/-- The original full commutator identity kills the actual outer action. -/
theorem SourceHypothesis.original_point_residual_inner_of_outer_abelian
    [IsMulCommutative (MulAut.Outer (actorImage H K))] :
    actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K ⊔
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  apply supplement_le_component_centralizer _ _ (actorImage H ((T : Subgroup G) ⊓ L))
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : (D.fullSetup hZ T z).L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  unfold actorImage
  rw [←map_commutator,←SubgroupTransport.subgroupOf_commutator _ _ hLH (inf_le_left.trans hTH),
    S.original_point_residual_full_commutator D hZ z hz hTz]

include hz hTz hH hn in
/-- Semilinear coverage discharges outer commutativity for the original normal PSL₂ component. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_inner
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {n : ℕ} (hn2 : 2 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K ⊔
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
  have hmstar := hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  let : IsMulCommutative (MulAut.Outer (actorImage H K)) :=
    OuterAutomorphisms.linearTwo_outer_isMulCommutative (by omega : 1 < n) hmstar
  exact S.original_point_residual_inner_of_outer_abelian D hZ z hz hTz hH hn

include hz hTz hH hn in
/-- The surviving original Sylow E₉ has a nontrivial centralizer on the normal PSL₂ component. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_centralizer_ne_bot
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {n : ℕ} (hn2 : 2 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    actorImage H (D.fullSetup hZ T z).L₁ ⊓
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ≠ ⊥ := by
  let E := D.fullSetup hZ T z
  let A : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P := (A : Subgroup E.L₁).map E.L₁.subtype
  obtain ⟨hP,hcard,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH A
  change IsElementaryAbelian 3 (actorImage H P) at hP
  change Nat.card (actorImage H P) = 9 at hcard
  let _ := hP
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  have hinner := S.original_abelian_normal_linearTwo_inner D hZ z hz hTz hH hn hKH hK hn2 hm
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let e : actorImage H K ≃* SL(2,F) :=
    (componentStarEquiv H K hKH hK).symm.trans
      (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  have hzK : center (actorImage H K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hc : center SL(2,F) = ⊥ := BenderSuzuki.Converse.center_SL2_eq_bot
    have he : e x = 1 := mem_bot.mp (hc.le ((centerCongr e) ⟨x,hx⟩).property)
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  have hr : primeRank 3 (actorImage H K) ≤ 1 := by
    rw [primeRank_equiv 3 e]
    exact (Matrix.SL2.binary_threeRank_eq_one (F := F)).le
  have hPD : actorImage H P ≤ actorImage H E.L₁ := map_mono (comap_mono (map_subtype_le _))
  have hne := elementary_plane_inner_centralizer_ne_bot (actorImage H P) (actorImage H K)
    hcard hzK hr (hPD.trans hinner)
  intro he
  exact hne (bot_unique ((inf_le_inf_right _ hPD).trans he.le))
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
open Representation Representation.BinaryOffender
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
/-- The same centralizer is normal and moves the entire original section U_H/V₁. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_moving_centralizer
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    let C := actorImage H (D.fullSetup hZ T z).L₁ ⊓
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
    C.Normal ∧ C ≠ ⊥ ∧
      ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H),
        let _ := hU
        ∃ a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁,
          subspaceCommutator a.representation ⊤ C = ⊤ := by
  let C := actorImage H (D.fullSetup hZ T z).L₁ ⊓
    centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hnormal : C.Normal := by
    have hh := S.original_abelian_residual_centralizer_normal D hZ z hz hTV hH hKH hK hgen
    rwa [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn] at hh
  let _ := hnormal
  have hne : C ≠ ⊥ := S.original_abelian_normal_linearTwo_centralizer_ne_bot
    D hZ z hz hTz hH hn hKH hK hn2 hm
  obtain ⟨hU,a,_⟩ := S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  exact ⟨hnormal,hne,hU,a,
    S.original_normal_local_actor_full_movement D hZ z hz hTV hTz hbound hH a C hne
      (inf_le_left.trans (map_mono (comap_mono le_sup_left)))⟩
end CFSG.Quasithin.Chapter12.Section06
