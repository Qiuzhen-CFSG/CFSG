module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiBorel

/-!
# Excluding both original Suzuki component orbits

The invariant Borel argument makes the entire L₁-star centralize K₀-star.
The already proved natural-section and full-movement argument makes this
centralizer intersection trivial. Thus L₁-star would be trivial, contrary
to its surviving original Sylow E₉. This excludes the exchanged Suzuki
field-action case as well as the normal case.

The final application constructs the source's actual reduced actor
J = K₀L₁T and excludes the Suzuki marking on both K/O₂(K) and K-star.
The full original module and every retained earlier geometry premise are
unchanged. Other 12.6.31 rows, their subgroup/module identifications and
the universal NaturalReduction remain with the source assembly.

Source: Aschbacher--Smith 12.6.30--31, printed pp.835--836.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Suzuki Chapter13.Section08.Components.Suzuki.BorelSource
open Chapter15.Section03 Chapter15.Section03.Candidates.SuzukiExclusion
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
open BenderSuzuki.MatrixGroups
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
/-- Both Suzuki component orbits are impossible on the original actor. -/
theorem SourceHypothesis.original_abelian_suzuki_impossible
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) : False := by
  let E := D.fullSetup hZ T z
  have hc := S.original_abelian_suzuki_residual_centralizes D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hm eK
  have hzero : actorImage H E.L₁ = ⊥ := (inf_eq_left.mpr hc).symm.trans
    (S.original_abelian_suzuki_residual_centralizer_eq_bot D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hm eK)
  let A : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P := (A : Subgroup E.L₁).map E.L₁.subtype
  have hcard := (S.original_point_sylow_star D hZ z hz hTz hH A).2.1
  change Nat.card (actorImage H P) = 9 at hcard
  have hP : actorImage H P = ⊥ :=
    bot_unique ((map_mono (comap_mono (map_subtype_le _))).trans_eq hzero)
  have hone : Nat.card (actorImage H P) = 1 := by simp [hP]
  omega

include hz hTV hTz hbound hTI hns hH in
/-- Apply the Suzuki exclusion after the source's actual replacement
H by K₀L₁T, retaining the escaping component and both quotient carriers. -/
theorem SourceHypothesis.original_abelian_reduced_no_suzuki :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      ∀ m : ℕ, 0 < m →
        ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) ∧
        ¬ Nonempty ((actorImage J K) ≃* SuzukiMatrixGroup m) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  intro m hm
  constructor
  · rintro ⟨e⟩
    exact S.original_abelian_suzuki_impossible D hZ z hz hTV hTz hbound hTI hns hJ hKle hKJ rfl hm e
  · rintro ⟨e⟩
    exact S.original_abelian_suzuki_impossible D hZ z hz hTV hTz hbound hTI hns hJ hKle hKJ rfl hm
      ((componentStarEquiv _ K hKle hKJ).trans e)

end CFSG.Quasithin.Chapter12.Section06
