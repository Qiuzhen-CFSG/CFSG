module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentProjection
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Overlap

/-!
# The marked two-core of the ordinary-component projection

The perfect coordinate projection is invariant under the component stabilizer
in the actual overlap M intersect N_G(B). The overlap saturation theorem puts
its noncentral two-core in the literal two-core of that overlap. This supplies
both the local subgroup and its marked two-core needed by the remaining
ordinary-model inspection, retaining the original nonnormal A5 pair.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal projection carries the overlap stabilizer and actual two-core marking. -/
theorem source_a5_oddNormalizer_component_projection_saturated
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G))
    let Y := D.maximalLocal.subgroupOf (normalizer (B : Set G))
    ∃ P Q : Subgroup (normalizer (B : Set G)), P ≤ K ∧
      Q ≤ centralizer (K : Set (normalizer (B : Set G))) ∧
      Group.IsPerfect P ∧ Group.IsPerfect Q ∧ F ≤ P ⊔ Q ∧ P ≤ F ⊔ Q ∧
      ⁅P.pCoreIn 2,P⁆ ≠ ⊥ ∧ P.pCoreIn 2 ≤ Y.pCoreIn 2 ∧
      Y ⊓ normalizer (K : Set (normalizer (B : Set G))) ≤
        normalizer (P : Set (normalizer (B : Set G))) := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let U := D.fullModule.subgroupOf N
  let Y := D.maximalLocal.subgroupOf N
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,hm,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hUF : U ≤ F.subgroupOf N := subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))
  have hmove : U = ⁅U,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hFN]
    exact hm
  have hnc : ¬ U ≤ centralizer (K : Set N) := by
    intro hc
    apply houtK
    rw [←source_fullModule_normalizer D]
    apply (show K.map N.subtype ≤ centralizer (D.fullModule : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨k,hk,rfl⟩ v hv
    exact congrArg Subtype.val (hc (show (⟨v,hVN hv⟩ : N) ∈ U from hv) k hk).symm
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  have hUp : IsPGroup 2 U := (isPGroup_pCoreIn 2 F).to_le hVF |>.comap_subtype
  obtain ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc,hstab⟩ :=
    exists_perfect_projection_with_noncentral_core K (centralizer (K : Set N))
      (F.subgroupOf N) U (le_centralizer_iff.mp le_rfl) hinner hUF hUp hmove hnc
  have hYF : Y ≤ normalizer (F.subgroupOf N : Set N) := by
    have hnorm : D.maximalLocal ⊓ N ≤ normalizer (F : Set G) :=
      ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    intro y hy f
    exact hnorm ⟨hy,y.property⟩ (f : G)
  have hYP : Y ⊓ normalizer (K : Set N) ≤ normalizer (P : Set N) :=
    hstab _ inf_le_right (inf_le_right.trans (normalizer_le_normalizer_centralizer K))
      (inf_le_left.trans hYF)
  have hcore : P.pCoreIn 2 ≤ Y.pCoreIn 2 :=
    source_a5_oddNormalizer_component_core_saturation D e hn hp B hB hBC hBV hperm K hK
      (P.pCoreIn 2) ((pCoreIn_le 2 P).trans hPK) (isPGroup_pCoreIn 2 P)
      (hYP.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  exact ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc,hcore,hYP⟩

end CFSG.Quasithin.Chapter10
