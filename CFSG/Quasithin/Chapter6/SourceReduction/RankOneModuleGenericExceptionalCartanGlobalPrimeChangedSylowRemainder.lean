module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeContainingRemainder
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeComponentSource

/-!
# Original components and parabolics at the larger changed Sylow

If the selected right factor is an actual component of H and has non-A₅
quotient, source 1.2.8 gives maximality in the original full-Sylow family.
The proved changed-Sylow argument would then identify the ambient Sylow
with T₀, contradicting its index two in T. Thus the original-component
branch has A₅ quotient and the Hall calculation gives p=5 and n≠2.

The parabolic branch retains its own field and the original residual model.
The same selected pair also carries the remaining smaller-Sylow catalogue.
The exceptional A₅ and parabolic contradictions, compatible zero-core
recognition and higher-field normalization still require their source proofs.
Source: Aschbacher–Smith 1.2.8(3), p.507, and 5.2.2, pp.648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- In the larger-Sylow case an original component is an A₅ quotient with
its original quintic actor; otherwise retain the precise parabolic field. -/
@[expose] def RemainingLargerSource (H R : Subgroup G) (p n : ℕ) : Prop :=
  ((R.subgroupOf H).IsCComponent ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
    p = 5 ∧ n ≠ 2) ∨
  (¬ (R.subgroupOf H).IsCComponent ∧
    ∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
       IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
       ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)))

/-- Maximality applies only to an actual H-component: if a changed Sylow
is ambient, that same component has the exceptional A₅ quotient. -/
theorem LocalData.largerChangedSylow_component_four
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (U : Sylow 2 G)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
  by_contra hn
  have he := d.changedSylow_eq_of_nonA5 h hH c hd hz
    (d.right_mem_original_local_family hH.1.1 hC) hn P hTP
  have hUT : (U : Subgroup G) ≤ (T : Subgroup G) :=
    (hU.trans he).le.trans inf_le_left
  have hTU := U.is_maximal' T.isPGroup' hUT
  have hT0 : normalizingSylow T R = (T : Subgroup G) :=
    (hU.trans he).symm.trans hTU.symm
  have hi := d.normalizingSylow_index hH.1.1.2 c hd hz
  rw [hT0,relIndex_self] at hi
  omega

/-- The source pair now carries exactly the unresolved smaller containing
cases and the original-component/parabolic distinction at a larger Sylow. -/
theorem source_prime_pair_changedSylow_remainder
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              RemainingSourceContainer X K) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n)))) := by
  classical
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_containing_remainder h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with hsmall | ⟨U,hU⟩
  · exact .inl hsmall
  refine .inr ⟨U,hU,lt_of_le_of_ne hTP ?_,?_⟩
  · intro he
    have hUT : (U : Subgroup G) ≤ (T : Subgroup G) :=
      (hU.trans he.symm).le.trans inf_le_left
    have hTU := U.is_maximal' T.isPGroup' hUT
    have hT0 : normalizingSylow T R = (T : Subgroup G) :=
      (hU.trans he.symm).symm.trans hTU.symm
    rw [hT0,relIndex_self] at hi
    omega
  · by_cases hC : (R.subgroupOf H).IsCComponent
    · have hfour := d.largerChangedSylow_component_four h hH c hd hz hC P hTP U hU
      exact .inl ⟨hC,hfour,hA5 hfour⟩
    · exact .inr ⟨hC,hs.resolve_left hC⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
