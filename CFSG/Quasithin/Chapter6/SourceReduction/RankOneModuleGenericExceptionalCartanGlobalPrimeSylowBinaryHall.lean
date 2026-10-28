module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryCover
public import Theory.SpecificGroups.Triality.BinaryLocalAutomorphisms
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalParabolicDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalProjectiveResidual
public import Theory.GroupTheory.CComponent.TwoCoreOverlapRank
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeComponentSource
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalProjectiveResidual
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSpecialLinearResidual
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticResidual

/-!
# Excluding binary triality by the original right Hall subgroup

At the smaller changed Sylow, a binary triality containing component K
is the two-residual of the whole smaller overgroup and also of the
normal prime-generated subgroup. Hence the full local extension,
including the original right Hall subgroup B, normalizes K.

The literal quotient action of B on K/O₂(K) preserves the proper
nonsolvable image of the selected right factor. The ambient quasithin
seven-rank bound and the binary triality seven-plane make the action
kernel seven-free. The model normalizer bound then gives seven-rank
at most one for B.

For each original PSL₃, SL₃ or Sp₄ residual row, the checked comparison
forces its field degree to be three. Its actual split torus supplies two
independent seven-directions in B, a contradiction. This excludes the
entire rank-two containing family on the actual changed-Sylow witness,
without identifying the original left degree with the residual degree.

When the selected right factor is an actual H-component, its movement
by T also supplies two independent seven-directions in the overlap:
pass to the ambient two-core quotient and use commuting conjugate
components. This excludes the binary endpoint in the component source
row as well, and strengthens the existing non-A₅ containing-component
witness with a full rank-two exclusion.

The internal imports reuse the literal residual-normalizer constructions
within the existing Cartan module family, preserving their private boundary.
Zero-core recognition, higher-field reduction, other containing families
and full conditional normalization remain with
qt-d-1222-rankone-cartan-local-to-global. The original h513 input is unchanged.
Source: Aschbacher–Smith 5.1.12–13 and 5.2.2, printed pp.635–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem residual_join_two_eq (J U : Subgroup G) (hU : IsPGroup 2 U)
    (hn : U ≤ normalizer (J : Set G)) : residual (J ⊔ U) = residual J := by
  let X := J ⊔ U
  let N := J.subgroupOf X
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le J.le_normalizer hn)
  have hh := pResidual_of_normal_pGroup_supplement 2 N (U.subgroupOf X)
    hU.comap_subtype (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
  have he := congrArg (map X.subtype) hh
  rw [map_map] at he
  let a := subgroupOfEquivOfLe (show J ≤ X from le_sup_left)
  have heq : X.subtype.comp N.subtype = J.subtype.comp a.toMonoidHom := by ext x; rfl
  rw [heq,←map_map,map_pResidual] at he
  exact he.symm

/-- The binary overcomponent is normalized by the whole local extension:
its two-residual is already that of the normal prime-generated subgroup. -/
theorem LocalData.binaryTriality_extension_normalizes
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) :
    extension T L H B D R ≤ normalizer (K : Set G) := by
  have he := (d.source_overcomponent_binaryTriality_cover h hH c hd hz hSyl hRK hKX hK hKn hm).2.1
  rw [residual_join_two_eq (generated L H D R) (normalizingSylow T R)
    (T.isPGroup'.to_le inf_le_left)
    ((le_sup_right.trans le_sup_left).trans d.extension_normalizes_generated)] at he
  rw [he]
  exact d.extension_normalizes_generated.trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (generated L H D R)))

/-- At the smaller Sylow, a binary triality containing component forces
seven-rank at most one for the actual original right Hall subgroup. -/
theorem LocalData.binaryTriality_right_seven_rank_le_one
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) :
    primeRank 7 B ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := generated L H D R ⊔ normalizingSylow T R
  let E := extension T L H B D R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let qK := QuotientGroup.mk' (pCore 2 K)
  let Rk := (R.subgroupOf K).map qK
  obtain ⟨_,_,_,_,e,he⟩ := d.source_overcomponent_binaryTriality_cover
    h hH c hd hz hSyl hRK hKX hK hKn hm
  have hRX : R ≤ X := hRK.le.trans hKX
  have hmap : (R.subgroupOf K).map (inclusion hKX) = R.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_map]
    change (R.subgroupOf K).map K.subtype = _
    rw [map_subgroupOf_eq_of_le hRK.le,map_subgroupOf_eq_of_le hRX]
  have hemap : Rk.map e.toMonoidHom = Rbar := by
    rw [map_map]
    have hh : e.toMonoidHom.comp qK = q.comp (inclusion hKX) := by
      ext x; exact he x
    rw [hh,←map_map,hmap]
  have hSylKeep := hSyl
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le (show normalizingSylow T R ≤ X from le_sup_right)]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf le_sup_right hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map q)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hns : ¬ Group.IsSolvable Rbar := by
    intro hs
    let := hs
    exact hlocalbar.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show Rbar ≤ Rbar ⊔ (P : Subgroup _) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  have hlt := d.right_image_lt h hH hSylKeep hRX hKX hRK hK
  have hne : Rk ≠ ⊤ := by
    intro hh
    have hh' : Rbar = ⊤ := by rw [←hemap,hh,map_top_of_surjective _ e.surjective]
    change Rbar < _ at hlt
    rw [hh'] at hlt
    exact (not_lt_of_ge le_top) hlt
  have hnsK : ¬ Group.IsSolvable Rk := by
    intro hs
    let := hs
    have hh := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective Rk)
    rw [hemap] at hh
    exact hns hh
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set _) := by
    change (S : Subgroup X).map q ≤ _
    rw [heS]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  let U := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have heback : Rbar.map e.symm.toMonoidHom = Rk := by
    rw [←hemap,map_map]
    have heid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact e.symm_apply_apply x
    rw [heid,map_id]
  have hnU : (U : Subgroup (K ⧸ pCore 2 K)) ≤ normalizer (Rk : Set _) := by
    rw [←heback]
    exact (map_mono hn).trans (le_normalizer_map e.symm.toMonoidHom)
  have hrE := (Chapter3.sqtk_of_mem_H h.qtke (d.extension_core_ne_bot hz)).stronglyQuasithin
    7 (by decide) (by decide)
  have hm' : Triality.Standard.IsTrialityGroupAt (2^1) (K ⧸ pCore 2 K) := by simpa using hm
  obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp hm'
  exact Triality.Standard.BinaryLocalAutomorphisms.core_action_seven_rank_le_one K R E B
    hRK.le (hKX.trans le_sup_left) le_sup_right
    (le_sup_right.trans (d.binaryTriality_extension_normalizes h hH c hd hz hSylKeep hRK hKX hK hKn hm))
    d.B_normalizes_right a hrE U hne hnsK hnU
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem units_seven_rank_pos {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 8) : 1 ≤ primeRank 7 Fˣ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hu : Nat.card Fˣ = 7 := by rw [Nat.card_units,hF]
  exact primeRank_ge_of_elementary_embedding
    (fun x : Fˣ => hu ▸ pow_card_eq_one' (x := x))
    (by simpa using hu) (MonoidHom.id Fˣ) Function.injective_id

/-- The actual right Hall subgroup has two independent seven-directions
when the original residual has a classical rank-two quotient over eight. -/
theorem CartanPair.right_seven_rank_ge_two_of_classical_residual
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 8 ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 8 ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) :
    2 ≤ primeRank 7 B := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hi : ¬ 7 ∣ (B.subgroupOf (normalizer (L : Set G) ⊓ H)).index := by
    intro hi
    exact c.right_hall.p_in_pi_of_p_dvd_index ⟨7,by decide⟩ hi (by change (7 : ℕ) ≠ 2; decide)
  have hBR : primeRank 7 B = primeRank 7 (normalizer (L : Set G) ⊓ H : Subgroup G) := by
    rw [←primeRank_equiv 7 (subgroupOfEquivOfLe c.right_le)]
    exact (B.subgroupOf (normalizer (L : Set G) ⊓ H)).primeRank_eq_of_not_dvd_index hi
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,hF,N,hNM,⟨e⟩⟩ := projective_residual_normalizer hH (f := 3) (by decide) hm
    have hr := primeRank_mono 7 hNM
    rw [←primeRank_equiv 7 (N.equivMapOfInjective (residual H).subtype
      (residual H).subtype_injective),←hBR] at hr
    have hl := primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 N) pCore_isPGroup
    rw [primeRank_equiv 7 e] at hl
    have hb := Matrix.PSL3.CartanActions.BorelQuotient.projective_torus_primeRank_ge_two
      (p := 7) F (by rw [hF]; decide) (Or.inl (by decide))
    omega
  · obtain ⟨F,_,_,hF,N,hNM,⟨e⟩⟩ := specialLinear_residual_normalizer hH (f := 3) (by decide) hm
    have hr := primeRank_mono 7 hNM
    rw [←primeRank_equiv 7 (N.equivMapOfInjective (residual H).subtype
      (residual H).subtype_injective),←hBR] at hr
    have hl := primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 N) pCore_isPGroup
    rw [primeRank_equiv 7 e,primeRank_prod_eq_add] at hl
    have hb := units_seven_rank_pos hF
    omega
  · obtain ⟨F,_,_,_,hF,⟨e⟩⟩ := right_torus_of_residual c hTL hH hgen (f := 3) (by decide) hm
    rw [primeRank_equiv 7 e,primeRank_prod_eq_add]
    have hb := units_seven_rank_pos hF
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Every classical rank-two residual row excludes every rank-two
containing component at the smaller changed Sylow, including binary triality. -/
theorem LocalData.classical_residual_not_rankTwo_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) := by
  intro hmodel
  have he := (d.source_rankTwo_container_residual_degree_three
    h hH c hd hz hSyl hRK hKX hK hKn hmodel hf hm).1
  have ht := (d.source_overcomponent_rankTwo_configuration
    h hH c hd hz hSyl hRK hKX hK hKn hmodel).1
  have hu := d.binaryTriality_right_seven_rank_le_one h hH c hd hz hSyl hRK hKX hK hKn ht
  subst f
  have hl := c.right_seven_rank_ge_two_of_classical_residual h.sylow_normalizes hH hgen hm
  omega

/-- The actual changed-Sylow witness in a classical residual row has no
rank-two containing component in its smaller-Sylow alternative. -/
theorem LocalData.changedSylow_classical_residual_excludes_rankTwo
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
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
          ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨P,hTP,hD,hcases⟩ := d.changedSylow_binary_cover h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,_⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,
      d.classical_residual_not_rankTwo_container h hH hgen c hd hz hSyl hRK hKX hK hKn hf hm⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A moved actual H-component with quotient PSL₂(8) gives two
seven-directions in the prescribed right Hall subgroup. -/
theorem LocalData.component_right_seven_rank_ge_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hm : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8) : 2 ≤ primeRank 7 B := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let M := normalizer (L : Set G) ⊓ H
  have hRH : R ≤ H := d.right_le_residual.trans (map_subtype_le _)
  let C := R.subgroupOf H
  let Mh := M.subgroupOf H
  let eC := subgroupOfEquivOfLe hRH
  let eqC := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  let eqF := eqC.trans e
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := eqF.isSimpleGroup
  have hcZ : center (C ⧸ pCore 2 C) = ⊥ := by
    apply map_injective (f := eqF.toMonoidHom) eqF.injective
    rw [center_map_equiv,Subgroup.map_bot,Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]
  let : Group.IsPerfect C := hC.perfect
  let : IsQuasisimple (C ⧸ pCore 2 C) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hcZ).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hcard : Nat.card (B ⊓ R : Subgroup G) = 7 := by
    exact d.right_cartan_card c (m := 3) ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
  have hrpos : 1 ≤ primeRank 7 (B ⊓ R : Subgroup G) := by
    by_contra hlow
    have he : primeRank 7 (B ⊓ R : Subgroup G) = 0 := by omega
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp he) (by rw [hcard])
  have hoverlap : 1 ≤ primeRank 7 (Mh ⊓ C : Subgroup H) := by
    change 1 ≤ primeRank 7 ((M ⊓ R).subgroupOf H)
    rw [primeRank_equiv 7 (subgroupOfEquivOfLe
      (show M ⊓ R ≤ H from inf_le_right.trans hRH))]
    exact hrpos.trans (primeRank_mono 7 (inf_le_inf c.right_le le_rfl))
  have hi : ¬ 7 ∣ (B.subgroupOf M).index := by
    intro hi
    exact c.right_hall.p_in_pi_of_p_dvd_index ⟨7,by decide⟩ hi (by change (7 : ℕ) ≠ 2; decide)
  have heB : primeRank 7 B = primeRank 7 Mh := by
    rw [primeRank_equiv 7 (subgroupOfEquivOfLe (show M ≤ H from inf_le_right)),
      ←primeRank_equiv 7 (subgroupOfEquivOfLe c.right_le)]
    exact (B.subgroupOf M).primeRank_eq_of_not_dvd_index hi
  by_contra hlow
  have hineq : primeRank 7 Mh < 2 * primeRank 7 (Mh ⊓ C : Subgroup H) := by omega
  have hn := hC.normalizes_of_overlap_primeRank (M := Mh) hcZ 7 (by decide) hineq
  have hTM : (T : Subgroup G) ≤ M := le_inf h.sylow_normalizes hH.1.1.2
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    intro t ht
    have hnt := hn (show (⟨t,hH.1.1.2 ht⟩ : H) ∈ Mh from hTM ht)
    rw [←subgroupOf_normalizer_eq hRH] at hnt
    exact hnt
  exact (d.normalizingSylow_lt hH.1.1.2 c hd hz).not_ge (le_inf le_rfl hTN)

/-- An actual H-component excludes the whole rank-two containing family
at the smaller Sylow; the binary endpoint contradicts its Hall rank. -/
theorem LocalData.component_source_not_rankTwo_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) := by
  intro hm
  obtain ⟨ht,hr,_⟩ := d.source_overcomponent_rankTwo_configuration
    h hH c hd hz hSyl hRK hKX hK hKn hm
  have hl := d.component_right_seven_rank_ge_two h hH c hd hz hC hr
  have hu := d.binaryTriality_right_seven_rank_le_one h hH c hd hz hSyl hRK hKX hK hKn ht
  omega

/-- The actual non-A₅ component source witness has no rank-two or odd
rank-one containing model, with the full-Sylow comparison discharged. -/
theorem LocalData.component_source_overcomponent_rankTwo_exclusion
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let q := QuotientGroup.mk' (pCore 2 X)
    ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
      (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
      ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) ∧
      (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  have hSyl := d.normalizingSylow_sylow_source_of_component h hH c hd hz hC hnot
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,hb,ht,_,ho,hj⟩ :=
    d.component_source_overcomponent_odd_exclusions h hH c hd hz hC hnot
  exact ⟨K,hRK,hKX,hK,hKn,hlt,hb,ht,
    d.component_source_not_rankTwo_container h hH c hd hz hC hSyl hRK hKX hK hKn,ho,hj⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
