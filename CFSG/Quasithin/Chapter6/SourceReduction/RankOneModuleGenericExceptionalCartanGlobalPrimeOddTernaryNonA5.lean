module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeNoncentralSection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOddTernaryRecognition

/-!
# Removing all odd ternary smaller-Sylow containers

Restrict the actual quotient Sylow to the ordinary containing component.
The preceding recognition applies to the literal right image, whose simple
two-core quotient is already proved for both actual components and selected
parabolics. Hence every odd ternary row forces an A₅ right quotient, contrary
to the completed smaller-Sylow A₅ exclusion. This also removes both cubic covers.

The same source pair now retains only a J₄ containing image in the
smaller-Sylow branch, and the existing faithful-actor argument forces p = 3.
Relative normality, strict quotient embedding, original Hall data and all
larger-Sylow and zero-core alternatives are retained. Full Cartan normalization
still requires those remaining branches and the higher-field reductions.

Source: Aschbacher–Smith 5.1.12–13 and 5.2.2, pp.635–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Odd ternary containing images force the same selected right quotient to be PSL₂(4). -/
theorem LocalData.source_overcomponent_odd_ternary_right_four
    {T : Sylow 2 G} {L W H A B D R X K : Subgroup G} {n p q : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (_hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hq : q.Prime) (ho : Odd q)
    (hm : let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      ClassicalGroup.IsPSL I 3 q ∨ ClassicalGroup.IsPSU I 3 q ∨
      Chapter1.Section02.LocalModels.IsSL I 3 q ∨ Chapter1.Section02.LocalModels.IsSU I 3 q) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map π
  let Kbar := (K.subgroupOf X).map π
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map π)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map π ≤ _
    rw [heS]
    apply (map_mono (f := π) ?_).trans (le_normalizer_map π)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hRKbar : Rbar ≤ Kbar := map_mono (comap_mono hRK)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlocalbar hRKbar (hK.map_quotient (pCore 2 X)).subnormal
  let U := Rbar.subgroupOf Kbar
  have hnU : (Q : Subgroup Kbar) ≤ normalizer (U : Set Kbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hRKbar]
    exact comap_mono hn
  let r := π.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (π.subgroupMap_surjective _) hr
  let b := (subgroupOfEquivOfLe hRKbar).symm
  let e₃ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let eR : (R ⧸ pCore 2 R) ≃* (U ⧸ pCore 2 U) := e₁.trans (e₂.trans e₃)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := d.selected_right_simple h hH c hd hz hs
  let : IsSimpleGroup (U ⧸ pCore 2 U) := eR.symm.isSimpleGroup
  let : Group.IsPerfect U := by
    let := hU.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show U ≤ U ⊔ (Q : Subgroup Kbar) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  exact (OddTernary.right_quotient_four Q U hnU (d.right_quotient.of_equiv eR.symm)
    hq ho hm).of_mulEquiv eR

open Chapter1.Section02 LocalModels

/-- The non-A₅ selected right factor excludes every odd ternary containing
row, including the original special linear and unitary cubic covers. -/
theorem LocalData.remaining_source_container_janko
    {T : Sylow 2 G} {L W H A B D R X K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingQuasisimpleSourceContainer X K) :
    let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    A36Common I ∧ IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧
      Nonempty (I ≃* Janko4.Model) := by
  obtain ⟨hcommon,hcomponent,hcases⟩ := hm
  refine ⟨hcommon,hcomponent,?_⟩
  rcases hcases with ⟨hI,hj | ⟨q,hq,ho,u,hm⟩⟩ | ⟨_,q,hq,ho,u,hm⟩
  · exact ⟨hI,hj⟩
  · apply (hnot (d.source_overcomponent_odd_ternary_right_four h hH c hd hz hs
      hSyl hRX hKX hRK hK hq ho ?_)).elim
    cases u
    · exact .inl hm
    · exact .inr (.inl hm)
  · apply (hnot (d.source_overcomponent_odd_ternary_right_four h hH c hd hz hs
      hSyl hRX hKX hRK hK hq ho ?_)).elim
    cases u
    · exact .inr (.inr (.inl hm))
    · exact .inr (.inr (.inr hm))

/-- The original smaller-Sylow branch retains only J₄ and a cubic actor,
with the same selected pair and all other source alternatives preserved. -/
theorem source_prime_pair_janko_containing_remainder
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
              (let I := (K.subgroupOf X).map q;
                A36Common I ∧ IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧
                  Nonempty (I ≃* Janko4.Model)) ∧ p = 3 ∧
              ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_quasisimple_containing_remainder h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm,hn⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    obtain ⟨hcommon,hcomponent,hsimple,⟨ej⟩⟩ := d.remaining_source_container_janko h hH c hd hz hs
      hSyl (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK.le hK hn hm
    let X := generated L H D R ⊔ normalizingSylow T R
    let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
    let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
    let eK : I ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
    have hp := d.source_overcomponent_janko_four_prime h hH c hd hz hSyl hRK.le hKX hK hKn
      ⟨eK.symm.trans ej⟩
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,⟨hcommon,hcomponent,hsimple,⟨ej⟩⟩,hp,hn⟩
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
