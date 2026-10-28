module
public import Theory.GroupTheory.NormalQuotientActionKernel
public import Theory.GroupTheory.Hall.BorelComplementNormalizer
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.HallSource
public import Theory.GroupTheory.RelativeComplementProjection
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The original torus-normalizer actor on the natural quotient

The original Hall torus chooses A=N_S(B). Restricting the Sylow complement
gives S=RA and H=LA with the literal intersections trivial. The action
kernel on L/O₂(L) is a normal two-subgroup of H, hence lies in Q and misses A.
The original torus and Sylow intersection descend to the actual Borel pair,
and A preserves both. These are precisely the inputs for simultaneous
field-automorphism alignment; no model or action marking is assumed.

Source: Aschbacher–Smith, 2.4.12(1), printed p.532.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_torus_normalizer_complements_of_choice
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (B : Subgroup G)
    (hcomp : IsComplement'
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf (T : Subgroup G))
      ((normalizer (B : Set G)).subgroupOf (T : Subgroup G))) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let F := S ⊓ normalizer (B : Set G)
    R ⊔ F = S ∧ L ⊔ F = d.H ∧ Disjoint R F ∧ Disjoint L F ∧
      IsComplement' (R.subgroupOf S) (F.subgroupOf S) ∧
      IsComplement' (L.subgroupOf d.H) (F.subgroupOf d.H) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let F := S ⊓ normalizer (B : Set G)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hRL : R=S⊓L := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1
  have hLH : L ≤ d.H := map_subtype_le _
  have hSH : S ≤ d.H := map_subtype_le _
  have hFS : F ≤ S := inf_le_left
  have hd : Disjoint R F := by
    apply disjoint_def.mpr
    intro g hgR hgF
    have he := disjoint_def.mp hcomp.disjoint
      (show (⟨g,hST.le (hRS hgR)⟩ : T) ∈ R.subgroupOf (T : Subgroup G) from hgR)
      (show (⟨g,hST.le (hRS hgR)⟩ : T) ∈ (normalizer (B:Set G)).subgroupOf (T : Subgroup G) from hgF.2)
    exact congrArg Subtype.val he
  have hg : R ⊔ F = S := by
    apply le_antisymm (sup_le hRS hFS)
    intro s hs
    obtain ⟨⟨r,f⟩,he⟩ := hcomp.2 (⟨s,hST.le hs⟩ : T)
    have heG := congrArg Subtype.val he
    change ((r:T):G)*((f:T):G)=s at heG
    have hfS : ((f:T):G) ∈ S := by
      have hh : ((f:T):G)=((r:T):G)⁻¹*s := by rw [←heG,inv_mul_cancel_left]
      rw [hh]
      exact S.mul_mem (S.inv_mem (hRS r.property)) hs
    exact heG ▸ (R⊔F).mul_mem (mem_sup_left r.property) (mem_sup_right ⟨hfS,f.property⟩)
  have hdL : Disjoint L F := by
    apply disjoint_def.mpr
    intro g hgL hgF
    exact disjoint_def.mp hd (hRL.symm ▸ (show g∈S⊓L from ⟨hgF.1,hgL⟩)) hgF
  have hgL : L ⊔ F = d.H := by
    have hh : L ⊔ S = d.H := by simpa only [hsingle] using d.ambient_L0_sup_sylow
    calc
      L ⊔ F = L ⊔ (R ⊔ F) := by rw [←sup_assoc,sup_eq_left.mpr (hRL.le.trans inf_le_right)]
      _ = L ⊔ S := congrArg (fun W : Subgroup G => L ⊔ W) hg
      _ = d.H := hh
  let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHL : d.H ≤ normalizer (L:Set G) := by
    have hh := d.block.le_normalizer_map d.H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  let : (L.subgroupOf d.H).Normal := normal_subgroupOf_of_le_normalizer hHL
  exact ⟨hg,hgL,hd,hdL,(relative_isComplement hRS hFS hg hd).symm,
    (relative_isComplement hLH (hFS.trans hSH) hgL hdL).symm⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_block_quotient_action_kernel
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block) {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock d.block n) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    (normalQuotientAction d.block (pCore 2 d.block)).ker ≤ pCore 2 d.H := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let K := d.block ⧸ pCore 2 d.block
  have hq : IsPGroup 2 (d.H ⧸ d.block) := by
    have he : d.block=pResidual 2 d.H := hsingle.symm.trans d.L0_eq_residual
    exact (isPGroup_quotient_pResidual (G := d.H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq he.symm)
  obtain ⟨_,_,F,_,_,hF,_,_,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hc : center K=⊥ := by
    apply eq_bot_iff.mpr
    intro k hk
    have hh := (centerCongr m.quotientIso ⟨k,hk⟩).property
    change m.quotientIso k ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hh
    exact mem_bot.mpr (m.quotientIso.injective (hh.trans m.quotientIso.map_one.symm))
  have hp : IsPGroup 2 (QuotientGroup.mk' (pCore 2 d.block)).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact le_sSup ⟨inferInstance,
    Theory.GroupTheory.kernel_isPGroup_of_normal_inner_quotient d.block hq
      (QuotientGroup.mk' (pCore 2 d.block)) hp hc
      (normalQuotientAction d.block (pCore 2 d.block))
      (normalQuotientAction_inner d.block (pCore 2 d.block))⟩

theorem source_torus_normalizer_quotient_action_faithful
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (B : Subgroup G)
    (hcomp : IsComplement'
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf (T : Subgroup G))
      ((normalizer (B : Set G)).subgroupOf (T : Subgroup G))) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    let F := (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)
    Function.Injective ((normalQuotientAction d.block (pCore 2 d.block)).comp
      (inclusion (show F ≤ d.H from inf_le_left.trans (map_subtype_le _)))) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let F := S ⊓ normalizer (B : Set G)
  let f := (normalQuotientAction d.block (pCore 2 d.block)).comp
    (inclusion (show F ≤ d.H from inf_le_left.trans (map_subtype_le _)))
  change Function.Injective f
  apply f.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro a ha
  have haQ : (a:G) ∈ twoCore d.H := mem_map_of_mem d.H.subtype
    (source_block_quotient_action_kernel d hsingle hL ha)
  have hQR : twoCore d.H ≤ R := by
    change twoCore d.H ≤ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    rw [(source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1]
    exact le_inf (pCoreIn_le_sylow d.H d.S)
      ((source_core_absorption d hG T hST hsingle hL hM hTM hunique).2 ▸ map_subtype_le _)
  have hd := (source_torus_normalizer_complements_of_choice d hG T hST hsingle hL hM hTM hunique B hcomp).2.2.1
  exact Subtype.ext (disjoint_def.mp hd (hQR haQ) a.property)
end CFSG.Quasithin.Chapter2.LinearShadows.Single

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_actor_borel_of_choice
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (D B : Subgroup G) (hDM : D ≤ M ⊓ d.block.map d.H.subtype)
    (hDB : D ≤ B) (hB : Odd (Nat.card B)) (hDc : Nat.card D=2^n-1)
    (hSn : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊔ D : Subgroup G) : Set G)) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    let A := (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)
    let ρ := (normalQuotientAction d.block (pCore 2 d.block)).comp
      (inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _)))
    let K := d.block ⧸ pCore 2 d.block
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F=2^n ∧
      ∃ (_e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
        (P : Sylow 2 K) (D₀ : Subgroup K),
        (P : Subgroup K) = ((d.S : Subgroup d.H).subgroupOf d.block).map
          (QuotientGroup.mk' (pCore 2 d.block)) ∧
        D₀ = (D.comap (d.H.subtype.comp d.block.subtype)).map
          (QuotientGroup.mk' (pCore 2 d.block)) ∧
        D₀ ≤ normalizer (P : Set K) ∧ Disjoint (P : Subgroup K) D₀ ∧
        (P : Subgroup K) ⊔ D₀ = normalizer (P : Set K) ∧
        ∀ a : A, (P : Subgroup K).map (ρ a).toMonoidHom = P ∧
          D₀.map (ρ a).toMonoidHom=D₀ := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L := d.block.map d.H.subtype
  let A := S ⊓ normalizer (B : Set G)
  let iL := d.H.subtype.comp d.block.subtype
  have hiL : Function.Injective iL := d.H.subtype_injective.comp d.block.subtype_injective
  have hiRange : iL.range=L := by
    dsimp only [iL]
    rw [MonoidHom.range_comp,range_subtype]
  let D' := D.comap iL
  have hDmap : D'.map iL = D := by
    rw [map_comap_eq,hiRange,inf_eq_right.mpr (hDM.trans inf_le_right)]
  have hDodd : Odd (Nat.card D') := by
    rw [←card_map_of_injective hiL,hDmap]
    exact hB.of_dvd_nat (card_dvd_of_le hDB)
  obtain ⟨P,hP,hN⟩ := source_intersection_borel d hsingle hL
  have hPR : (P : Subgroup d.block).map iL=R := by
    change ((P : Subgroup d.block).map (d.H.subtype.comp d.block.subtype))=R
    rw [←map_map,hP,map_inf _ _ _ d.H.subtype_injective]
    exact (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1.symm
  have hDP : D' ≤ normalizer (P : Set d.block) := by
    rw [hN]
    intro a ha
    exact (hDM ha).1
  have hDR : D ≤ normalizer (R : Set G) := by
    rw [←hDmap,←hPR]
    exact (map_mono hDP).trans ((P : Subgroup d.block).le_normalizer_map iL)
  have hAD : A ≤ normalizer (D : Set G) := torusNormalizer_preserves_borel_complement S R D B
    (T.isPGroup'.to_le ((sSup_le fun _ h => h.1).trans hST.le)) hB hDB hDR hSn
  have hAR : A ≤ normalizer (R : Set G) := inf_le_left.trans
    (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  let α := (MulAut.conjNormal : d.H →* MulAut d.block).comp
    (inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _)))
  let q := QuotientGroup.mk' (pCore 2 d.block)
  let K := d.block ⧸ pCore 2 d.block
  let ρ : A →* MulAut K := (normalQuotientAction d.block (pCore 2 d.block)).comp
    (inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _)))
  have hα (a : A) : iL.comp (α a).toMonoidHom = (MulAut.conj (a:G)).toMonoidHom.comp iL := by
    ext l
    rfl
  have hαP (a : A) : (P : Subgroup d.block).map (α a).toMonoidHom=P := by
    apply map_injective hiL
    rw [map_map,hα,←map_map,hPR]
    exact mem_normalizer_iff_map_conj_eq.mp (hAR a.property)
  have hαD (a : A) : D'.map (α a).toMonoidHom=D' := by
    apply map_injective hiL
    rw [map_map,hα,←map_map,hDmap]
    exact mem_normalizer_iff_map_conj_eq.mp (hAD a.property)
  obtain ⟨hn,_,F,_,_,hF,_,_,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hd : Disjoint (P : Subgroup d.block) D' := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hDodd).pow_left k
  let qF := m.quotientIso.toMonoidHom.comp q
  have hqF : Function.Surjective qF := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkP : pCore 2 d.block ≤ (P : Subgroup d.block) := pCore_isPGroup.le_sylow_of_normal P
  have hkF : qF.ker ≤ (P : Subgroup d.block) := by
    intro l hl
    exact hkP ((QuotientGroup.eq_one_iff l).mp (m.quotientIso.map_eq_one_iff.mp hl))
  have hcD : Nat.card D'=Nat.card F-1 := by
    rw [←card_map_of_injective hiL,hDmap,hDc,hF]
  have hgen := Matrix.SpecialLinearGroup.sylow_normalizer_complement_of_card qF hqF P hkF D' hDP hd hcD
  let P₀ : Sylow 2 K := P.mapSurjective (QuotientGroup.mk'_surjective _)
  let D₀ := D'.map q
  have hpre : (P₀ : Subgroup K).comap q=P := comap_map_eq_self (by
    intro l hl
    exact hkP ((QuotientGroup.eq_one_iff l).mp hl))
  have hNmap : (normalizer (P : Set d.block)).map q=normalizer (P₀ : Set K) := by
    have hh : (normalizer (P₀ : Set K)).comap q=normalizer (P : Set d.block) := by
      change (normalizer ((P₀ : Subgroup K) : Set K)).comap q =
        normalizer ((P : Subgroup d.block) : Set d.block)
      rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),hpre]
    rw [←hh,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  refine ⟨F,inferInstance,inferInstance,inferInstance,hF,
    m.quotientIso.trans (Theory.PSL2.sl2QuotientEquiv F),P₀,D₀,?_,rfl,?_,?_,?_,?_⟩
  · change (P : Subgroup d.block).map q = _
    congr 1
    apply map_injective d.block.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  · exact (map_mono hDP).trans_eq hNmap
  · obtain ⟨k,hk⟩ := P₀.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr (hDodd.of_dvd_nat (card_map_dvd D' q))).pow_left k
  · change (P : Subgroup d.block).map q ⊔ D'.map q = _
    rw [←Subgroup.map_sup,hgen,hNmap]
  · intro a
    have he : (ρ a).toMonoidHom.comp q=q.comp (α a).toMonoidHom := by
      ext l
      exact normalQuotientAction_apply_mk d.block (pCore 2 d.block)
        (inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _)) a) l
    constructor
    · change ((P : Subgroup d.block).map q).map (ρ a).toMonoidHom=P₀
      rw [map_map,he,←map_map,hαP]
      rfl
    · change (D'.map q).map (ρ a).toMonoidHom=D'.map q
      rw [map_map,he,←map_map,hαD]
end CFSG.Quasithin.Chapter2.LinearShadows.Single

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_actor_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    ∃ D B : Subgroup G, D ≤ M ⊓ L ∧ D ≤ B ∧ IsCyclic D ∧ Nat.card D=2^n-1 ∧
      Odd (Nat.card B) ∧ R ⊓ centralizer (B : Set G)=⊥ ∧
      let A := S ⊓ normalizer (B : Set G)
      IsComplement' (R.subgroupOf S) (A.subgroupOf S) ∧
      IsComplement' (L.subgroupOf d.H) (A.subgroupOf d.H) ∧
      A ≤ normalizer (D : Set G) ∧
      let ρ := (normalQuotientAction d.block (pCore 2 d.block)).comp
        (inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _)))
      Function.Injective ρ ∧
      let K := d.block ⧸ pCore 2 d.block
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F=2^n ∧
        ∃ (_e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
          (P : Sylow 2 K) (D₀ : Subgroup K),
          (P : Subgroup K) = ((d.S : Subgroup d.H).subgroupOf d.block).map
            (QuotientGroup.mk' (pCore 2 d.block)) ∧
          D₀ = (D.comap (d.H.subtype.comp d.block.subtype)).map
            (QuotientGroup.mk' (pCore 2 d.block)) ∧
          D₀ ≤ normalizer (P : Set K) ∧ Disjoint (P : Subgroup K) D₀ ∧
          (P : Subgroup K) ⊔ D₀ = normalizer (P : Set K) ∧
          ∀ a : A, (P : Subgroup K).map (ρ a).toMonoidHom = P ∧
            D₀.map (ρ a).toMonoidHom=D₀ := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  obtain ⟨D,B,hDM,hDB,hcyc,hcard,_,hodd,_,_,hBR,_,hSn,_,hfixed,hcomp,_⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  have hc := source_torus_normalizer_complements_of_choice d hG T hST hsingle hL hM hTM hunique B hcomp
  have hi := source_torus_normalizer_quotient_action_faithful d hG T hST hsingle hL hM hTM hunique B hcomp
  have hAD := torusNormalizer_preserves_borel_complement S R D B
    (T.isPGroup'.to_le ((sSup_le fun _ h => h.1).trans hST.le)) hodd hDB (hDB.trans hBR) hSn
  exact ⟨D,B,hDM,hDB,hcyc,hcard,hodd,hfixed,hc.2.2.2.2.1,hc.2.2.2.2.2,hAD,hi,
    source_field_actor_borel_of_choice d hG T hST hsingle hL hM hTM hunique
      D B hDM hDB hodd hcard hSn⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
