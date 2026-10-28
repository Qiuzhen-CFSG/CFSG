module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialFieldAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Maximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCenterKernel
public import Theory.SpecificGroups.PSL2.TorusFixedInner
public import Theory.AtlasPort.LinearGroups.G2.NormalizedRootCentralizers

/-!
# G₂ and triality center fixers and the original left quotient

Let K = O²(H) and S = O₂(N_G(L) ∩ H). In the actual compatible G₂
comparison, a left Borel element fixing Z(K) belongs to S. In model
coordinates its unipotent factor centralizes the highest root, while its
two torus parameters are forced to one by the left local-factor condition
and fixation of the highest-root point. Whole-overlap agreement transports
that same point through both maps.

For t ∈ C_T(Z(K)), all displacements on the original left Borel therefore
lie in S. The binary PSL₂ normalizer-displacement theorem makes its action
on L/O₂(L) inner. Cancelling the inner representative gives the actual
containment C_T(Z(K)) ≤ S O₂(LT), valid at every original exponent n > 1.

The triality analogue uses the central-local Borel kernel proved in
`RankOneModuleGenericGlobalTrialityCenterKernel`. The actual right center
contains the same highest-root point transported through both compatible
maps. This gives the same left-inner conclusion and S O₂(LT) containment,
without a parity restriction on the original degree.

The intrinsic core O₂(LT) remains to be removed in both rows. The existing computation
of O₂(G₀T), for the larger left parabolic G₀, does not identify this core.
Thus this is a reduction of the centralizer premise in F.4.35, not yet
its discharge. Source: Aschbacher–Smith F.4.29(2,7), pp.289–290,
F.4.35, p.292, and its application in 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem quotient_inner_of_displacements
    {K : Subgroup G} {T : Sylow 2 G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Theory.PSL2.Group F)
    (t : T)
    (hd : ∀ x ∈ normalizer (P : Set K),
      x⁻¹ * K.normalizerMonoidHom ⟨t,hTK t.property⟩ x ∈ P) :
    pCoreJoinAction 2 hTK (inclusion le_sup_right t) ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
  let a : MulAut K := K.normalizerMonoidHom ⟨t,hTK t.property⟩
  let b := pCoreJoinAction 2 hTK (inclusion le_sup_right t)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  let c := MulAut.congr e b
  have he (x : K) : q (a x) = c (q x) := by
    change e (QuotientGroup.mk' _ (a x)) = e (b (e.symm (e (QuotientGroup.mk' _ x))))
    rw [e.symm_apply_apply]
    exact congrArg e (pCoreJoinAction_mk 2 hTK (inclusion le_sup_right t) x).symm
  have hPa : (P : Subgroup K).map a.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP] at hx ⊢
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem t.property hx)
        ((T : Subgroup G).inv_mem t.property)
    · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
  have hQc : (Q : Subgroup (Theory.PSL2.Group F)).map c.toMonoidHom = Q := by
    change ((P : Subgroup K).map q).map c.toMonoidHom = _
    have hh : c.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext (fun x => (he x).symm)
    rw [Subgroup.map_map,hh,←Subgroup.map_map,hPa]
    rfl
  have hk : q.ker ≤ (P : Subgroup K) := by
    intro x hx
    exact pCore_isPGroup.le_sylow_of_normal P
      ((QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp hx))
  have hpre : (Q : Subgroup (Theory.PSL2.Group F)).comap q = P :=
    comap_map_eq_self hk
  have hN : (normalizer (Q : Set (Theory.PSL2.Group F))).comap q = normalizer (P : Set K) := by
    change (normalizer ((Q : Subgroup (Theory.PSL2.Group F)) : Set _)).comap q =
      normalizer ((P : Subgroup K) : Set K)
    rw [comap_normalizer_eq_of_surjective _ hq,hpre]
  have hc : c ∈ MulAut.innerSubgroup (Theory.PSL2.Group F) :=
    Matrix.ProjectiveSpecialLinearGroup.inner_of_normalizer_displacements F Q c hQc (by
      intro x hx
      obtain ⟨y,rfl⟩ := hq x
      have hy : y ∈ normalizer (P : Set K) := hN ▸ hx
      rw [←he,←map_inv,←map_mul]
      exact mem_map_of_mem q (hd y hy))
  rw [←MulAut.map_innerSubgroup_congr e] at hc
  obtain ⟨a,ha,hea⟩ := hc
  change b ∈ _
  exact (MulAut.congr e).injective hea ▸ ha

/-- The original left quotient detects Sylow actors fixing the right center,
provided the actual left Borel has precisely S as its pointwise kernel. -/
private theorem Preparation.source_center_fixer_inner_of_borel_kernel
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B Z : Subgroup G} {n : ℕ}
    (_d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hZN : localBorel T L ≤ normalizer (Z : Set G))
    (hdet : localBorel T L ⊓ centralizer (Z : Set G) ≤ sourceS L H) :
    ∀ t : T, t.val ∈ centralizer (Z : Set G) →
      pCoreJoinAction 2 h.sylow_normalizes (inclusion le_sup_right t) ∈
        MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have hP' : (P : Subgroup L) = (T : Subgroup G).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  have hB : (normalizer (P : Set L)).map L.subtype = localBorel T L := by
    rw [localBorel_eq_map]
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [hP']
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  intro t ht
  have hd : ∀ x ∈ normalizer (P : Set L),
      x⁻¹ * L.normalizerMonoidHom ⟨t,h.sylow_normalizes t.property⟩ x ∈ P := by
    intro x hx
    have hxB : x.val ∈ localBorel T L := hB ▸ mem_map_of_mem L.subtype hx
    have htN : t.val ∈ normalizer (localBorel T L : Set G) := by
      apply inf_normalizer_le_normalizer_inf
      refine ⟨h.sylow_normalizes t.property,?_⟩
      apply (normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).le_normalizer
      exact inf_normalizer_le_normalizer_inf
        ⟨(T : Subgroup G).le_normalizer t.property,h.sylow_normalizes t.property⟩
    have htx : t.val * x.val * t.val⁻¹ ∈ localBorel T L :=
      (mem_normalizer_iff.mp htN x.val).mp hxB
    have hdB := (localBorel T L).mul_mem ((localBorel T L).inv_mem hxB) htx
    have hdC : x.val⁻¹ * t.val * x.val * t.val⁻¹ ∈ centralizer (Z : Set G) := by
      have hn := normalizer_le_normalizer_centralizer Z (inv_mem (hZN hxB))
      exact (centralizer (Z : Set G)).mul_mem
        (by simpa only [inv_inv] using (mem_normalizer_iff.mp hn t.val).mp ht) ((centralizer _).inv_mem ht)
    have hdC' : x.val⁻¹ * (t.val * x.val * t.val⁻¹) ∈ centralizer (Z : Set G) := by
      simpa only [mul_assoc] using hdC
    have hdS := hdet ⟨hdB,hdC'⟩
    change x⁻¹ * L.normalizerMonoidHom ⟨t,h.sylow_normalizes t.property⟩ x ∈ (P : Subgroup L)
    rw [hP']
    exact sourceS_le_sylow h.sylow_normalizes hTH hdS
  exact quotient_inner_of_displacements h.sylow_normalizes P hP' e t hd

open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
private theorem g2_borel_point_kernel
    {F : Type} [Field F] [CharP F 2]
    (g : Model F) (hgL : g ∈ local₂) (hgB : g ∈ Atlas.G2.borel)
    (hgC : Commute g (rootA (1:F))) : g ∈ unipotent := by
  obtain ⟨⟨u,v⟩,he⟩ := borelProductEquiv.surjective ⟨g,hgB⟩
  have he : (u : Model F) * v.val = g := congrArg Subtype.val he
  obtain ⟨⟨l,m⟩,hv⟩ := v.property
  have hve : (v : Model F) = torus l m := hv.symm
  rw [hve] at he
  have htL : torus l m ∈ local₂ (F := F) := by
    have hh := (local₂ (F := F)).mul_mem
      ((local₂ (F := F)).inv_mem (unipotent_le_local₂ u.property)) hgL
    rwa [←he,inv_mul_cancel_left] at hh
  have hl : l = 1 := by
    rw [local₂_eq_fixingFirstVector] at htL
    change (torus l m).val (Atlas.SplitOctonion.basisVector 0) = _ at htL
    rw [torus_first_basis] at htL
    apply Units.ext
    simpa [Atlas.SplitOctonion.basisVector] using congrFun htL 0
  have huc : Commute (u : Model F) (rootA (1:F)) := by
    have hu : (u : Model F) ∈ unipotentRange := unipotent_eq_range.le u.property
    obtain ⟨a,ha⟩ := hu
    rw [←ha]
    exact unipotentProduct_commute_rootA a 1
  have htc : Commute (torus l m) (rootA (1:F)) := by
    rw [←he] at hgC
    simpa only [inv_mul_cancel_left] using huc.inv_left.mul_left hgC
  have hm : m = 1 := by
    have hh := (NormalizedRootCentralizers.torus_commute_rootA_iff l m one_ne_zero).mp htc
    apply Units.ext
    simpa only [hl,Units.val_one,one_mul] using hh
  rw [hl,hm] at he
  have ht1 : torus (1:Fˣ) 1 = 1 := torusHom.map_one
  rw [ht1,mul_one] at he
  exact he ▸ u.property

private theorem g2_source_sylow_image
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ((sourceS L H).subgroupOf (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)).map
      ((parabolic₂ (F := F)).subtype.comp e.left.toMonoidHom) = unipotent := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let R := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : P →* Model F := (parabolic₂ (F := F)).subtype.comp e.left.toMonoidHom
  let V := ((sourceS L H).subgroupOf P).map f
  have hVP : IsPGroup 2 V := ((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map f
  have hVB : V ≤ Atlas.G2.borel := by
    rintro _ ⟨x,hx,rfl⟩
    let b : (P ⊓ R : Subgroup G) := ⟨x.val,x.property,
      (show sourceS L H ≤ R from le_sup_right.trans le_sup_left) hx⟩
    have heq := congrArg Subtype.val (e.left_commutes b)
    change f x = (e.middle b).val at heq
    rw [heq]
    exact (ChapterF.GreenBook.LieModels.G2.overlap_eq_borel (F := F)).le (e.middle b).property
  let U := (Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype
    (show unipotent ≤ Atlas.G2.borel from le_sup_left)
  let : (U : Subgroup (Atlas.G2.borel (K := F))).Normal := EvenBorelTorus.radical_normal
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  obtain ⟨D,hD⟩ := (hVP.comap_subtype : IsPGroup 2 (V.subgroupOf Atlas.G2.borel)).exists_le_sylow
  have hDU : D = U := Subsingleton.elim _ _
  have hVU : V ≤ unipotent := by
    intro x hx
    have hh := hD (show (⟨x,hVB hx⟩ : Atlas.G2.borel (K := F)) ∈ V.subgroupOf Atlas.G2.borel from hx)
    rw [hDU] at hh
    exact hh
  obtain ⟨D,hD⟩ := (d.hypothesisF11 h hTH).sylow_parabolic 0
  let U' := ((unipotent (K := F)).subgroupOf parabolic₂).map e.left.symm.toMonoidHom
  have hSU : (D : Subgroup P) ≤ U' := by
    intro x hx
    have hxS : x.val ∈ sourceS L H := hD.le (mem_map_of_mem P.subtype hx)
    have hxU : f x ∈ unipotent := hVU (mem_map_of_mem f hxS)
    exact ⟨e.left x,hxU,e.left.symm_apply_apply x⟩
  have heq := D.is_maximal' ((unipotent_isTwoGroup.comap_subtype).map e.left.symm.toMonoidHom) hSU
  have hU' : U'.map P.subtype = sourceS L H := by
    change U' = (D : Subgroup P) at heq
    rw [heq]
    exact hD
  have hsub : (sourceS L H).subgroupOf P = U' := by
    change (sourceS L H).comap P.subtype = U'
    rw [←hU',comap_map_eq_self_of_injective P.subtype_injective]
  rw [hsub,Subgroup.map_map]
  change ((unipotent (K := F)).subgroupOf parabolic₂).map
    ((parabolic₂ (F := F)).subtype.comp
      (e.left.toMonoidHom.comp e.left.symm.toMonoidHom)) = unipotent
  have hh : e.left.toMonoidHom.comp e.left.symm.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact e.left.apply_symm_apply x
  rw [hh,MonoidHom.comp_id]
  exact map_subgroupOf_eq_of_le (unipotent_le_local₂.trans local₂_le_parabolic₂)

/-- The original left Borel fixes the entire right center only inside S.
The compatible maps, including their whole-overlap agreement, supply the
same highest-root element on both sides. -/
theorem Preparation.g2_left_borel_center_kernel
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    localBorel T L ⊓ centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤
      sourceS L H := by
  have hF := (d.g2_local_structure h hTH hp F he).1
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let R := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : P →* Model F := (parabolic₂ (F := F)).subtype.comp e.left.toMonoidHom
  let r : parabolic₁ (F := F) →* G := R.subtype.comp e.right.symm.toMonoidHom
  have hr : Function.Injective r := R.subtype_injective.comp e.right.symm.injective
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  have hLf : (L.subgroupOf P).map f = local₂ := by
    have hL : L.subgroupOf P = solvableResidual P := by
      apply map_injective P.subtype_injective
      rw [map_subgroupOf_eq_of_le hLP]
      exact (d.parabolic_residuals h hTH hp 0).symm
    rw [hL,show f = (parabolic₂ (F := F)).subtype.comp e.left.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.left.toMonoidHom e.left.surjective]
    exact HigherFieldResiduals.parabolic₂_residual hq
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hJ : J = solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJr : J.map r = residual H := by
    rw [hJ,show r = R.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hTH hp 1
  let z : parabolic₁ (F := F) := ⟨rootA 1,
    borel_le_parabolic₁ (mem_sup_left (show rootA (1:F) ∈ unipotent from subset_closure (by simp)))⟩
  have hzJ : z ∈ (center J).map J.subtype := by
    have hzL : z ∈ J := radical₁_le_local₁ (rootA_mem_radical₁ _)
    refine ⟨⟨z,hzL⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA (1:F) x.property)
  have hz : r z ∈ (center (residual H)).map (residual H).subtype := by
    have hh := mem_map_of_mem r hzJ
    rw [map_subgroup_center_eq r hr,hJr] at hh
    exact hh
  let zL : P := e.left.symm ⟨rootA 1,
    borel_le_parabolic₂ (mem_sup_left (show rootA (1:F) ∈ unipotent from subset_closure (by simp)))⟩
  have hzLR : zL.val = r z := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
      ⟨rootA 1,z.property,borel_le_parabolic₂ (mem_sup_left (show rootA (1:F) ∈ unipotent from subset_closure (by simp)))⟩
    exact (congrArg Subtype.val (e.symm.left_commutes b)).trans
      (congrArg Subtype.val (e.symm.right_commutes b)).symm
  intro x hx
  let y : P := ⟨x,hLP hx.1.1⟩
  have hyR : x ∈ R := by
    change x ∈ residual H ⊔ sourceS L H ⊔ ChapterF.Source.borel L (sourceS L H)
    exact mem_sup_right (d.left_borel_eq.symm ▸ hx.1)
  let b : (P ⊓ R : Subgroup G) := ⟨x,y.property,hyR⟩
  have hyB : f y ∈ Atlas.G2.borel := by
    have hh := congrArg Subtype.val (e.left_commutes b)
    change f y = (e.middle b).val at hh
    rw [hh]
    exact (ChapterF.GreenBook.LieModels.G2.overlap_eq_borel (F := F)).le (e.middle b).property
  have hyL : f y ∈ local₂ := hLf ▸ mem_map_of_mem f hx.1.1
  have hez : f zL = rootA 1 := congrArg Subtype.val (e.left.apply_symm_apply _)
  have hyC : Commute (f y) (rootA (1:F)) := by
    change f y * rootA (1:F) = rootA (1:F) * f y
    rw [←hez,←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    change x*zL.val=zL.val*x
    rw [hzLR]
    exact (mem_centralizer_iff.mp hx.2 _ hz).symm
  have hyU := g2_borel_point_kernel (f y) hyL hyB hyC
  rw [←g2_source_sylow_image d h hTH e] at hyU
  obtain ⟨a,ha,hea⟩ := hyU
  have hay : a = y := (parabolic₂ (F := F)).subtype_injective.comp e.left.injective hea
  change y ∈ (sourceS L H).subgroupOf P
  rw [←hay]
  exact ha

/-- Every original Sylow actor fixing the right G₂ center has inner action
on the original left quotient, at every field degree. -/
theorem Preparation.g2_center_fixer_left_inner
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (t : T) (ht : t.val ∈ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) :
    pCoreJoinAction 2 h.sylow_normalizes (inclusion le_sup_right t) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  apply d.source_center_fixer_inner_of_borel_kernel h hTH ?_
    (d.g2_left_borel_center_kernel h hTH hp F he) t ht
  have hBP : localBorel T L ≤
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 := by
    rw [←d.left_borel_eq]
    exact le_sup_right
  exact hBP.trans (((normal_subgroupOf_iff_le_normalizer
    (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
      le_sup_left.trans le_sup_left)).mp
        ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (center (residual H))))

omit [Finite G] in
private theorem inner_action_mem_core_join_sylow
    {K : Subgroup G} {T : Sylow 2 G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore 2 K) = ⊥) (t : T)
    (hi : pCoreJoinAction 2 hTK (inclusion le_sup_right t) ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    t.val ∈ (K ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K) := by
  let f := pCoreJoinAction 2 hTK
  obtain ⟨z,hzinner⟩ := hi
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
  have he : f (inclusion le_sup_left k) = f (inclusion le_sup_right t) :=
    (pCoreJoinAction_on_component 2 hTK k).trans hzinner
  have hx : inclusion le_sup_right t * (inclusion le_sup_left k)⁻¹ ∈ f.ker := by
    change f (_ * _) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  rw [pCoreJoinAction_kernel 2 hTK T.isPGroup' hz] at hx
  have hq : t.val * k.val⁻¹ ∈ (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
    mem_map_of_mem (K ⊔ (T : Subgroup G)).subtype hx
  have hQT : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hkT : k.val ∈ (T : Subgroup G) := by
    have hh := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hQT hq)) t.property
    simpa only [_root_.mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hh := ((K ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)).mul_mem
    (mem_sup_left hq) (mem_sup_right ⟨hkT,k.property⟩)
  simpa only [inv_mul_cancel_right] using hh

/-- The remaining G₂ Sylow centralizer lies in S times the intrinsic
core of LT. This isolates the full-extension kernel still to be removed;
no equality of this core with the already computed core of G₀T is used. -/
theorem Preparation.g2_center_fixer_le_left_core_join_sourceS
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ sourceS L H := by
  have hS := (d.g2_local_structure h hTH hp F he).2.2.2.2
  have hs := (d.ordinary_sylow_core_geometry h hTH hS).1 0
  change sourceS L H = (T : Subgroup G) ⊓ L at hs
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv,Subgroup.map_bot]
    exact Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot
  intro t ht
  rw [hs]
  exact inner_action_mem_core_join_sylow h.sylow_normalizes hz ⟨t,ht.1⟩
    (d.g2_center_fixer_left_inner h hTH hp F he ⟨t,ht.1⟩ ht.2)

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
open _root_.Triality.Standard.RadicalCoordinates.Centers

omit [Finite G] in
private theorem triality_center_inverse_value
    {M : Type*} [Group M] (X₀ X₁ : Subgroup G) (Y₀ Y₁ B : Subgroup M)
    (h₀ : B ≤ Y₀) (h₁ : B ≤ Y₁)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X₀ (X₀ ⊓ X₁) X₁ inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups Y₀ B Y₁ h₀ h₁)) (b : B) :
    (e.right.symm ⟨b.val,h₁ b.property⟩).val =
      (e.left.symm ⟨b.val,h₀ b.property⟩).val :=
  (congrArg (fun y : X₁ => y.val) (e.symm.right_commutes b)).trans
    (congrArg (fun y : X₀ => y.val) (e.symm.left_commutes b)).symm

omit [Finite G] in
private theorem triality_center_left_value
    {M : Type*} [Group M] (X₀ X₁ : Subgroup G) (Y₀ Y₁ B : Subgroup M)
    (h₀ : B ≤ Y₀) (h₁ : B ≤ Y₁)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X₀ (X₀ ⊓ X₁) X₁ inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups Y₀ B Y₁ h₀ h₁)) (b : (X₀ ⊓ X₁ : Subgroup G)) :
    (e.left ⟨b.val,b.property.1⟩).val = (e.middle b).val :=
  congrArg (fun y : Y₀ => y.val) (e.left_commutes b)

/-- Whole-overlap compatibility puts a left Borel element fixing the original
right triality center in the original common Sylow S. The central local-factor
condition is used as well as the highest-root condition. -/
theorem Preparation.triality_left_borel_center_kernel
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    localBorel T L ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H := by
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp _ rfl he).elim
  obtain ⟨e⟩ := he
  let P := binaryParameters m hm
  have hq : 2 < P.q := by
    change 2^1 < 2^m
    exact Nat.pow_lt_pow_right (by decide) (d.triality_parameter_gt_one h hp m hm e)
  let X := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : X →* Carrier P := (parabolic P .central).subtype.comp e.left.toMonoidHom
  let r : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hr : Function.Injective r := Y.subtype_injective.comp e.right.symm.injective
  have hLX : L ≤ X := le_sup_left.trans le_sup_left
  have hLf : (L.subgroupOf X).map f = localFactor P .central := by
    have hL : L.subgroupOf X = solvableResidual X := by
      apply map_injective X.subtype_injective
      rw [map_subgroupOf_eq_of_le hLX]
      exact (d.parabolic_residuals h hTH hp 0).symm
    rw [hL,show f = (parabolic P .central).subtype.comp e.left.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.left.toMonoidHom e.left.surjective]
    exact parabolic_solvableResidual_map P rfl hq .central
  let J := (localFactor P .arms).subgroupOf (parabolic P .arms)
  have hJ : J = solvableResidual (parabolic P .arms) := by
    apply map_injective (parabolic P .arms).subtype_injective
    rw [map_subgroupOf_eq_of_le (localFactor_le_parabolic P .arms),
      TrialityComparison.arms_parabolic_residual P rfl]
  have hJr : J.map r = residual H := by
    rw [hJ,show r = Y.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hTH hp 1
  let z := highestHom P rfl (Multiplicative.ofAdd 1)
  have hzH : z ∈ highestRoot P := by rw [←highestHom_range P rfl]; exact ⟨_,rfl⟩
  have hzU : z ∈ unipotent P := map_subtype_le _ (highestRoot_le_center_unipotent P rfl hzH)
  have hzB := unipotent_le_borel P hzU
  let zR : parabolic P .arms := ⟨z,borel_le_parabolic P .arms hzB⟩
  have hzJ : zR ∈ (center J).map J.subtype := by
    have hzL : zR ∈ J := unipotent_le_localFactor P .arms (unipotent_isPGroup_binary P rfl) hzU
    refine ⟨⟨zR,hzL⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    have hx := _root_.Triality.Standard.RadicalCoordinates.localFactor_arms_le_centralizer_center_unipotent
      P rfl x.property
    rw [embedded_center_unipotent P rfl] at hx
    exact (mem_centralizer_iff.mp hx z hzH).symm
  have hz : r zR ∈ (center (residual H)).map (residual H).subtype := by
    have hh := mem_map_of_mem r hzJ
    rw [map_subgroup_center_eq r hr,hJr] at hh
    exact hh
  let zL : X := e.left.symm ⟨z,borel_le_parabolic P .central hzB⟩
  have hzLR : zL.val = r zR := by
    let b : borel P := ⟨z,hzB⟩
    exact (triality_center_inverse_value X Y (parabolic P .central) (parabolic P .arms)
      (borel P) (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e b).symm
  intro x hx
  let y : X := ⟨x,hLX hx.1.1⟩
  have hyY : x ∈ Y := mem_sup_right (d.left_borel_eq.symm ▸ hx.1)
  let b : (X ⊓ Y : Subgroup G) := ⟨x,y.property,hyY⟩
  have hyB : f y ∈ borel P := by
    have hh := triality_center_left_value X Y (parabolic P .central) (parabolic P .arms)
      (borel P) (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e b
    change f y = (e.middle b).val at hh
    rw [hh]
    exact (e.middle b).property
  have hyL : f y ∈ localFactor P .central := hLf ▸ mem_map_of_mem f hx.1.1
  have hez : f zL = z := congrArg (fun y : parabolic P .central => y.val) (e.left.apply_symm_apply _)
  have hyC : Commute (f y) z := by
    change f y * z = z * f y
    rw [←hez,←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    change x*zL.val=zL.val*x
    rw [hzLR]
    exact (mem_centralizer_iff.mp hx.2 _ hz).symm
  have hyU := TrialityCenterComparison.central_borel_point_kernel m hm (f y) hyL hyB hyC
  have hS := d.triality_right_unipotent_image h hTH P rfl e
  let a : parabolic P .arms := ⟨f y,borel_le_parabolic P .arms hyB⟩
  have haS : r a ∈ sourceS L H := hS ▸ mem_map_of_mem r hyU
  have haxy : r a = x := by
    let c : borel P := ⟨f y,hyB⟩
    have hh := triality_center_inverse_value X Y (parabolic P .central) (parabolic P .arms)
      (borel P) (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e c
    exact hh.trans (congrArg (fun y : X => y.val) (e.left.symm_apply_apply y))
  exact haxy ▸ haS


/-- Every original triality center fixer induces an inner automorphism on the
original left binary PSL₂ quotient, with no parity restriction on its degree. -/
theorem Preparation.triality_center_fixer_left_inner
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse))
    (t : T) (ht : t.val ∈ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) :
    pCoreJoinAction 2 h.sylow_normalizes (inclusion le_sup_right t) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  apply d.source_center_fixer_inner_of_borel_kernel h hTH ?_
    (d.triality_left_borel_center_kernel h hTH hp m hm he) t ht
  have hBP : localBorel T L ≤
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 := by
    rw [←d.left_borel_eq]
    exact le_sup_right
  exact hBP.trans (((normal_subgroupOf_iff_le_normalizer
    (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
      le_sup_left.trans le_sup_left)).mp
        ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (center (residual H))))

/-- The triality center fixer lies in S O₂(LT). This isolates the original
intrinsic kernel, without replacing it by the core of the larger parabolic. -/
theorem Preparation.triality_center_fixer_le_left_core_join_sourceS
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ sourceS L H := by
  have hS := d.triality_sourceS_le_factors h hTH hp m hm he
  have hs := (d.ordinary_sylow_core_geometry h hTH hS).1 0
  change sourceS L H = (T : Subgroup G) ⊓ L at hs
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv,Subgroup.map_bot]
    exact Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot
  intro t ht
  rw [hs]
  exact inner_action_mem_core_join_sylow h.sylow_normalizes hz ⟨t,ht.1⟩
    (d.triality_center_fixer_left_inner h hTH hp m hm he ⟨t,ht.1⟩ ht.2)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
