module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterGeometry
public import Theory.SpecificGroups.PSL2.SylowIntersections
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterGeometry
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterCentralizer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# Local Sylow maximality and the original G₂ equality S = T

For the original torus involution t, the fixed positive root F has a nonzero
parameter. Under the same right parabolic map it lies in C_S(t) and escapes
O₂(O²(H)). Distinct Sylow two-subgroups of the binary PSL₂ quotient intersect
trivially, so every two-subgroup of O²(H) containing C_S(t) lies in S.

If a two-group U in N_G(O²(H)) centralizes t and contains C_T(t), its
intersection with O²(H) therefore determines the unique Sylow subgroup S.
Thus U normalizes S. The actual torus splitting gives S C_T(t) = T, so the
two-group S U contains the ambient Sylow subgroup T and equals T. This proves
local Sylow maximality, and excludes the strict local enlargement already
constructed from the ambient q⁴ lower bound. Consequently S = T at every
original exponent n > 1, including even degrees and field four.

The Chapter 12 companion applies this equality to the full short-root
centralizer. Original uniqueness, exhaustive concrete amalgam comparison,
and completion recognition remain inputs or assembly obligations; this
module does not identify the ambient group with a concrete model.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294, and 5.3.3, p.659
(`refs/quasithin.pdf`). Internal imports reuse the same source family's root
and torus transports without changing their public boundaries. Root formulas
retain the attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2LocalSylow
variable {G : Type*} [Group G] [Finite G]

private theorem unique_sylow_above_noncore
    (K : Subgroup G) (P : Sylow 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Theory.PSL2.Group F)
    (C : Subgroup G) (hCP : C ≤ (P : Subgroup K).map K.subtype)
    (hne : ¬ C ≤ K.pCoreIn 2)
    (U : Subgroup G) (hU : IsPGroup 2 U) (hUK : U ≤ K) (hCU : C ≤ U) :
    U ≤ (P : Subgroup K).map K.subtype := by
  let q : K →* Theory.PSL2.Group F := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 K) x)=1 ↔ x ∈ pCore 2 K
    rw [←e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨R,hR⟩ := (hU.comap_subtype (K := K)).exists_le_sylow
  let Pq := P.mapSurjective hq
  let Rq := R.mapSurjective hq
  have heq : Pq=Rq := by
    apply Theory.PSL2.sylow_eq_of_inf_ne_bot
    intro hb
    apply hne
    intro x hx
    have hxK := hUK (hCU hx)
    have hxP : (⟨x,hxK⟩ : K) ∈ P := by
      obtain ⟨y,hy,hyx⟩ := hCP hx
      exact (show y=⟨x,hxK⟩ from Subtype.ext hyx) ▸ hy
    have hxR : (⟨x,hxK⟩ : K) ∈ R := hR (hCU hx)
    have hh : q ⟨x,hxK⟩ ∈ (Pq : Subgroup _) ⊓ (Rq : Subgroup _) :=
      ⟨mem_map_of_mem q hxP,mem_map_of_mem q hxR⟩
    rw [hb,mem_bot] at hh
    have hxq : (⟨x,hxK⟩ : K) ∈ q.ker := hh
    rw [hk] at hxq
    exact mem_map_of_mem K.subtype hxq
  have hPR : (P : Subgroup K)=(R : Subgroup K) := by
    have hm : (P : Subgroup K).map q=(R : Subgroup K).map q := congrArg Sylow.toSubgroup heq
    have hp : q.ker ≤ (P : Subgroup K) := hk ▸ pCore_isPGroup.le_sylow_of_normal P
    have hr : q.ker ≤ (R : Subgroup K) := hk ▸ pCore_isPGroup.le_sylow_of_normal R
    have hh := congrArg (fun X : Subgroup (Theory.PSL2.Group F) => X.comap q) hm
    simpa only [comap_map_eq_self hp,comap_map_eq_self hr] using hh
  intro x hx
  exact mem_map_of_mem K.subtype (hPR.symm ▸ hR (show (⟨x,hUK hx⟩ : K) ∈ U.subgroupOf K from hx))

omit [Finite G] in
private theorem local_maximality
    (T : Sylow 2 G) (K S C E : Subgroup G)
    (hST : S ≤ T) (hSK : S ≤ K) (hC : C ≤ S)
    (hCK : C ≤ E) (hSE : S ⊔ E=(T : Subgroup G))
    (hunique : ∀ U : Subgroup G, IsPGroup 2 U → U ≤ K → C ≤ U → U ≤ S)
    (V : Subgroup G) (hV : IsPGroup 2 V) (hEV : E ≤ V)
    (hVK : V ≤ normalizer (K : Set G)) : V ≤ T := by
  let R := V ⊓ K
  have hCR : C ≤ R := le_inf (hCK.trans hEV) (hC.trans hSK)
  have hRS : R ≤ S := hunique R (hV.to_le inf_le_left) inf_le_right hCR
  have hVR : V ≤ normalizer (R : Set G) :=
    (le_inf V.le_normalizer hVK).trans inf_normalizer_le_normalizer_inf
  have hVS : V ≤ normalizer (S : Set G) := by
    intro v hv
    have hmap (v : V) : S.map (MulAut.conj v.val).toMonoidHom ≤ S := by
      apply hunique _ ((T.isPGroup'.to_le hST).map _)
      · rintro _ ⟨x,hx,rfl⟩
        exact (mem_normalizer_iff.mp (hVK v.property) x).mp (hSK hx)
      · intro x hx
        refine ⟨v.val⁻¹*x*v.val,?_,?_⟩
        · exact hRS (by simpa only [inv_inv] using
            (mem_normalizer_iff.mp (hVR (V.inv_mem v.property)) x).mp (hCR hx))
        · simp [mul_assoc]
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact hmap ⟨v,hv⟩ (mem_map_of_mem _ hx)
    · intro hx
      have hh := hmap (⟨v,hv⟩⁻¹) (mem_map_of_mem (MulAut.conj v⁻¹).toMonoidHom hx)
      simpa [mul_assoc] using hh
  have htwo := (T.isPGroup'.to_le hST).to_sup_of_normal_left' hV hVS
  have hTV : (T : Subgroup G) ≤ S ⊔ V := hSE ▸ sup_le_sup_left hEV S
  have heq := T.is_maximal' htwo hTV
  exact le_sup_right.trans_eq heq

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2LocalSylow

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The fixed root F survives in the actual right two-core quotient. -/
theorem Preparation.g2_outer_fixed_not_le_core
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htD : t.val ∈ normalizer (D : Set G)) :
    ¬ sourceS L H ⊓ centralizer ({t.val} : Set G) ≤ (residual H).pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have hS := source_g2_inverse_sylow_image d h hH.1.1.2 e
  obtain ⟨ρ,hρ⟩ := d.g2_torus_normalizer_root_action h hH.1.1.2 hp F e hD hmark t htD
  have ht : t.val^2=1 := congrArg Subtype.val ((orderOf_eq_prime_iff.mp ht2).1)
  obtain ⟨x,hx,hfix⟩ := G2OuterGeometry.nonzero_fixed (ρ 5)
    (G2OuterGeometry.root_action_involutive f hf t.val ht ρ hρ 5)
  have hm := G2OuterGeometry.fixed_root_mem f (sourceS L H)
    (sourceS L H ⊓ centralizer ({t.val} : Set G)) hS t.val le_rfl ρ hρ 5 x hfix
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hJ : J=solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJf : J.map f=residual H := by
    rw [hJ,show f=P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 1
  have hQ : ((radical₁ (F := F)).subgroupOf parabolic₁).map f=(residual H).pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 local₁ parabolic₁ (le_sup_left.trans_eq local₁_sup_borel),
      local₁_pCoreIn] at hh
    exact hh
  intro hle
  have hmem := hle hm
  rw [←hQ,mem_map_iff_mem hf] at hmem
  obtain ⟨v,hv,he⟩ := hmem
  have hh := congrFun (unipotentProduct_injective he) 5
  exact hx (by simpa [hv] using hh.symm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- Every local two-group containing C_T(t) equals it, for the same marked t. -/
theorem Preparation.g2_outer_centralizer_local_maximal
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htD : t.val ∈ normalizer (D : Set G))
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (hEU : (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) ≤ U)
    (hUC : U ≤ normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)) :
    U = (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  let S := sourceS L H
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let C := S ⊓ centralizer ({t.val} : Set G)
  have hST : S ≤ T := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hs := d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)
  have hSK : S ≤ residual H := hs.2.2.2.2 1
  obtain ⟨b⟩ := hs.2.2.1
  let eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans local₁CoreQuotientEquivPSL
  have hPs := d.sylow 1
  change ∃ P : Sylow 2 (residual H),
    (P : Subgroup (residual H)).map (residual H).subtype = S ⊓ residual H at hPs
  obtain ⟨P,hP⟩ := hPs
  rw [inf_eq_left.mpr hSK] at hP
  have hne := d.g2_outer_fixed_not_le_core h hH hp F e hD hmark t ht2 htD
  have hunique (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQK : Q ≤ residual H) (hCQ : C ≤ Q) : Q ≤ S := by
    rw [←hP]
    exact G2LocalSylow.unique_sylow_above_noncore (residual H) P eR C
      (inf_le_left.trans_eq hP.symm) hne Q hQ hQK hCQ
  have hsplit : S ⊔ E=(T : Subgroup G) := by
    obtain ⟨D',hD',_,hmark',_,_,hsplit⟩ := d.g2_source_sylow_torus_split h hH.1.1.2 hp F e
    have heq := marked_torus_unique d h hH.1.1.2 F e hD hD' hmark hmark'
    subst D'
    have hUE := (d.g2_outer_torus_centralizer h hH.1.1.2 hp F e hD hmark t htD).1
    apply le_antisymm (sup_le hST inf_le_left)
    intro x hx
    have hx' : x ∈ (S : Set G) * ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := hsplit ▸ hx
    obtain ⟨s,hs,u,hu,rfl⟩ := hx'
    exact (S ⊔ E).mul_mem (mem_sup_left hs) (mem_sup_right ⟨hu.1,hUE hu⟩)
  have hUT := G2LocalSylow.local_maximality T (residual H) S C E hST hSK
    inf_le_left (inf_le_inf_right _ hST) hsplit hunique U hU hEU (hUC.trans inf_le_left)
  exact le_antisymm (le_inf hUT (hUC.trans inf_le_right)) hEU

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- C_T(t) is an actual Sylow subgroup of N_G(O²(H)) intersect C_G(t). -/
theorem Preparation.g2_outer_centralizer_local_sylow
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htD : t.val ∈ normalizer (D : Set G)) :
    let C := normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype =
      (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  let C := normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  have hEC : E ≤ C := inf_le_inf_right _ (hH.1.1.2.trans (le_normalizer_residual H))
  obtain ⟨P,hP⟩ := ((T.isPGroup'.to_le (show E ≤ T from inf_le_left)).comap_subtype (K := C)).exists_le_sylow
  refine ⟨P,d.g2_outer_centralizer_local_maximal h hH hp F e hD hmark t ht2 htD
    ((P : Subgroup C).map C.subtype) (P.isPGroup'.map _) ?_ (map_subtype_le _)⟩
  change E ≤ (P : Subgroup C).map C.subtype
  rw [←map_subgroupOf_eq_of_le hEC]
  exact map_mono hP

/-- Local Sylow maximality excludes the strict enlargement and proves S=T. -/
theorem Preparation.g2_sourceS_eq_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    sourceS L H = (T : Subgroup G) := by
  obtain ⟨e,_⟩ := d.g2_completion_involution_classes h hH hp F he
  by_contra hne
  obtain ⟨D,hD,_,hmark,eR,t,ht2,htS,htD,_⟩ :=
    d.g2_exists_outer_involution h hH.1.1.2 hp F e hne
  obtain ⟨U,hU,hEU,hUC,_⟩ :=
    d.g2_outer_involution_local_enlargement h hH hp F e hD hmark t ht2 htS htD
  exact hEU.ne (d.g2_outer_centralizer_local_maximal h hH hp F e hD hmark
    t ht2 htD U hU hEU.le hUC).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
