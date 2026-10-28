module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootActionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterInvolution
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterInvolution
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2LocalSylow

/-!
# Triality fixed roots and local centralizer Sylow subgroups

Conjugation by the original marked torus involution preserves both the
torus and the positive subgroup through the same right-parabolic map.
The genuine cubic root calculation constructs a fixed element outside
the arms radical. Transport identifies that radical with O₂(O²(H)),
so C_S(t) is not contained in the original right two-core.

Distinct Sylow two-subgroups of PSL₂(q³) intersect trivially. Thus every
two-subgroup of O²(H) containing C_S(t) lies in S. A two-subgroup of the
right normalizer containing C_T(t) consequently normalizes S. The original
cyclic torus complement gives S C_T(t)=T, so ambient Sylow maximality
forces the larger local two-subgroup back into T. Hence C_T(t) is Sylow
in N_G(O²(H)) intersect C_G(t), for every original n>1, including field four.

This proves the local maximality input to F.4.37, with no root-action or
fixed-lift premise. Sylow placement in all of C_G(t), the full common
coefficient action, S=T and triality recognition remain assembly obligations.
The Chapter 12 companion supplies the literal chosen-module application.

Source: Aschbacher--Smith F.4.37--38, pp.293--294, and 5.3.3, p.659
(`refs/quasithin.pdf`). Internal imports reuse source marking transports,
torus uniqueness and the general PSL₂/Sylow arguments already checked
within this source family, preserving their existing public boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The original torus involution fixes an element of S outside O₂(O²(H)).
It is constructed on the genuine cubic-field root and transported through
the same original right parabolic map. -/
theorem Preparation.triality_outer_fixed_not_le_core
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htD : t.val∈normalizer (D : Set G)) :
    ¬ sourceS L H ⊓ centralizer ({t.val} : Set G) ≤ (residual H).pCoreIn 2 := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have hS := d.triality_right_unipotent_image h hTH P rfl e
  have htY := source_parabolics_normalized h.sylow_normalizes hTH 1 t.property
  let b := MulAut.congr e.right (Y.normalizerMonoidHom ⟨t.val,htY⟩)
  have hb (x : parabolic P .arms) : f (b x)=t.val*f x*t.val⁻¹ := by
    change (e.right.symm (e.right (Y.normalizerMonoidHom ⟨t.val,htY⟩ (e.right.symm x)))).val=_
    rw [e.right.symm_apply_apply]
    rfl
  have hU : ((unipotent P).subgroupOf (parabolic P .arms)).map b.toMonoidHom=
      (unipotent P).subgroupOf (parabolic P .arms) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hxS : f x∈sourceS L H := hS ▸ mem_map_of_mem f hx
      have hyS : f (b x)∈sourceS L H := by
        rw [hb]
        exact (mem_normalizer_iff.mp (sylow_normalizes_sourceS h.sylow_normalizes hTH t.property) _).mp hxS
      rw [←hS,mem_map_iff_mem hf] at hyS
      exact hyS
    · rw [card_map_of_injective b.injective]
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  have hmr := (source_triality_torus_markings m hm e (hD.trans hC) hmark).2
  have hbD := torus_action_map (M := Carrier P) Y (parabolic P .arms)
    (torus P) e.right D t.val htY htD hmr
  have ht : t.val*t.val=1 := by
    have hh : t.val^2=1 := congrArg Subtype.val ((orderOf_eq_prime_iff.mp ht2).1)
    exact (pow_two t.val).symm.trans hh
  have hinv : Function.Involutive b := by
    intro x
    apply hf
    rw [hb,hb]
    calc
      t.val*(t.val*f x*t.val⁻¹)*t.val⁻¹ = (t.val*t.val)*f x*(t.val*t.val)⁻¹ := by group
      _ = f x := by rw [ht]; simp
  obtain ⟨x,hxU,hfix,hxQ⟩ := TrialityRootAction.fixed_root_outside_radical
    m hm (d.triality_local_structure h hTH hp m hm e).2.1 b hbD hU hinv
  have hx : f x∈sourceS L H ⊓ centralizer ({t.val} : Set G) := by
    refine ⟨hS ▸ mem_map_of_mem f hxU,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp ((hb x).symm.trans (congrArg f hfix))).symm
  let J := (localFactor P .arms).subgroupOf (parabolic P .arms)
  have hJ : J=solvableResidual (parabolic P .arms) := by
    apply map_injective (parabolic P .arms).subtype_injective
    rw [map_subgroupOf_eq_of_le (localFactor_le_parabolic P .arms),
      TrialityComparison.arms_parabolic_residual P rfl]
  have hJf : J.map f=residual H := by
    rw [hJ,show f=Y.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hTH hp 1
  have hQ : ((radical P .arms).subgroupOf (parabolic P .arms)).map f=(residual H).pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 (localFactor P .arms) (parabolic P .arms)
      (localFactor_le_parabolic P .arms)] at hh
    change (((pCore 2 (localFactor P .arms)).map (localFactor P .arms).subtype).subgroupOf
      (parabolic P .arms)).map f=(residual H).pCoreIn 2 at hh
    rw [localFactor_twoCore_map P rfl .arms] at hh
    exact hh
  intro hle
  have hh := hle hx
  rw [←hQ,mem_map_iff_mem hf] at hh
  exact hxQ hh

/-- Every two-subgroup of the original right normalizer centralizing t and
containing C_T(t) equals C_T(t). The fixed root forces the unique PSL₂(q³)
Sylow subgroup, and the original cyclic complement restores all of T. -/
theorem Preparation.triality_outer_centralizer_local_maximal
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htD : t.val∈normalizer (D : Set G))
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (hEU : (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) ≤ U)
    (hUC : U ≤ normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)) :
    U=(T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  let S := sourceS L H
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let C := S ⊓ centralizer ({t.val} : Set G)
  have hST : S ≤ T := sourceS_le_sylow h.sylow_normalizes hTH
  have hSK : S ≤ residual H :=
    d.triality_sourceS_le_factors h hTH hp m hm (Or.inr ⟨e⟩) 1
  obtain ⟨b⟩ := (d.triality_local_structure h hTH hp m hm e).2.2.2.1
  let eR : (residual H ⧸ pCore 2 (residual H)) ≃*
      Theory.PSL2.Group (ExtensionField (binaryParameters m hm)) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (localFactorArmsQuotientEquivPSL2 (binaryParameters m hm) rfl)
  have hPs := d.sylow 1
  change ∃ P : Sylow 2 (residual H),
    (P : Subgroup (residual H)).map (residual H).subtype=S ⊓ residual H at hPs
  obtain ⟨P,hP⟩ := hPs
  rw [inf_eq_left.mpr hSK] at hP
  have hne := d.triality_outer_fixed_not_le_core h hTH hp m hm e hD hmark t ht2 htD
  have hunique (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQK : Q ≤ residual H) (hCQ : C ≤ Q) : Q ≤ S := by
    rw [←hP]
    exact G2LocalSylow.unique_sylow_above_noncore (residual H) P eR C
      (inf_le_left.trans_eq hP.symm) hne Q hQ hQK hCQ
  have hsplit : S ⊔ E=(T : Subgroup G) := by
    obtain ⟨D',hD',_,hmark',_,_,hsplit⟩ := d.triality_source_sylow_torus_split h hTH hp m hm e
    have heq := triality_marked_torus_unique d h hTH m hm e hD hD' hmark hmark'
    subst D'
    have hUE := (d.triality_outer_torus_centralizer h hTH hp m hm e hD hmark t htD).1
    apply le_antisymm (sup_le hST inf_le_left)
    intro x hx
    have hx' : x∈(S : Set G)*((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := hsplit ▸ hx
    obtain ⟨s,hs,u,hu,rfl⟩ := hx'
    exact (S ⊔ E).mul_mem (mem_sup_left hs) (mem_sup_right ⟨hu.1,hUE hu⟩)
  have hUT := G2LocalSylow.local_maximality T (residual H) S C E hST hSK
    inf_le_left (inf_le_inf_right _ hST) hsplit hunique U hU hEU (hUC.trans inf_le_left)
  exact le_antisymm (le_inf hUT (hUC.trans inf_le_right)) hEU

/-- C_T(t) is Sylow in N_G(O²(H)) ∩ C_G(t), with the original torus and
whole-overlap comparison. Ambient Sylow placement still requires F.4.37. -/
theorem Preparation.triality_outer_centralizer_local_sylow
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htD : t.val∈normalizer (D : Set G)) :
    let C := normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype=
      (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  let C := normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  have hEC : E ≤ C := inf_le_inf_right _ (hTH.trans (le_normalizer_residual H))
  obtain ⟨P,hP⟩ := ((T.isPGroup'.to_le (show E ≤ T from inf_le_left)).comap_subtype (K := C)).exists_le_sylow
  refine ⟨P,d.triality_outer_centralizer_local_maximal h hTH hp m hm e hD hmark t ht2 htD
    ((P : Subgroup C).map C.subtype) (P.isPGroup'.map _) ?_ (map_subtype_le _)⟩
  change E ≤ (P : Subgroup C).map C.subtype
  rw [←map_subgroupOf_eq_of_le hEC]
  exact map_mono hP

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
