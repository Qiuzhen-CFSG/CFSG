module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.Nonfusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FullNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.InvolutionTransfer
public import Stellmacher.ElementaryAbelianMaxFusion

/-!
# Weak closure and root nonfusion in the prepared symplectic row

The faithful native action of the whole middle excludes outer elements
from elementary subgroups of order at least q³. Consequently the original
Sylow T has exactly the two pure parabolic cores as its maximum elementary
subgroups, and J(T)=S. Their coordinate markings survive both orientations
of the given pure amalgam.

Burnside set fusion first proves each core weakly closed in T, using the
literal identity N_G(S)=D. Burnside element fusion then gives control on
each core centralizer by its original full normalizer. In particular both
root-center memberships are preserved under ambient conjugacy inside Z(S).

This is the weak-closure and root-nonfusion step of Aschbacher–Smith F.4.35,
printed p.292 of `refs/quasithin.pdf`, for the prepared pair of 5.3.1–3.
The field-involution Sylow placement, complete marked three-class comparison,
and ambient order comparison remain separate obligations. No S=T premise is
used; the whole residual, both orientations and n=2 are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- The faithful whole-middle action puts every sufficiently large elementary
subgroup in the pure Borel. -/
theorem Preparation.symplectic_large_elementary_middle_le_pure
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVD : V ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hcard : Nat.card F^3 ≤ Nat.card V) :
    V ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 := by
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let C := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  obtain ⟨hmn,hlift⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  have hm' : 1 < m := hmn.symm ▸ h.exponent
  have hact : ∃ σ : D →* SourceNormalizerExtension.flagAutomorphisms F,
      Function.Injective σ ∧
      ∀ g, (σ g).val ∈ MulAut.innerSubgroup (Sp F) ↔ g.val ∈ C := by
    rcases hlift with ⟨_,σ,hσ,_,_,hi⟩ | ⟨_,σ,hσ,_,_,hi⟩
    · exact ⟨σ,hσ,hi⟩
    · exact ⟨σ,hσ,hi⟩
  obtain ⟨σ,hσ,hi⟩ := hact
  let f : V →* MulAut (Sp F) :=
    (SourceNormalizerExtension.flagAutomorphisms F).subtype.comp
      (σ.comp (inclusion hVD))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (hσ.comp (inclusion_injective hVD))
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hb : f.range ≤ MulAut.innerSubgroup (Sp F) := by
    apply SourceFusionOrder.large_elementary_preserving_is_inner hF hm'
    · rintro a ⟨v,rfl⟩
      exact SourceNormalizerExtension.flag_preservesDiagram _
    · rwa [Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv]
  intro v hv
  exact (hi ⟨v,hVD hv⟩).mp (hb ⟨⟨v,hv⟩,rfl⟩)

/-- Sylow maximality in the pure Borel puts every elementary subgroup of T
of order at least q³ in S. -/
theorem Preparation.symplectic_large_elementary_sylow_le_sourceS
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup G)) (hcard : Nat.card F^3 ≤ Nat.card V) :
    V ≤ sourceS L H := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hTD : (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hVC : V ≤ C := d.symplectic_large_elementary_middle_le_pure h hH hp F hm hF he
    V (hVT.trans hTD) hcard
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  obtain ⟨R,hR⟩ := hs
  have hRT : (R : Subgroup C) ≤ (T : Subgroup G).subgroupOf C := by
    intro x hx
    exact sourceS_le_sylow h.sylow_normalizes hH.1.1.2
      (hR ▸ mem_map_of_mem C.subtype hx)
  have hTR : (T : Subgroup G).subgroupOf C = R :=
    R.is_maximal' (T.isPGroup'.comap_subtype (K := C)) hRT
  intro v hv
  have hvR : (⟨v,hVC hv⟩ : C) ∈ (R : Subgroup C) := by
    rw [←hTR]
    exact hVT hv
  exact hR ▸ mem_map_of_mem C.subtype hvR
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open CentralRootGeometry
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem wing_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {S P : Subgroup G} (hSP : S ≤ P)
    (a : S ≃* unipotent (F := F)) (i : Bool)
    (f : P →* Sp F) (hf : Function.Injective f)
    (hfa : ∀ s : S, f ⟨s.val,hSP s.property⟩ = (a s).val)
    (hcore : (pCore 2 P).map f = (wing i).map unipotent.subtype) :
    ((wing i).comap a.toMonoidHom).map S.subtype = P.pCoreIn 2 := by
  ext x
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hh : f ⟨s.val,hSP s.property⟩ ∈ (pCore 2 P).map f := by
      rw [hcore,hfa]
      exact mem_map_of_mem _ hs
    obtain ⟨p,hp,he⟩ := hh
    have he' : p = ⟨s.val,hSP s.property⟩ := hf he
    exact ⟨p,hp,congrArg Subtype.val he'⟩
  · rintro ⟨p,hp,rfl⟩
    have hh : f p ∈ (wing i).map unipotent.subtype :=
      hcore ▸ mem_map_of_mem f hp
    obtain ⟨u,hu,he⟩ := hh
    let s := a.symm u
    have hsp : (⟨s.val,hSP s.property⟩ : P) = p := by
      apply hf
      rw [hfa]
      simpa only [s,a.apply_symm_apply,Subgroup.subtype_apply] using he
    refine ⟨s,?_,congrArg Subtype.val hsp⟩
    change a (a.symm u) ∈ wing i
    rwa [a.apply_symm_apply]

private theorem pair_max_elementary_geometry
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m)
    {P Q C S : Subgroup G} (hCP : C ≤ P) (hCQ : C ≤ Q) (hSC : S ≤ C)
    (hs : Chapter1.IsSylowIn 2 S C)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) :
    Stellmacher.elementaryAbelianMaxSubgroups S = {P.pCoreIn 2,Q.pCoreIn 2} ∧
      Stellmacher.elementaryAbelianMaxJ S = S ∧
      Nat.card (P.pCoreIn 2) = Nat.card F^3 ∧
      Nat.card (Q.pCoreIn 2) = Nat.card F^3 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF (by omega)).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.middle.toMonoidHom = unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.middle.toMonoidHom) e.middle.surjective) U)
  let a : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.middle.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  have hl (s : S) :
      (e.left ⟨s.val,(hSC.trans hCP) s.property⟩).val = (a s).val :=
    congrArg Subtype.val (e.left_commutes ⟨s.val,hSC s.property⟩)
  have hr (s : S) :
      (e.right ⟨s.val,(hSC.trans hCQ) s.property⟩).val = (a s).val :=
    congrArg Subtype.val (e.right_commutes ⟨s.val,hSC s.property⟩)
  have hcorel : (pCore 2 P).map (pointParabolic.subtype.comp e.left.toMonoidHom) =
      (wing false).map (unipotent (F := F)).subtype := by
    rw [←map_map,pCore_map_iso 2 e.left,
      pointParabolic_core_map_eq_radical hF hm]
    exact SymplecticConjugatePair.pointRadical_eq_wing
  have hcorer : (pCore 2 Q).map (planeParabolic.subtype.comp e.right.toMonoidHom) =
      (wing true).map (unipotent (F := F)).subtype := by
    rw [←map_map,pCore_map_iso 2 e.right,
      planeParabolic_core_map_eq_radical hF hm]
    exact SymplecticConjugatePair.planeRadical_eq_wing
  have hwl := wing_transport (hSC.trans hCP) a false _
    (pointParabolic.subtype_injective.comp e.left.injective) hl hcorel
  have hwr := wing_transport (hSC.trans hCQ) a true _
    (planeParabolic.subtype_injective.comp e.right.injective) hr hcorer
  have hw (i : Bool) :
      (wing i).map (S.subtype.comp a.symm.toMonoidHom) =
      ((wing i).comap a.toMonoidHom).map S.subtype := by
    rw [←map_map,map_equiv_eq_comap_symm']
    rfl
  have hpair := Stellmacher.maxFamily_pair_equiv S a.symm (wing false) (wing true)
    (SourceFusionOrder.native_max_elementary_pair (F := F))
  rw [hw,hw,hwl,hwr] at hpair
  refine ⟨hpair,?_,?_,?_⟩
  · have hj := Stellmacher.elementaryAbelianMaxJ_map_injective
      (S.subtype.comp a.symm.toMonoidHom) (S.subtype_injective.comp a.symm.injective) ⊤
    rw [elementaryAbelianMaxJ_top] at hj
    have htop : (⊤ : Subgroup (unipotent (F := F))).map
        (S.subtype.comp a.symm.toMonoidHom) = S := by
      rw [←map_map,map_top_of_surjective _ a.symm.surjective,
        ←MonoidHom.range_eq_map,range_subtype]
    rwa [htop] at hj
  · calc
      Nat.card (P.pCoreIn 2) = Nat.card ((wing false).map (S.subtype.comp a.symm.toMonoidHom)) :=
        congrArg (fun U : Subgroup G => Nat.card U) (hwl.symm.trans (hw false).symm)
      _ = Nat.card (wing (F := F) false) := card_map_of_injective (S.subtype_injective.comp a.symm.injective)
      _ = Nat.card F^3 := card_wing false
  · calc
      Nat.card (Q.pCoreIn 2) = Nat.card ((wing true).map (S.subtype.comp a.symm.toMonoidHom)) :=
        congrArg (fun U : Subgroup G => Nat.card U) (hwr.symm.trans (hw true).symm)
      _ = Nat.card (wing (F := F) true) := card_map_of_injective (S.subtype_injective.comp a.symm.injective)
      _ = Nat.card F^3 := card_wing true

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- The pure Sylow has exactly the two marked maximum elementary cores,
which generate it and have order q³. -/
theorem Preparation.symplectic_inner_max_elementary_pair :
    Stellmacher.elementaryAbelianMaxSubgroups (sourceS L H) =
      {(ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).pCoreIn 2,
       (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).pCoreIn 2} ∧
    Stellmacher.elementaryAbelianMaxJ (sourceS L H) = sourceS L H ∧
    ∀ i : Fin 2, Nat.card ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2) =
      Nat.card F^3 := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hf := d.hypothesisF11 h hH.1.1.2
  have hm' : 1 < m :=
    (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.symm ▸ h.exponent
  have hSC : sourceS L H ≤ C := le_inf (le_sup_right.trans le_sup_left)
    (le_sup_right.trans le_sup_left)
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · obtain ⟨hpair,hJ,hc0,hc1⟩ :=
      pair_max_elementary_geometry hF hm' inf_le_left inf_le_right hSC hs e
    refine ⟨hpair,hJ,?_⟩
    intro i
    fin_cases i
    · exact hc0
    · exact hc1
  · obtain ⟨hpair,hJ,hc1,hc0⟩ :=
      pair_max_elementary_geometry hF hm' inf_le_right inf_le_left hSC hs e.reverse
    refine ⟨?_,hJ,?_⟩
    · simpa only [Set.pair_comm] using hpair
    · intro i
      fin_cases i
      · exact hc0
      · exact hc1

/-- Outer field automorphisms do not create further maximum elementary
subgroups: the full original T has precisely the same two cores as S. -/
theorem Preparation.symplectic_max_elementary_sylow_pair :
    Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
      {(ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).pCoreIn 2,
       (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).pCoreIn 2} ∧
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) = sourceS L H := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let Q : Fin 2 → Subgroup G := fun i => (P i).pCoreIn 2
  obtain ⟨hpair,hJ,hcard⟩ := d.symplectic_inner_max_elementary_pair h hH hp F hm hF he
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hQT (i : Fin 2) : Q i ≤ (T : Subgroup G) :=
    ((d.hypothesisF11 h hH.1.1.2).parabolic_core_le_S i).trans hST
  have hQe (i : Fin 2) : IsElementaryAbelian 2 (Q i) :=
    (d.symplectic_sylow_wing_geometry h hH hp F hm hF he).2.1 i
  have hfamilies : Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
      Stellmacher.elementaryAbelianMaxSubgroups (sourceS L H) := by
    ext V
    constructor
    · intro hV
      let := hV.2.1
      have hc : Nat.card F^3 ≤ Nat.card V := by
        rw [←hcard 0]
        exact hV.2.2 (Q 0) (hQT 0) (hQe 0)
      exact ⟨d.symplectic_large_elementary_sylow_le_sourceS h hH hp F hm hF he V hV.1 hc,
        hV.2.1,fun B hB hBe => hV.2.2 B (hB.trans hST) hBe⟩
    · intro hV
      have hcV : Nat.card V = Nat.card F^3 := by
        have hh := hV
        rw [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hh
        rcases hh with rfl | rfl
        · exact hcard 0
        · exact hcard 1
      refine ⟨hV.1.trans hST,hV.2.1,?_⟩
      intro B hBT hBe
      let := hBe
      by_cases hb : Nat.card F^3 ≤ Nat.card B
      · exact hV.2.2 B
          (d.symplectic_large_elementary_sylow_le_sourceS h hH hp F hm hF he B hBT hb) hBe
      · rw [hcV]
        omega
  exact ⟨hfamilies.trans hpair,(congrArg sSup hfamilies).trans hJ⟩

/-- Both actual parabolic cores are weakly closed in the ambient Sylow.
The normalizer correction uses the literal whole common normalizer. -/
theorem Preparation.symplectic_parabolic_cores_weakly_closed
    (i : Fin 2) (g : G)
    (hg : ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2).map
      (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    g ∈ normalizer ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2 : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let Q : Fin 2 → Subgroup G := fun j => (P j).pCoreIn 2
  let M : Fin 2 → Subgroup G := fun j => normalizer (![L,residual H] j : Set G)
  let D := M 0 ⊓ M 1
  obtain ⟨hpair,hJ⟩ := d.symplectic_max_elementary_sylow_pair h hH hp F hm hF he
  have hSP := d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hS : sourceS L H = (T : Subgroup G) ⊓ L :=
    (inf_eq_left.mpr (hSP 0)).symm.trans d.left_intersection
  have hDN : D = normalizer (sourceS L H : Set G) := by
    rw [hS]
    exact (d.symplectic_normalizer_local_conditions h hH hp F hm hF he).normalizer_eq_middle.symm
  have hnQ (j : Fin 2) : normalizer (Q j : Set G) = M j := by
    have heq : (center (Q j)).map (Q j).subtype = Q j := by
      let := (d.symplectic_sylow_wing_geometry h hH hp F hm hF he).2.1 j
      rw [center_eq_top,←MonoidHom.range_eq_map,range_subtype]
    have hh := (d.symplectic_parabolic_core_center_normalizers h hH hp F hm hF he j).2
    change normalizer ((center (Q j)).map (Q j).subtype : Set G) = M j at hh
    rwa [heq] at hh
  have hDQ (j : Fin 2) : D ≤ normalizer (Q j : Set G) := by
    rw [hnQ j]
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  have hSD : sourceS L H ≤ D := by rw [hDN]; exact le_normalizer
  have hQi : Q i ∈ Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    rw [hpair]
    fin_cases i <;> simp [Q,P]
  have hQg : (Q i).map (MulAut.conj g).toMonoidHom ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    refine ⟨hg,hQi.2.1.map _,?_⟩
    intro U hUT hU
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hQi.2.2 U hUT hU
  have hSg : sourceS L H ≤ normalizer
      ((Q i).map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hQg
    rcases hQg with hh | hh
    · rw [hh]
      exact hSD.trans (hDQ 0)
    · rw [hh]
      exact hSD.trans (hDQ 1)
  have hw : ∀ x : G, (sourceS L H).map (MulAut.conj x).toMonoidHom ≤ (T : Subgroup G) →
      x ∈ normalizer (sourceS L H : Set G) := by
    rw [←hJ]
    exact Stellmacher.maxJ_weakly_closed_normalizer T
  obtain ⟨k,hk,heq⟩ := T.weakly_closed_normalizer_controls_set_fusion
    (sourceS L H) (sourceS_le_sylow h.sylow_normalizes hH.1.1.2) hw
    (Q i : Set G) ((Q i).map (MulAut.conj g).toMonoidHom : Set G)
    (hSD.trans (hDQ i)) hSg g rfl
  have hkQ := mem_normalizer_iff_conj_image_eq.mp (hDQ i (hDN.symm ▸ hk))
  exact mem_normalizer_iff_map_conj_eq.mpr (SetLike.coe_injective (heq.symm.trans hkQ))
/-- On the centralizer of either actual radical, its full normalizer controls
ambient element fusion. This is stronger than the needed center-only clause. -/
theorem Preparation.symplectic_core_centralizer_fusion
    (i : Fin 2) {x y : G}
    (hx : x ∈ centralizer ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2 : Set G))
    (hy : y ∈ centralizer ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2 : Set G))
    (hxy : IsConj x y) :
    ∃ g ∈ normalizer (![L,residual H] i : Set G), g*x*g⁻¹=y := by
  let Q := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) :=
    ((d.hypothesisF11 h hH.1.1.2).parabolic_core_le_S i).trans
      (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
  obtain ⟨g,hg,hgxy⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion Q hQT
    (d.symplectic_parabolic_cores_weakly_closed h hH hp F hm hF he i) hx hy hxy
  have hQ : (center Q).map Q.subtype = Q := by
    let := (d.symplectic_sylow_wing_geometry h hH hp F hm hF he).2.1 i
    rw [center_eq_top,←MonoidHom.range_eq_map,range_subtype]
  have hn := (d.symplectic_parabolic_core_center_normalizers h hH hp F hm hF he i).2
  change normalizer ((center Q).map Q.subtype : Set G) = _ at hn
  rw [hQ] at hn
  exact ⟨g,hn ▸ hg,hgxy⟩

/-- Each original full normalizer controls fusion of elements in Z(S),
without the transfer conclusion S=T. -/
theorem Preparation.symplectic_center_fusion_control
    (i : Fin 2) (x y : sourceS L H)
    (hx : x ∈ center (sourceS L H)) (hy : y ∈ center (sourceS L H))
    (hxy : IsConj x.val y.val) :
    ∃ g ∈ normalizer (![L,residual H] i : Set G), g*x.val*g⁻¹=y.val := by
  have hc (z : sourceS L H) (hz : z ∈ center (sourceS L H)) :
      z.val ∈ centralizer ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2 : Set G) := by
    intro q hq
    exact congrArg Subtype.val ((mem_center_iff.mp hz)
      ⟨q,(d.hypothesisF11 h hH.1.1.2).parabolic_core_le_S i hq⟩)
  exact d.symplectic_core_centralizer_fusion h hH hp F hm hF he i (hc x hx) (hc y hy) hxy

/-- Neither root-center type can fuse to a different type inside Z(S).
This supplies the root nonfusion inside Z(S) used in F.4.37 and F.4.39. -/
theorem Preparation.symplectic_root_center_nonfusion
    (i : Fin 2) (x y : sourceS L H)
    (hx : x ∈ center (sourceS L H)) (hy : y ∈ center (sourceS L H))
    (hxy : IsConj x.val y.val) :
    x.val ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ↔
      y.val ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype := by
  obtain ⟨g,hg,heq⟩ := d.symplectic_center_fusion_control h hH hp F hm hF he i x y hx hy hxy
  have hn := (d.symplectic_root_center_fusion h hH hp F hm hF he i).2.2
  have hgZ : g ∈ normalizer
      ((center (![L,residual H] i)).map (![L,residual H] i).subtype : Set G) := hn.symm ▸ hg
  have hz := hgZ x.val
  change (x.val ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ↔
    g*x.val*g⁻¹ ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype) at hz
  rwa [heq] at hz

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
