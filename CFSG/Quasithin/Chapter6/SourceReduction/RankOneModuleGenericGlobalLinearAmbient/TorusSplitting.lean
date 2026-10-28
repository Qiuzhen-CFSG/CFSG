module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CoreContainment
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.Transfer
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusSplitting
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# A marked Hall torus complement in the original linear Sylow

The whole-Borel comparison transports the full diagonal torus and the
unipotent radical to the original common Borel and S. The normal-Sylow
Frattini argument gives T = S N_T(D). The matrix torus-normalizer calculation
makes the intersection trivial, and the original quotient field action makes
N_T(D) cyclic. The original field, exponent, and both comparison orientations
are retained, including field four.

This constructs the actual complement used to mark an outer involution;
it does not assume a realization of the full normalizers or conclude ambient
recognition. Source: Aschbacher--Smith §5.3.2, §5.3.7 and F.4.29(2), printed
pp.659--661 and 289 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.LinearAmbientGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem source_common_borel_normalized
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) : Set G) := by
  have hTS := sylow_normalizes_sourceS hTL hTH
  have hb (K : Subgroup G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
      (T : Subgroup G) ≤ normalizer (ChapterF.Source.borel K (sourceS L H) : Set G) := by
    have hi := (le_inf hTS hTK).trans inf_normalizer_le_normalizer_inf
    exact (le_inf hTK (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf
    ((le_inf (hb L hTL) (hb (residual H) (hTH.trans (le_normalizer_residual H)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) hTS).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem Preparation.linear_cyclic_of_disjoint_sourceS
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n r : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    (he : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^r))
    (hUT : U ≤ (T : Subgroup G)) (hdis : Disjoint (sourceS L H) U) : IsCyclic U := by
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := he
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let : IsCyclic (E ≃+* E) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let f := (residualSylowFieldAction hTH e).comp (inclusion hUT)
  apply isCyclic_of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro u hu
  have hs : u.val ∈ sourceS L H := by
    have hk : inclusion hUT u ∈ (residualSylowFieldAction hTH e).ker := hu
    rw [d.residual_sylow_field_kernel h hTH hS e] at hk
    exact hk
  exact Subtype.ext (disjoint_def.mp hdis hs u.property)

private theorem Preparation.linear_torus_split_of_borel_equiv
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hq : 2 < Nat.card F)
    (heR : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^n))
    (a : ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ≃* borel F) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : C, b.val ∈ D ↔ (a b).val ∈ torus F) ∧
      Disjoint (sourceS L H) (normalizer (D : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (D : Set G) : Subgroup G) ∧
      (T : Set G) = (sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := by
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let hf := d.hypothesisF11 h hTH
  have hSC : sourceS L H ≤ C := le_sup_right
  have hCS : C ≤ normalizer (sourceS L H : Set G) := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    change C ≤ normalizer ((sourceS L H ⊓ L : Subgroup G) : Set G) at hh
    rwa [inf_eq_left.mpr (show sourceS L H ≤ L from hS 0)] at hh
  have hcore : C.pCoreIn 2 = sourceS L H := by
    obtain ⟨P,hP⟩ := hf.sylow_commonBorel
    apply le_antisymm ((pCoreIn_le_sylow C P).trans_eq hP)
    exact le_pCoreIn_of_normalizes hf.S_isP hSC hCS
  have hSR : ((sourceS L H).subgroupOf C).map a.toMonoidHom =
      (unipotent F).subgroupOf (borel F) := by
    rw [←BorelQuotient.twoCore_eq F hF,←pCore_map_iso 2 a]
    congr 1
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hcore.symm
  let D₀ := ((torus F).subgroupOf (borel F)).map a.symm.toMonoidHom
  let D := D₀.map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hD₀ : D.subgroupOf C = D₀ := comap_map_eq_self_of_injective C.subtype_injective _
  have hDa : (D.subgroupOf C).map a.toMonoidHom = (torus F).subgroupOf (borel F) := by
    rw [hD₀]
    have heq : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext a.apply_symm_apply
    rw [map_map,heq,map_id]
  have hHall : IsHallSubgroup oddPrimes (D.subgroupOf C) := by
    rw [hD₀]
    constructor
    · intro p hp
      apply (torus_oddHall F hF).p_in_pi_of_p_dvd_card p
      rwa [card_map_of_injective a.symm.injective] at hp
    · intro p hp
      apply (torus_oddHall F hF).p_in_pi_of_p_dvd_index p
      change p.val ∣ (((torus F).subgroupOf (borel F)).map a.symm.toMonoidHom).index at hp
      have hi := index_map_equiv (H := (torus F).subgroupOf (borel F)) a.symm
      exact hi ▸ hp
  have hdis : Disjoint (sourceS L H) (normalizer (D : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hn
    let y : C := ⟨x,hSC hx⟩
    have hy : a y ∈ (unipotent F).subgroupOf (borel F) :=
      hSR ▸ mem_map_of_mem a.toMonoidHom hx
    have hyn : y ∈ normalizer (D.subgroupOf C : Set C) := by
      rw [mem_normalizer_iff]
      intro z
      exact mem_normalizer_iff.mp hn z.val
    have han := (D.subgroupOf C).le_normalizer_map a.toMonoidHom
      (mem_map_of_mem a.toMonoidHom hyn)
    rw [hDa] at han
    have han' := ((torus F).subgroupOf (borel F)).le_normalizer_map
      (borel F).subtype (mem_map_of_mem _ han)
    rw [map_subgroupOf_eq_of_le (torus_le_borel F)] at han'
    have he : (a y).val=1 := unipotent_torus_normalizer_trivial F hF hq _ hy han'
    have hey : y=1 := a.injective ((Subtype.ext he).trans a.map_one.symm)
    exact congrArg Subtype.val hey
  refine ⟨D,hDC,hHall,?_,hdis,?_,?_⟩
  · intro b
    have hh : a b ∈ (torus F).subgroupOf (borel F) ↔ b ∈ D.subgroupOf C := by
      rw [←hDa]
      exact mem_map_iff_mem a.injective
    exact hh.symm
  · exact d.linear_cyclic_of_disjoint_sourceS h hTH hS heR
      inf_le_left (hdis.mono_right inf_le_right)
  · obtain ⟨P,hP⟩ := hf.sylow_commonBorel
    exact OddHall.normal_sylow_frattini C (sourceS L H) (T : Subgroup G) D
      hf.commonBorel_solvable (sourceS_le_sylow h.sylow_normalizes hTH)
      (source_common_borel_normalized h.sylow_normalizes hTH) P hP hDC hHall

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
include d h hH hp hm hF he

theorem Preparation.linear_source_sylow_torus_split :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      ((∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F),
        ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
          b.val ∈ D ↔ (e.middle b).val ∈ torus F) ∨
       (∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse,
        ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
          b.val ∈ D ↔ (e.middle b).val ∈ torus F)) ∧
      Disjoint (sourceS L H) (normalizer (D : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (D : Set G) : Subgroup G) ∧
      (T : Set G) = (sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := by
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  obtain ⟨_,_,_,_,_,_,heR,_⟩ := (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).2.2
  have hq : 2 < Nat.card F := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  have hf := d.hypothesisF11 h hH.1.1.2
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · let a := (MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf).symm).trans e.middle
    obtain ⟨D,hDC,hHall,hmark,hdis,hcyc,hsplit⟩ :=
      d.linear_torus_split_of_borel_equiv h hH.1.1.2 hs F hF hq heR a
    refine ⟨D,hDC,hHall,Or.inl ⟨e,?_⟩,hdis,hcyc,hsplit⟩
    intro b
    exact hmark ⟨b.val,(ChapterF.Source.lemma_F_1_3_6 hf).le b.property⟩
  · let a := (MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf).symm).trans e.middle
    obtain ⟨D,hDC,hHall,hmark,hdis,hcyc,hsplit⟩ :=
      d.linear_torus_split_of_borel_equiv h hH.1.1.2 hs F hF hq heR a
    refine ⟨D,hDC,hHall,Or.inr ⟨e,?_⟩,hdis,hcyc,hsplit⟩
    intro b
    exact hmark ⟨b.val,(ChapterF.Source.lemma_F_1_3_6 hf).le b.property⟩

omit [Finite G] d h hH hp [Field F] [Finite F] [CharP F 2] hm hF he in
/-- The complement has precisely the original Sylow/core index as its order. -/
private theorem torus_complement_card
    (S T D : Subgroup G) (hST : S ≤ T)
    (hdis : Disjoint S (normalizer (D : Set G)))
    (hsplit : (T : Set G) = (S : Set G) *
      (T ⊓ normalizer (D : Set G) : Set G)) :
    Nat.card (T ⊓ normalizer (D : Set G) : Subgroup G) = S.relIndex T := by
  let U := T ⊓ normalizer (D : Set G)
  have hc : IsComplement' (S.subgroupOf T) (U.subgroupOf T) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · apply disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (disjoint_def.mp hdis hx hy.2)
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      have hx : x.val ∈ (S : Set G) * (U : Set G) := hsplit ▸ x.property
      obtain ⟨s,hs,u,hu,he⟩ := hx
      exact ⟨⟨s,hST hs⟩,hs,⟨u,hu.1⟩,hu,Subtype.ext he⟩
  rw [←Nat.card_congr (subgroupOfEquivOfLe (show U ≤ T from inf_le_left)).toEquiv]
  exact hc.symm.index_eq_card.symm

/-- A proper source Sylow gives an actual outer involution normalizing the
same marked Hall torus. At field four this involution generates its complement. -/
theorem Preparation.linear_exists_outer_involution
    (hne : sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      ((∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F),
        ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
          b.val ∈ D ↔ (e.middle b).val ∈ torus F) ∨
       (∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse,
        ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
          b.val ∈ D ↔ (e.middle b).val ∈ torus F)) ∧
      Disjoint (sourceS L H) (normalizer (D : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (D : Set G) : Subgroup G) ∧
      Nat.card ((T : Subgroup G) ⊓ normalizer (D : Set G) : Subgroup G) =
        (sourceS L H).relIndex (T : Subgroup G) ∧
      (T : Set G) = (sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) ∧
      ∃ t : G, orderOf t = 2 ∧ t ∈ (T : Subgroup G) ∧
        t ∉ sourceS L H ∧ t ∈ normalizer (D : Set G) ∧
        (n = 2 → (T : Subgroup G) ⊓ normalizer (D : Set G) = zpowers t) := by
  obtain ⟨D,hDC,hHall,hmark,hdis,hcyc,hsplit⟩ :=
    d.linear_source_sylow_torus_split h hH hp F hm hF he
  let U := (T : Subgroup G) ⊓ normalizer (D : Set G)
  have hcard : Nat.card U = (sourceS L H).relIndex (T : Subgroup G) :=
    torus_complement_card _ _ _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2) hdis hsplit
  have hU : U ≠ ⊥ := by
    intro hu
    apply hne
    apply le_antisymm (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    apply relIndex_eq_one.mp
    rw [←hcard,hu,Nat.card_unique]
  let : Nontrivial U := U.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨k,hk⟩ := (T.isPGroup'.to_le (show U ≤ T from inf_le_left)).exists_card_eq
  have hkpos : 0<k := by
    have hh := Finite.one_lt_card (α := U)
    rw [hk] at hh
    by_contra hn
    have hz : k=0 := by omega
    simp [hz] at hh
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (hk ▸ dvd_pow_self 2 (by omega))
  have hu2 : orderOf u.val = 2 := (orderOf_coe u).trans hu
  have huS : u.val ∉ sourceS L H := by
    intro hs
    have hu1 : u.val=1 := disjoint_def.mp hdis hs u.property.2
    rw [hu1,orderOf_one] at hu2
    omega
  refine ⟨D,hDC,hHall,hmark,hdis,hcyc,hcard,hsplit,u.val,hu2,u.property.1,huS,u.property.2,?_⟩
  intro hn
  apply (eq_of_le_of_card_ge (zpowers_le.mpr u.property) ?_).symm
  rw [Nat.card_zpowers,hu2,hcard]
  have hd := d.linear_source_sylow_index_dvd h hH hp F hm hF he
  rw [hn] at hd
  exact Nat.le_of_dvd (by decide) hd

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
