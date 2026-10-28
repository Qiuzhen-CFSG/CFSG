module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleWhole
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2.ElementaryLift
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.ElementaryAbelian.Injective

/-!
# The natural single-factor obstruction to generation parameter one

A moving maximum elementary subgroup has an offender image on the original
module and on its natural quotient. That image fills a Sylow subgroup of the
normal SL₂ layer. This is an actual elementary lift in the original group,
so the rank-one quotient-lift obstruction applies without asserting that
E-generation descends through arbitrary quotients.

The genuine quasisimple E.2.3 row supplies the whole natural quotient and
its faithful ambient action. Perfectness excludes the field of order two.
Source: Aschbacher--Smith E.2.3, B.2.7 and 6.1.5, printed pp.216--217,
76 and 666--669.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

private theorem not_isEGenerated_one_of_semilinear_quotient
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] [Group.IsPerfect L]
    (F : BinaryField) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hF : 2 < Nat.card F.Carrier)
    (ρ : Representation (ZMod 2) H (Fin 2 → F.Carrier))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F.Carrier),
      ρ (g : H) v = Matrix.mulVec (e g).val v)
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hk g v) =
      ρ g (f v)) : ¬ IsEGenerated 1 G := by
  classical
  let α := NormalElementaryQuotient.representation U q hq hk
  have hex : ∃ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ := by
    by_contra! hn
    apply hJ
    rw [← hk]
    exact sSup_le fun B hB => (map_eq_bot_iff B).mp (hn B hB)
  obtain ⟨B, hB, hne⟩ := hex
  let : IsElementaryAbelian 2 B := hB.2.1
  have hb : IsOffender α (B.map q) :=
    ((lemma_B_2_7_local U q hq hk T hUT (hk ▸ hJ)).2
      (B.map q) ⟨B, hB, rfl, hne⟩).isOffender α
  have hbρ : IsOffender ρ (B.map q) := ⟨hb.1,
    (fixedCodim_le_of_equivariant_surjection α ρ f hf he _).trans hb.2⟩
  obtain ⟨P, hP⟩ := SL2NaturalOffenders.exists_sylow hF L e ρ hfaith hnat hbρ
  have hd : 1 < F.degree := by
    have hp := F.degree_pos
    by_contra hn
    have hdeg : F.degree = 1 := by omega
    have hh : 2 < 2 := by simpa only [F.card_eq, hdeg, pow_one] using hF
    exact (Nat.lt_irrefl 2) hh
  have hlarge : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
  let ep : L ≃* BenderSuzuki.Converse.PSL2 F.Carrier := e.trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F.Carrier)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩)
  let : IsSimpleGroup (BenderSuzuki.Converse.PSL2 F.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup L := ep.isSimpleGroup
  let Q := P.mapSurjective (f := ep.toMonoidHom) ep.surjective
  have hQP : (Q : Subgroup _).map ep.symm.toMonoidHom = (P : Subgroup L) := by
    change ((P : Subgroup L).map ep.toMonoidHom).map ep.symm.toMonoidHom = _
    rw [map_map]
    simp
  have hfacts : ChapterF.Source.RankOneSylowFacts P :=
    ChapterF.Source.Linear.transport ep.symm Q P hQP
      (ChapterF.Source.Linear.projective_facts F.Carrier F.degree F.degree_pos F.card_eq Q)
  have hPc : Nat.card P = 2 ^ F.degree :=
    (SL2NaturalOffenders.sylow_card L e P).trans F.card_eq
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 ((P : Subgroup L).map L.subtype) := hP.symm ▸ inferInstance
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective
    ((P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom
    ((P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).injective
  exact ValuesEvenClassical.not_isEGenerated_of_rankOne_quotient_lift q hq L
    (Group.IsPerfect.not_isSolvable L) P
    (fun D hPD hD => hfacts.unique_maximal D hPD (lt_top_iff_ne_top.mpr hD))
    hfacts.proper.ne B hP.symm 1
    (hd.trans_le (IsElementaryAbelian.rank_ge_of_card (p := 2) hPc))

/-- The genuine single natural SL₂ row of E.2.3 excludes rank-one E-generation
in the original group, using an elementary Sylow lift supplied by B.2.7. -/
theorem quasisimple_linear_not_isEGenerated_one
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))).subtype) F 2) :
    ¬ IsEGenerated 1 G := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
  have hcore : pCore 2 H = ⊥ := by
    let c := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 c, hU.quotient_pCore_eq_bot, Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := (lemma_B_2_7_local U q hq hk T
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) (hk ▸ hJ)).1
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  let σ := α.comp Y.subtype
  obtain ⟨_, _, _, ⟨eV⟩⟩ :=
    quasisimple_linear_whole_source T hP U hU hJ q hq hk hqs s F ⟨e⟩
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  let ea := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := ea.toMonoidHom) ea.surjective
  have hself : centralizer (L : Set H) ≤ L := by
    change centralizer (A.map Y.subtype : Set H) ≤ A.map Y.subtype
    rw [hL]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  let f := eV.linearEquiv.toLinearMap.comp (fixedSpace σ A).mkQ
  have hf : Function.Surjective f := eV.linearEquiv.surjective.comp (fixedSpace σ A).mkQ_surjective
  have hkf : f.ker = fixedSpace α L := by
    ext v
    change eV.linearEquiv ((fixedSpace σ A).mkQ v) = 0 ↔ _
    rw [← eV.linearEquiv.map_zero, eV.linearEquiv.injective.eq_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [fixedSpace_comp_map]
  let eg := ea.symm.trans eV.groupEquiv
  let τ := (SL2NaturalOffenders.NoStrong.natural (F := F.Carrier)).comp eg.toMonoidHom
  have hτ : Function.Injective τ := by
    intro a b hab
    apply eg.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  have hef (g : L) v : f (α (g : H) v) = τ g (f v) := by
    let a := ea.symm g
    have ha : ((a : Y) : H) = (g : H) := congrArg Subtype.val (ea.apply_symm_apply g)
    have hh := eV.intertwines a ((fixedSpace σ A).mkQ v)
    change f (α ((a : Y) : H) v) = _ at hh
    rw [ha] at hh
    exact hh
  obtain ⟨ρ, hρ, heρ, hnat⟩ :=
    exists_faithful_action_of_normal_layer_quotient α L hself τ hτ f hf hkf hef
  exact not_isEGenerated_one_of_semilinear_quotient T U q hq hk
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hJ L F eg hF
    ρ hρ (fun g v => hnat g v) f hf heρ

end CFSG.Quasithin.ChapterE.ThompsonAction
