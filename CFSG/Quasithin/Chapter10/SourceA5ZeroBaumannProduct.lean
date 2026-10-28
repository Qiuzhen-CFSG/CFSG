module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroSecondCentralizerImage
public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannPairFactor
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairMarkedIntersection
public import Theory.GroupTheory.QuotientPairDirectProduct

/-!
# The original zero-center Baumann subgroup is a four-dihedral product

The two centralizers of the chosen commuting original blocks map onto the
opposite coordinates of the marked Baumann quotient. The split two-core lies
in their join, so their quotient generation lifts to the whole Baumann
subgroup. The trivial joint centralizer makes the factors disjoint; their
normalizer control makes them commute. Conjugation by the selected Sylow
element transports the known dihedral-square recognition between the two
factors. The internal product retains its multiplication formula.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

/-- The two original block centralizers give a marked internal direct product. -/
theorem source_a5_zero_baumann_centralizer_product
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    let R := ChapterB.baumann (S : Subgroup H)
    let A := L.subgroupOf H
    ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧
      let B := A.map (MulAut.conj t).toMonoidHom
      A ≠ B ∧ ∃ f : ((R ⊓ centralizer (A : Set H) : Subgroup H) ×
        (R ⊓ centralizer (B : Set H) : Subgroup H)) ≃* R,
        ∀ a b, (f (a,b) : H) = (a : H) * (b : H) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let R := ChapterB.baumann (S : Subgroup H)
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint,d,c,hcid,hex,hN,haxes⟩ :=
    source_a5_zero_centralizer_marked_pair_both_axes D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  obtain ⟨_,a,b,hab⟩ := paired_thompson_baumann_of_symmetric_model S
    (source_a5_minimal_parabolic D e hn) U hU
    (source_local_thompson_not_centralizes D hout) q hq hk d c hex
  let F₁ := (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom
  let F₂ := (ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  let F := (F₁.prod F₂).map j
  have hRF : R.map q = F := hab
  have hcore : q.ker = pCore 2 H := hk.trans
    (source_a5_zero_centralizer_paired_action D e hn hout hz).2
  have hcoreR : q.ker ≤ R := hcore ▸ source_a5_zero_core_le_baumann D e hn hout hz
  have hR : R = F.comap q := by
    rw [←hRF, comap_map_eq_self hcoreR]
  have hFY : F ≤ Y := by
    rintro _ ⟨v,hv,rfl⟩
    exact (c.action.groupEquiv.symm v).property
  have hRY : R ≤ Y.comap q := by
    rw [hR]
    exact comap_mono hFY
  have hrestrict (E : Subgroup H) :
      (R ⊓ centralizer (E : Set H)).map q =
        F ⊓ (Y.comap q ⊓ centralizer (E : Set H)).map q := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨by simpa [hR] using hr.1, ⟨r,⟨hRY hr.1,hr.2⟩,rfl⟩⟩
    · rintro ⟨hxF,r,hr,rfl⟩
      exact ⟨r,⟨by simpa [hR] using hxF,hr.2⟩,rfl⟩
  let C₁ := R ⊓ centralizer (A : Set H)
  let C₂ := R ⊓ centralizer (B : Set H)
  have hcoords : (F₁.prod (⊥ : Subgroup (Equiv.Perm (Fin 5)))) ⊔
      ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod F₂) = F₁.prod F₂ := by
    apply le_antisymm
    · exact sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl)
    · intro x hx
      have h1 : (x.1,1) ∈ F₁.prod (⊥ : Subgroup (Equiv.Perm (Fin 5))) := ⟨hx.1,by simp⟩
      have h2 : (1,x.2) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod F₂ := ⟨by simp,hx.2⟩
      simpa using (F₁.prod (⊥ : Subgroup (Equiv.Perm (Fin 5))) ⊔
        ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod F₂)).mul_mem
          ((show F₁.prod (⊥ : Subgroup (Equiv.Perm (Fin 5))) ≤ _ from le_sup_left) h1)
          ((show (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod F₂ ≤ _ from le_sup_right) h2)
  have hmaps : (C₁ ⊔ C₂).map q = R.map q := by
    rw [Subgroup.map_sup, hRF]
    change (R ⊓ centralizer (A : Set H)).map q ⊔
      (R ⊓ centralizer (B : Set H)).map q = F
    rw [hrestrict, hrestrict]
    rcases haxes with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · rw [hA,hB]
      change (F₁.prod F₂).map j ⊓ d.second.map Y.subtype ⊔
        ((F₁.prod F₂).map j ⊓ d.first.map Y.subtype) = F
      rw [c.map_subtype_inf_second Y.subtype Y.subtype_injective,
        c.map_subtype_inf_first Y.subtype Y.subtype_injective, ←Subgroup.map_sup,
        sup_comm, hcoords]
    · rw [hA,hB]
      change (F₁.prod F₂).map j ⊓ d.first.map Y.subtype ⊔
        ((F₁.prod F₂).map j ⊓ d.second.map Y.subtype) = F
      rw [c.map_subtype_inf_first Y.subtype Y.subtype_injective,
        c.map_subtype_inf_second Y.subtype Y.subtype_injective, ←Subgroup.map_sup, hcoords]
  have hkerJoin : q.ker ≤ C₁ ⊔ C₂ := by
    rw [hcore,hsplit]
    apply sup_le
    · apply le_trans _ le_sup_right
      rw [←hkA]
      exact le_inf (inf_le_left.trans (hcore ▸ hcoreR)) inf_le_right
    · apply le_trans _ le_sup_left
      rw [←hkB]
      exact le_inf (inf_le_left.trans (hcore ▸ hcoreR)) inf_le_right
  have hgen : C₁ ⊔ C₂ = R := by
    have hh := congrArg (fun P : Subgroup (H ⧸ C) => P.comap q) hmaps
    simpa only [comap_map_eq_self hkerJoin, comap_map_eq_self hcoreR] using hh
  have hRA : R ≤ normalizer (A : Set H) := hRY.trans hN
  have htS : t ∈ (S : Subgroup H) := ht
  have hRmap : R.map (MulAut.conj t).toMonoidHom = R := by
    apply mem_normalizer_iff_map_conj_eq.mp
    exact (normalizer_le_normalizer_baumann (S : Subgroup H))
      ((S : Subgroup H).le_normalizer htS)
  have hRB : R ≤ normalizer (B : Set H) := by
    have hm := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hRA
    rw [map_equiv_normalizer_eq A (MulAut.conj t),hRmap] at hm
    exact hm
  have hdisj : Disjoint C₁ C₂ :=
    (disjoint_of_pair_centralizer_layers A B C₂ C₁ inf_le_right inf_le_right hjoint).symm
  have hcommute : C₁ ≤ centralizer (C₂ : Set H) :=
    le_centralizer_iff.mp (inf_centralizer_pair_commutes R A B hRA hRB hjoint)
  obtain ⟨f,hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C₁ C₂ hdisj hcommute
  exact ⟨t,ht,hne,f.trans (MulEquiv.subgroupCongr hgen),hf⟩


/-- The local Baumann subgroup in the zero-center branch is a product of four
order-eight dihedral groups. -/
theorem source_a5_zero_baumann_dihedral_four_product
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    Nonempty (ChapterB.baumann (S : Subgroup H) ≃*
      (DihedralGroup 4 × DihedralGroup 4) × (DihedralGroup 4 × DihedralGroup 4)) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let R := ChapterB.baumann (S : Subgroup H)
  let A := L.subgroupOf H
  obtain ⟨t,ht,_,f,_⟩ := source_a5_zero_baumann_centralizer_product D e hn hout hz
  obtain ⟨eA⟩ := source_a5_zero_baumann_factor_dihedral_square D e hn hout hz
  have htS : t ∈ (S : Subgroup H) := ht
  have hRmap : R.map (MulAut.conj t).toMonoidHom = R := by
    apply mem_normalizer_iff_map_conj_eq.mp
    exact (normalizer_le_normalizer_baumann (S : Subgroup H))
      ((S : Subgroup H).le_normalizer htS)
  let B := A.map (MulAut.conj t).toMonoidHom
  have hmap : (R ⊓ centralizer (A : Set H)).map (MulAut.conj t).toMonoidHom =
      R ⊓ centralizer (B : Set H) :=
    inf_centralizer_conjugate_of_map_eq R A t hRmap
  let eB : (R ⊓ centralizer (B : Set H) : Subgroup H) ≃*
      DihedralGroup 4 × DihedralGroup 4 :=
    (MulEquiv.subgroupCongr hmap.symm).trans
      (((MulAut.conj t).subgroupMap (R ⊓ centralizer (A : Set H))).symm.trans eA)
  exact ⟨f.symm.trans (eA.prodCongr eB)⟩

/-- The same four-dihedral recognition for the original ambient Sylow subgroup. -/
theorem source_a5_zero_original_baumann_dihedral_four_product
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    Nonempty (ChapterB.baumann (T : Subgroup G) ≃*
      (DihedralGroup 4 × DihedralGroup 4) × (DihedralGroup 4 × DihedralGroup 4)) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let R := ChapterB.baumann (S : Subgroup H)
  obtain ⟨eR⟩ := source_a5_zero_baumann_dihedral_four_product D e hn hout hz
  have hmap : R.map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change R.map H.subtype = ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
    exact he.trans (congrArg ChapterB.baumann (map_subgroupOf_eq_of_le le_sup_right))
  let f : R ≃* ChapterB.baumann (T : Subgroup G) :=
    (R.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨f.symm.trans eR⟩

end CFSG.Quasithin.Chapter10
