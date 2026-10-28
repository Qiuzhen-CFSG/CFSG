module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Parabolic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.ParabolicModel
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.GeneralizedFitting.TwoSimpleFactors

/-!
# The original overlap has the symmetric-three wreath quotient

The Hall-faithful conjugation action of H∩M on L₀/O₂(L₀) has a two-group
kernel. The original paired parabolic supplies the entire S₄² base of its
image. The source exchange element cannot induce an inner automorphism:
otherwise it would normalize the original C-component, by the solvable
quotient correspondence. Thus the image is the whole S₄ wreath product.
Removing its two-core gives the literal (H∩M)/O₂(H∩M) ≃ S₃ wr C₂.

The final export gives this quotient for the actual maximal subgroup of the
original minimal parabolic H. This is the input to the E.2.2 elimination in
10.2.3(3); it does not yet identify H/O₂(H), or H/C_H(U), with S₅ wr C₂.
Hall faithfulness remains the authorized input discharged by the parent
qt-d-10-fixed-hstar-parameter. No vanishing or later centralizer data is used.
Source: Aschbacher--Smith 10.2.3(3), printed p.745, applied in 10.3.1, p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan

private theorem kernel_two_of_hall {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (B : Subgroup X) (hB : IsHallSubgroup OddHall.oddPrimes B)
    (hi : Function.Injective (f.comp B.subtype)) : IsPGroup 2 f.ker := by
  have hd : B ⊓ f.ker = ⊥ := by
    apply bot_unique
    intro x hx
    have he : (⟨x,hx.1⟩ : B) = 1 := hi (by simpa using hx.2)
    exact congrArg Subtype.val he
  have hh := OddHall.hall_restrict_of_normalizes
    (D := B) (B := ⊤) (N := f.ker) (by
      constructor
      · intro p hp
        apply hB.p_in_pi_of_p_dvd_card p
        simpa only [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ ⊤ from le_top)).toEquiv] using hp
      · intro p hp
        apply hB.p_in_pi_of_p_dvd_index p
        change p.val ∣ B.relIndex ⊤ at hp
        simpa only [relIndex_top_right] using hp)
    le_top le_top (by rw [normalizer_eq_top]; exact le_top)
  have he : B.subgroupOf f.ker = ⊥ := by
    apply map_injective f.ker.subtype_injective
    rw [subgroupOf_map_subtype,hd,Subgroup.map_bot]
  rw [he] at hh
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p=2 := Classical.not_not.mp
    (hh.p_in_pi_of_p_dvd_index ⟨p,hpp⟩ (by simpa only [index_bot] using hpd))
  simpa only [hp2] using Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_refl 2,by decide⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem overlap_action_kernel_two
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsPGroup 2 (CentralHall.action D (D.maximalLocal.subgroupOf H) le_rfl).ker := by
  obtain ⟨hP,f,_,_,d,he,hperm,_⟩ := source_hstar_cartan_data_of_generation_gt_one D hH
    (by rw [s.generation H hH]; decide)
  have hb : d.witness.abelianGroup ≤ D.maximalLocal.subgroupOf H := he ▸ d.hall_le
  have hh := he ▸ d.hall
  have hi := CentralHall.action_injective D d.witness.abelianGroup hb
    (Bender.survivor_hall_faithful hfaith hmany s hH _ hb hh d.witness.abelian hperm)
  let P := D.maximalLocal.subgroupOf H
  let B := d.witness.abelianGroup.subgroupOf P
  apply kernel_two_of_hall _ B hh
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : d.witness.abelianGroup => (z : H)) (hi (a₁ := ⟨x.val.val,x.property⟩)
    (a₂ := ⟨y.val.val,y.property⟩) hxy)

private theorem marked_action_preserves
    {H : Subgroup G} (e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* ParabolicModel.Pair)
    (hp : (H.subgroupOf (localOrbit T L)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
        ParabolicModel.P.prod ParabolicModel.P)
    (g : D.maximalLocal.subgroupOf H) :
    (ParabolicModel.P.prod ParabolicModel.P).map
      ((MulAut.congr e (CentralHall.action D (D.maximalLocal.subgroupOf H) le_rfl g)).toMonoidHom) =
        ParabolicModel.P.prod ParabolicModel.P := by
  let R := localOrbit T L
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  let a := MulAut.congr e (CentralHall.action D (D.maximalLocal.subgroupOf H) le_rfl g)
  have hle : (ParabolicModel.P.prod ParabolicModel.P).map a.toMonoidHom ≤
      ParabolicModel.P.prod ParabolicModel.P := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←hp] at hx ⊢
    obtain ⟨r,hr,rfl⟩ := hx
    let gm : D.maximalLocal := ⟨g.val.val,g.property⟩
    let r' := R.normalizerMonoidHom gm r
    refine ⟨r',?_,?_⟩
    · exact (H.le_normalizer g.val.property r).mp hr
    · change e (QuotientGroup.mk' (pCore 2 R) r') =
        e ((CentralHall.action D (D.maximalLocal.subgroupOf H) le_rfl g)
          (e.symm (e (QuotientGroup.mk' (pCore 2 R) r))))
      rw [e.symm_apply_apply]
      change e (QuotientGroup.mk' (pCore 2 R) r') =
        e (quotientAut (pCore 2 R) (R.normalizerMonoidHom gm) (QuotientGroup.mk' (pCore 2 R) r))
      rw [quotientAut_apply_mk]
  exact eq_of_le_of_card_ge hle (le_of_eq (card_map_of_injective a.injective).symm)


private theorem simple_component_normal_in_pair
    {X : Type*} [Group X] [Finite X] [IsQuasisimple Matrix.PSL3Two.SL]
    (A : Subgroup X) (hA : A.IsCComponent)
    (eA : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.SL)
    (e : (X ⧸ pCore 2 X) ≃* ParabolicModel.Pair) : A.Normal := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  let a := (cComponentTwoCoreQuotientEquiv hA).symm.trans eA
  let : IsQuasisimple (A.map π) := IsQuasisimple.of_mulEquiv a.symm
  have hcomp : IsComponent (X ⧸ pCore 2 X) (A.map π) :=
    ⟨(hA.map_quotient _).subnormal,inferInstance⟩
  have hp := (hcomp.map_equiv e).prod_cases Matrix.PSL3Two.center_eq_bot
  have hn : ((A.map π).map e.toMonoidHom).Normal := by
    rcases hp with hp | hp <;> rw [hp]
    · exact ⟨by rintro _ ⟨x,rfl⟩ g; exact ⟨g.1*x*g.1⁻¹,by ext <;> simp⟩⟩
    · exact ⟨by rintro _ ⟨x,rfl⟩ g; exact ⟨g.2*x*g.2⁻¹,by ext <;> simp⟩⟩
  have hn' := hn.comap e.toMonoidHom
  rw [comap_map_eq_self (by rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]; exact bot_le)] at hn'
  exact cComponent_normal_of_quotient_normal hA (pCore 2 X) hn'

private theorem exchange_action_not_inner
    (s : SourceLinearThreeSurvivor T D)
    (e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* ParabolicModel.Pair) :
    ¬ ∃ z, normalizerPCoreQuotientAction (localOrbit T L)
        ⟨s.exchange,le_normalizer_componentOrbit L T s.exchange_mem⟩ = MulAut.conj z := by
  let R := localOrbit T L
  let A := L.subgroupOf R
  let π := QuotientGroup.mk' (pCore 2 R)
  have hLR : L ≤ R := le_componentOrbit L T
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  let a := subgroupOfEquivOfLe hLR
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans s.quotient
  let := D.quasisimple
  let : IsQuasisimple Matrix.PSL3Two.SL := IsQuasisimple.of_mulEquiv s.quotient
  let : A.Normal := simple_component_normal_in_pair A hA eA e
  let : (A.map π).Normal := (inferInstance : A.Normal).map π (QuotientGroup.mk'_surjective _)
  let gm : D.maximalLocal := ⟨s.exchange,le_normalizer_componentOrbit L T s.exchange_mem⟩
  let δ := R.normalizerMonoidHom gm
  rintro ⟨z,hz⟩
  have he : (A.map δ.toMonoidHom).map π = A.map π := by
    rw [map_map]
    have hc : π.comp δ.toMonoidHom = (MulAut.conj z).toMonoidHom.comp π := by
      ext x
      have hh := MulEquiv.congr_fun hz (π x)
      change quotientAut (pCore 2 R) δ (π x) = (MulAut.conj z) (π x) at hh
      rw [quotientAut_apply_mk] at hh
      exact hh
    rw [hc,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
  let : Group.IsNilpotent (pCore 2 R) := pCore_isPGroup.isNilpotent
  have hAe : A.map δ.toMonoidHom = A :=
    (hA.map_equiv δ).eq_of_map_quotient_eq hA (pCore 2 R) he
  apply s.exchange_moves
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hm := congrArg (map R.subtype) hAe
  rw [map_map,show R.subtype.comp δ.toMonoidHom =
    (MulAut.conj s.exchange).toMonoidHom.comp R.subtype from rfl,←map_map,
    map_subgroupOf_eq_of_le hLR] at hm
  exact hm


private theorem congr_conj {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply,MulAut.conj_apply]

/-- The exact two-core quotient of the original maximal-local overlap. -/
theorem overlap_twoCore_quotient
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Nonempty (((H ⊓ D.maximalLocal : Subgroup G) ⧸ pCore 2 (H ⊓ D.maximalLocal : Subgroup G)) ≃*
      WreathTwoResidual.Actor) := by
  obtain ⟨e,_,hp⟩ := orbit_overlap_parabolic D hfaith hmany s hH
  let R := localOrbit T L
  let P := D.maximalLocal.subgroupOf H
  let π := QuotientGroup.mk' (pCore 2 R)
  let q := e.toMonoidHom.comp π
  let a₀ := CentralHall.action D P le_rfl
  let a := (MulAut.congr e).toMonoidHom.comp a₀
  let := D.quasisimple
  let : IsQuasisimple Matrix.PSL3Two.SL := IsQuasisimple.of_mulEquiv s.quotient
  have ha (g : P) : a g ∈ ParabolicModel.actorHom.range :=
    ParabolicModel.preserving_pair_realization (a g) (marked_action_preserves D e hp g)
  let lift := MonoidHom.ofInjective ParabolicModel.actorHom_injective
  let f : P →* ParabolicModel.Actor := lift.symm.toMonoidHom.comp (a.codRestrict _ ha)
  have hf (g : P) : ParabolicModel.actorHom (f g) = a g :=
    congrArg Subtype.val (lift.apply_symm_apply (a.codRestrict _ ha g))
  have hker : f.ker = a₀.ker := by
    ext x
    change f x = 1 ↔ a₀ x = 1
    rw [←ParabolicModel.actorHom_injective.eq_iff, hf, map_one]
    exact (MulAut.congr e).map_eq_one_iff
  have hk : IsPGroup 2 f.ker := hker ▸ overlap_action_kernel_two D hfaith hmany s hH
  have hb (x : ParabolicModel.P × ParabolicModel.P) :
      WreathTwoElementaryRank.baseHom x ∈ f.range := by
    have hx : ((x.1 : Matrix.PSL3Two.SL),(x.2 : Matrix.PSL3Two.SL)) ∈
        (H.subgroupOf R).map q := hp.symm ▸ ⟨x.1.property,x.2.property⟩
    obtain ⟨r,hr,he⟩ := hx
    let g : P := ⟨⟨r,hr⟩,R.le_normalizer r.property⟩
    refine ⟨g,ParabolicModel.actorHom_injective ?_⟩
    rw [hf,ParabolicModel.actorHom_base]
    change MulAut.congr e (normalizerPCoreQuotientAction R
      (inclusion R.le_normalizer r)) = _
    rw [normalizerPCoreQuotientAction_inner,congr_conj]
    exact congrArg MulAut.conj he
  have ho : ∃ g : P, (f g).right ≠ 1 := by
    let t : P := ⟨⟨s.exchange,hH.1.1.2 s.exchange_mem⟩,
      le_normalizer_componentOrbit L T s.exchange_mem⟩
    refine ⟨t,fun ht => ?_⟩
    have hh := ParabolicModel.actorHom_inner_of_base (f t) ht
    rw [hf] at hh
    let z : ParabolicModel.Pair := ((f t).left 1,(f t).left WreathTwoElementaryRank.turn)
    apply exchange_action_not_inner D s e
    refine ⟨e.symm z,(MulAut.congr e).injective ?_⟩
    rw [congr_conj,e.apply_symm_apply]
    exact hh
  have honto := ParabolicModel.onto_of_base_outside f hb ho
  have heP : (H ⊓ D.maximalLocal).subgroupOf H = P := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  let ep : (H ⊓ D.maximalLocal : Subgroup G) ≃* P :=
    (subgroupOfEquivOfLe (show H ⊓ D.maximalLocal ≤ H from inf_le_left)).symm.trans
      (MulEquiv.subgroupCongr heP)
  exact ⟨(QuotientGroup.congr _ _ ep (pCore_map_iso 2 ep)).trans
    ((f.pCoreQuotientEquiv honto hk).trans ParabolicModel.quotientEquiv)⟩


/-- The recognition input is the actual maximal subgroup of the original
minimal parabolic, with its intrinsic two-core. -/
theorem hstar_maximal_twoCore_quotient
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Nonempty ((minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH) ⧸
      pCore 2 (minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH))) ≃*
        WreathTwoResidual.Actor) := by
  rw [source_hstar_parabolicMax_eq_overlap D hH]
  obtain ⟨e⟩ := overlap_twoCore_quotient D hfaith hmany s hH
  have he : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  let a : D.maximalLocal.subgroupOf H ≃* (H ⊓ D.maximalLocal : Subgroup G) :=
    (MulEquiv.subgroupCongr he.symm).trans
      (subgroupOfEquivOfLe (show H ⊓ D.maximalLocal ≤ H from inf_le_left))
  exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
