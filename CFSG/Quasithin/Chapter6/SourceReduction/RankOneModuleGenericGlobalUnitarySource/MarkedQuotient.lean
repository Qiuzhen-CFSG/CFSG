module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourShortMarked
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortOrbit
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortAction
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortFusion

/-!
# The same marked roots in the ambient short-line quotient

The reduced amalgam supplies a single plane-residual isomorphism retaining
both root marks. Transport the native orthogonal module and its complete
fixed line through this map. The long root is in the original right
residual center, so the proved ambient common-centralizer bound applies
to this very marker. The literal line-normalizer quotient keeps the entire
line as its kernel, kills the short root, and retains the long root.
The existing Burnside correction controls simultaneous quotient fusion.

This joins the common-centralizer and quotient-orbit inputs of
Aschbacher–Smith F.4.42, printed pp.295–296 of `refs/quasithin.pdf`.
Ambient unique fixed cosets, full short-centralizer containment and the
subsequent order comparison still require their source arguments.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}
omit [Finite G] in
private theorem short_quotient_from_marked_equiv
    (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    (f : localFactor (MatrixField m) (form (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)) ≃* L) :
    let t := f (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
    orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L),
      z.val = f (SourceNormalizer.FourShortRoot.longMark
        (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).val ∧
      orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      U ≤ V ∧ U ≤ center (centralizer ({t} : Set L)) ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∀ {J : Type u} [Group J] (f : centralizer ({t} : Set L) →* J),
        U ≤ f.ker → ∀ v ∈ V.map f, v ≠ 1 →
          ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
            f a * f z * (f a)⁻¹ = v) ∧
      V.map (centralizer ({t} : Set L)).subtype =
        ⁅pCore 2 L,centralizer ({t} : Set L)⁆ ∧
      (∀ {J : Type u} [Group J] (f : centralizer ({t} : Set L) →* J),
        U ≤ f.ker → ∃ P : Subgroup J, Group.IsPerfect P ∧ P ≤ f.range ∧
          ∀ v ∈ V.map f, v ≠ 1 → ∃ a ∈ P, a * f z * a⁻¹ = v) ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∃ P : Sylow 2 (centralizer ({t} : Set L)),
        (P : Subgroup _) ≤ centralizer ({z} : Set _)) ∧
      (∀ {J : Type u} [Group J] (f : centralizer ({t} : Set L) →* J),
        f.ker = U → ∀ v ∈ V.map f, v ≠ 1 →
          ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      U = V ⊓ center (centralizer ({t} : Set L)) := by
  let F := MatrixField m
  let σ := fieldConj m
  let hσ := fieldConj_involutive m hm
  let B := localFactor F (form F σ hσ)
  let X := shortCentralizer F σ hσ
  let f : B ≃* L := f
  let t := f (shortLocal F σ hσ)
  let Y := centralizer ({t} : Set L)
  let a : X ≃* Y := (f.subgroupMap X).trans
    (MulEquiv.subgroupCongr (CentralizerSmallKernelTransport.map_centralizer f (shortLocal F σ hσ)))
  let V₀ := (orthogonalRadical F σ hσ).subgroupOf X
  let U₀ := (SourceNormalizer.FourShortRoot.shortLine F σ hσ).subgroupOf X
  let V := V₀.map a.toMonoidHom
  let U := U₀.map a.toMonoidHom
  let z := a (SourceNormalizer.FourShortRoot.longMark F σ hσ)
  have hV : V = normalClosure ({z} : Set Y) := by
    dsimp only [V,V₀]
    rw [←SourceNormalizer.FourShortRoot.long_normalClosure F σ hσ,
      map_normalClosure _ _ a.surjective,Set.image_singleton]
    rfl
  have ht : orderOf t = 2 :=
    (f.orderOf_eq _).trans ((orderOf_coe (SourceNormalizer.FourShortRoot.shortMark F σ hσ)).trans
      (SourceNormalizer.FourShortRoot.shortMark_order F σ hσ))
  refine ⟨(orderOf_coe t).trans ht,z,rfl,
    (orderOf_coe z.val).trans ((orderOf_coe z).trans ((a.orderOf_eq _).trans
      (SourceNormalizer.FourShortRoot.longMark_order F σ hσ))),U,?_⟩
  change IsElementaryAbelian 2 (normalClosure ({z} : Set Y)) ∧ _
  rw [←hV]
  let j : V₀ →* radical F σ hσ := (X.subtype.comp V₀.subtype).codRestrict _
    (fun x => orthogonalRadical_le_radical F σ hσ x.property)
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : radical F σ hσ => q.val) he
  let : IsElementaryAbelian 2 V₀ := IsElementaryAbelian.of_injective j hj
  have hVU : U₀ ≤ V₀ := fun x hx => SourceNormalizer.FourShortRoot.shortLine_le_orthogonal F σ hσ hx
  have hUV : U ≤ V := map_mono hVU
  have hUC : U ≤ center Y := by
    rintro y ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro b
    obtain ⟨c,rfl⟩ := a.surjective b
    exact (a.map_mul c x).symm.trans
      ((congrArg a (mem_center_iff.mp (SourceNormalizer.FourShortRoot.shortLine_le_center F σ hσ hx) c)).trans
        (a.map_mul x c))
  have hq : Nat.card (FixedBy.subfield F σ) = 2^m := PointLocal.fixedField_card m hm
  have hVc : Nat.card V = (2^m)^3 := by
    rw [card_map_of_injective a.injective]
    change Nat.card ((orthogonalRadical F σ hσ).subgroupOf X) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe (orthogonalRadical_le_shortCentralizer F σ hσ)).toEquiv,
      orthogonalRadical_card,hq]
  have hUc : Nat.card U = 2^m := by
    rw [card_map_of_injective a.injective]
    change Nat.card ((SourceNormalizer.FourShortRoot.shortLine F σ hσ).subgroupOf X) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe ((SourceNormalizer.FourShortRoot.shortLine_le_orthogonal F σ hσ).trans
      (orthogonalRadical_le_shortCentralizer F σ hσ))).toEquiv,
      SourceNormalizer.FourShortRoot.shortLine_card,hq]
  have hindex : U.relIndex V = (2^m)^2 := by
    have hi := (U.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv,hUc,hVc] at hi
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^m)
    exact hi.trans (by ring)
  have htmem : (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Y) ∈ U :=
    mem_map_of_mem a.toMonoidHom (SourceNormalizer.FourShortRoot.shortMark_mem_line F σ hσ)
  have htU : zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Y) < U := by
    apply lt_of_le_of_ne (zpowers_le.mpr htmem)
    intro he
    have hh := congrArg (fun D : Subgroup Y => Nat.card D) he
    have ho : orderOf (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Y) = 2 :=
      (orderOf_coe _).symm.trans ht
    rw [Nat.card_zpowers,ho,hUc] at hh
    have hlarge : 2 < 2^m := Nat.pow_lt_pow_right (by decide : 1 < 2) hm'
    omega
  have hVQ : (V.map Y.subtype).map L.subtype ≤ L.pCoreIn 2 := by
    rintro x ⟨y,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩
    apply mem_map_of_mem L.subtype
    have hwQ : w.val ∈ pCore 2 B := by
      rw [←radical_eq_twoCore F σ hσ]
      exact orthogonalRadical_le_radical F σ hσ hw
    exact (pCore_map_iso 2 f).le (mem_map_of_mem f.toMonoidHom hwQ)
  refine ⟨IsElementaryAbelian.map a.toMonoidHom,hVQ,hVc,hUc,hindex,hUV,hUC,htU,?_,?_,?_,?_,?_,?_,?_⟩
  · intro J _ g hUg v hv hv1
    have hker : U₀ ≤ (g.comp a.toMonoidHom).ker := by
      intro x hx
      exact hUg (mem_map_of_mem a.toMonoidHom hx)
    have hv' : v ∈ V₀.map (g.comp a.toMonoidHom) := by
      rw [←Subgroup.map_map]
      exact hv
    obtain ⟨b,hb,he⟩ := SourceNormalizer.FourShortRoot.orthogonal_image_residual_fusion
      F σ hσ (g.comp a.toMonoidHom) hker hv' hv1
    exact ⟨a b,(map_primeToResidual a).le (mem_map_of_mem a.toMonoidHom hb),he⟩
  · have hmaps : (V₀.map a.toMonoidHom).map Y.subtype =
        (V₀.map X.subtype).map f.toMonoidHom := by
      rw [map_map,map_map]
      congr 1
    change (V₀.map a.toMonoidHom).map Y.subtype = _
    rw [hmaps,map_subgroupOf_eq_of_le (orthogonalRadical_le_shortCentralizer F σ hσ),
      SourceNormalizer.FourShortRoot.orthogonal_eq_commutator F σ hσ (by
        rw [hq]
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) hm'),
      map_commutator,radical_eq_twoCore,pCore_map_iso]
    change ⁅pCore 2 L,(centralizer ({shortLocal F σ hσ} : Set B)).map f.toMonoidHom⁆ = _
    rw [CentralizerSmallKernelTransport.map_centralizer]
  · intro J _ g hUg
    have hker : U₀ ≤ (g.comp a.toMonoidHom).ker := by
      intro x hx
      exact hUg (mem_map_of_mem a.toMonoidHom hx)
    have hq4 : 3 < Nat.card (FixedBy.subfield F σ) := by
      rw [hq]
      have hh : 2^2 ≤ 2^m := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨P,hP,hPr,horbit⟩ := SourceNormalizer.FourShortRoot.orthogonal_image_perfect_orbit
      F σ hσ hq4 (g.comp a.toMonoidHom) hker
    refine ⟨P,hP,?_,?_⟩
    · rintro x hx
      obtain ⟨b,rfl⟩ := hPr hx
      exact ⟨a b,rfl⟩
    · intro v hv hv1
      apply horbit v _ hv1
      rwa [←map_map]

  · let b : {x : X // IsConj (SourceNormalizer.FourShortRoot.longMark F σ hσ) x} ≃
        {x : Y // IsConj z x} := Equiv.subtypeEquiv a.toEquiv (fun x => by
      constructor
      · exact a.toMonoidHom.map_isConj
      · intro hx
        have hh := a.symm.toMonoidHom.map_isConj hx
        change IsConj (a.symm (a (SourceNormalizer.FourShortRoot.longMark F σ hσ)))
          (a.symm (a x)) at hh
        simpa only [a.symm_apply_apply] using hh)
    rw [←Nat.card_congr b,SourceNormalizer.FourShortRoot.longClass_card,hq]
  · obtain ⟨P,hP⟩ := SourceNormalizer.FourShortRoot.exists_long_centralizing_sylow F σ hσ
    refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (a.map_mul _ _).symm.trans
      ((congrArg a (mem_centralizer_singleton_iff.mp (hP hx))).trans (a.map_mul _ _))
  · intro J _ g hg v hv hv1
    have hker : (g.comp a.toMonoidHom).ker = U₀ := by
      ext x
      change g (a x) = 1 ↔ x ∈ U₀
      rw [←MonoidHom.mem_ker,hg]
      constructor
      · rintro ⟨w,hw,he⟩
        exact a.injective he ▸ hw
      · exact mem_map_of_mem a.toMonoidHom
    have hv' : v ∈ V₀.map (g.comp a.toMonoidHom) := by
      rwa [←map_map]
    obtain ⟨x,hx,hunique⟩ := SourceNormalizer.FourShortRoot.existsUnique_long_lift
      F σ hσ (g.comp a.toMonoidHom) hker hv' hv1
    refine ⟨a x,⟨a.toMonoidHom.map_isConj hx.1,hx.2⟩,?_⟩
    intro y hy
    have hy' : IsConj (SourceNormalizer.FourShortRoot.longMark F σ hσ) (a.symm y) := by
      have hh := a.symm.toMonoidHom.map_isConj hy.1
      change IsConj (a.symm (a (SourceNormalizer.FourShortRoot.longMark F σ hσ)))
        (a.symm y) at hh
      simpa only [a.symm_apply_apply] using hh
    have he := hunique (a.symm y) ⟨hy',by
      change g (a (a.symm y)) = v
      rw [a.apply_symm_apply]
      exact hy.2⟩
    exact (a.apply_symm_apply y).symm.trans (congrArg a he)
  · have hline : U₀ = V₀ ⊓ center X := by
      ext x
      change x.val ∈ SourceNormalizer.FourShortRoot.shortLine F σ hσ ↔ _
      rw [SourceNormalizer.FourShortRoot.shortLine_eq_orthogonal_inf_centralizer]
      constructor
      · rintro ⟨hx,hc⟩
        exact ⟨hx,mem_center_iff.mpr (fun y => Subtype.ext (hc y.val y.property))⟩
      · rintro ⟨hx,hc⟩
        exact ⟨hx,fun y hy => congrArg Subtype.val (mem_center_iff.mp hc ⟨y,hy⟩)⟩
    change U₀.map a.toMonoidHom = V₀.map a.toMonoidHom ⊓ center Y
    rw [hline,map_inf _ _ _ a.injective,center_map_equiv]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The common-centralizer and quotient-orbit arguments use the very same
short root, long root and full short-root line from the reduced comparison. -/
theorem Preparation.unitary_marked_short_quotient_with_line
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ (∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v) ∧
      ∀ (s : Set (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)),
        s ⊆ V.map f →
        ∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
          (∀ x ∈ s, g*x*g⁻¹ ∈ V.map f) →
          ∃ a : UnitarySource.shortLineNormalizer L t U,
            a.val.val ∈ normalizer (L : Set G) ∧ ∀ x ∈ s,
              QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a * x *
                (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a)⁻¹ = g*x*g⁻¹ := by
  obtain ⟨hm',hn,e,_,_,_,hcommon⟩ :=
    d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,hfusion,_,_,_⟩ :=
    short_quotient_from_marked_equiv m hm hm' a
  have hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype := by
    rw [hzmark]
    exact haz
  have hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
      normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon z.val.val hzc hz
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card (V.map f) = (2^m)^2 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have hfusion := hfusion f hker.ge
  have hzne : f z ≠ 1 := by
    let : Nontrivial (V.map f) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcV]
      exact Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide)))
    obtain ⟨v,hv⟩ := exists_ne (1 : V.map f)
    have hvne : v.val ≠ 1 := fun he => hv (Subtype.ext he)
    obtain ⟨a,ha,he⟩ := hfusion v.val v.property hvne
    intro hzero
    rw [hzero,mul_one,mul_inv_cancel] at he
    exact hvne he.symm
  have htkill : f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 :=
    MonoidHom.mem_ker.mp (hker.ge (htU.le (mem_zpowers _)))
  refine ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hUV,hV,hVQ,hVc,hUc,hker,
    IsElementaryAbelian.map f,hcV,htU,htkill,hzne,hfusion,?_⟩
  have hUQ : ∀ u ∈ U, u.val.val ∈ L.pCoreIn 2 := by
    intro u hu
    exact hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype (hUV hu)))
  have htQ : t.val ∈ L.pCoreIn 2 := hUQ _ (htU.le (mem_zpowers _))
  have hmap : V.map f ≤
      ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) := by
    rintro v ⟨w,hw,rfl⟩
    refine ⟨UnitarySource.shortLineNormalizerMap L t U hU w,?_,rfl⟩
    exact hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype hw))
  intro s hs g hgs
  exact d.unitary_short_line_quotient_set_fusion h hH hp m hm hc t htQ U hUQ s
    (hs.trans hmap) g (fun x hx => hmap (hgs x hx))

/-- The common-centralizer and quotient-orbit arguments use the very same
short root, long root and full short-root line from the reduced comparison. -/
theorem Preparation.unitary_marked_short_quotient
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ (∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v) ∧
      ∀ (s : Set (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)),
        s ⊆ V.map f →
        ∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
          (∀ x ∈ s, g*x*g⁻¹ ∈ V.map f) →
          ∃ a : UnitarySource.shortLineNormalizer L t U,
            a.val.val ∈ normalizer (L : Set G) ∧ ∀ x ∈ s,
              QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a * x *
                (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a)⁻¹ = g*x*g⁻¹ := by
  obtain ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,_,hrest⟩ :=
    d.unitary_marked_short_quotient_with_line h hH hp m hm hc
  exact ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hrest⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
