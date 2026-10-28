module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortRoot

/-!
# The prepared short-root quotient orbits

The full fixed-field line in the original residual centralizer is retained
as the kernel. Every nonidentity image of its q³ long-root normal closure
is a conjugate of the marked long root after this line is killed. The
conjugating element lies in the original O^{2′} of that residual centralizer.
The literal map into N_{C_G(t)}(U)/U has exactly U as its kernel. Its
image module has order q² and the marked long root survives. No embedding
of the full normalizer into a unitary automorphism group is assumed.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
Both orientations, degree-two comparisons and q=4 are retained. Unique
fixed cosets in the ambient short-root centralizer are still required.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySource
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)

/-- The actual residual centralizer embeds in the ambient centralizer. -/
def shortCentralizerEmbedding : centralizer ({t} : Set L) →*
    centralizer ({t.val} : Set G) :=
  (L.subtype.comp (centralizer ({t} : Set L)).subtype).codRestrict _ (by
    intro x
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)))

theorem shortCentralizerEmbedding_injective :
    Function.Injective (shortCentralizerEmbedding L t) := by
  intro x y he
  have hh : x.val.val = y.val.val :=
    congrArg (fun a : centralizer ({t.val} : Set G) => a.val) he
  exact Subtype.ext (Subtype.ext hh)

/-- The normalizer is taken inside the actual ambient short-root centralizer. -/
def shortLineNormalizer (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (centralizer ({t.val} : Set G)) :=
  normalizer (U.map (shortCentralizerEmbedding L t) : Set _)

/-- The original entire line in its ambient normalizer. -/
def shortLineKernel (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (shortLineNormalizer L t U) :=
  (U.map (shortCentralizerEmbedding L t)).subgroupOf (shortLineNormalizer L t U)

instance shortLineKernel_normal (U : Subgroup (centralizer ({t} : Set L))) :
    (shortLineKernel L t U).Normal :=
  normal_subgroupOf_of_le_normalizer le_rfl

/-- Centrality of the local line places the whole residual centralizer in
the actual ambient line normalizer. -/
def shortLineNormalizerMap (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) :
    centralizer ({t} : Set L) →* shortLineNormalizer L t U :=
  (shortCentralizerEmbedding L t).codRestrict _ (by
    intro x
    apply Subgroup.centralizer_le_normalizer
    rintro y ⟨u,hu,rfl⟩
    exact (map_mul _ u x).symm.trans
      ((congrArg (shortCentralizerEmbedding L t) (mem_center_iff.mp (hU hu) x).symm).trans
        (map_mul _ x u)))

/-- The literal homomorphism into N_{C_G(t)}(U)/U. -/
def shortLineQuotientMap (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) :
    centralizer ({t} : Set L) →* shortLineNormalizer L t U ⧸ shortLineKernel L t U :=
  (QuotientGroup.mk' (shortLineKernel L t U)).comp (shortLineNormalizerMap L t U hU)

/-- The kernel is the whole original line, without an extra central kernel. -/
theorem shortLineQuotientMap_ker (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) :
    (shortLineQuotientMap L t U hU).ker = U := by
  ext x
  change QuotientGroup.mk' (shortLineKernel L t U)
    (shortLineNormalizerMap L t U hU x) = 1 ↔ x ∈ U
  apply (QuotientGroup.eq_one_iff _).trans
  change shortCentralizerEmbedding L t x ∈ U.map (shortCentralizerEmbedding L t) ↔ x ∈ U
  constructor
  · rintro ⟨y,hy,he⟩
    exact (shortCentralizerEmbedding_injective L t he) ▸ hy
  · exact mem_map_of_mem _

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The short-root centralizer in the original left residual contains the
actual long-root normal closure, full fixed line and all its nonzero quotient
vector orbits, with conjugators in the genuine prime-to-two residual. -/
theorem Preparation.unitary_short_root_quotient_orbits_with_core
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      U ≤ V ∧ U ≤ center (centralizer ({t} : Set L)) ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      ∀ {J : Type u} [Group J] (f : centralizer ({t} : Set L) →* J),
        U ≤ f.ker → ∀ v ∈ V.map f, v ≠ 1 →
          ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
            f a * f z * (f a)⁻¹ = v := by
  obtain ⟨hm',hn,⟨e⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  refine ⟨hm',hn,?_⟩
  let F := MatrixField m
  let σ := fieldConj m
  let hσ := fieldConj_involutive m hm
  let B := localFactor F (form F σ hσ)
  let X := shortCentralizer F σ hσ
  let f : B ≃* L := (L2ProjectIso m hm).trans e.symm
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
  refine ⟨t,(orderOf_coe t).trans ht,z,
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
  refine ⟨IsElementaryAbelian.map a.toMonoidHom,hVQ,hVc,hUc,hindex,hUV,hUC,htU,?_⟩
  intro J _ g hUg v hv hv1
  have hker : U₀ ≤ (g.comp a.toMonoidHom).ker := by
    intro x hx
    exact hUg (mem_map_of_mem a.toMonoidHom hx)
  have hv' : v ∈ V₀.map (g.comp a.toMonoidHom) := by
    rw [←map_map]
    exact hv
  obtain ⟨b,hb,he⟩ := SourceNormalizer.FourShortRoot.orthogonal_image_residual_fusion
    F σ hσ (g.comp a.toMonoidHom) hker hv' hv1
  exact ⟨a b,(map_primeToResidual a).le (mem_map_of_mem a.toMonoidHom hb),he⟩

/-- The short-root centralizer in the original left residual contains the
actual long-root normal closure, full fixed line and all its nonzero quotient
vector orbits, with conjugators in the genuine prime-to-two residual. -/
theorem Preparation.unitary_short_root_quotient_orbits
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      IsElementaryAbelian 2 V ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      U ≤ V ∧ U ≤ center (centralizer ({t} : Set L)) ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      ∀ {J : Type u} [Group J] (f : centralizer ({t} : Set L) →* J),
        U ≤ f.ker → ∀ v ∈ V.map f, v ≠ 1 →
          ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
            f a * f z * (f a)⁻¹ = v := by
  obtain ⟨hm',hn,t,ht,z,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,hfusion⟩ :=
    d.unitary_short_root_quotient_orbits_with_core h hH hp m hm hc
  exact ⟨hm',hn,t,ht,z,hz,U,hV,hVc,hUc,hindex,hUV,hU,htU,hfusion⟩

/-- The original ambient line normalizer quotient has the expected
q²-element elementary module and all its nonzero vectors are conjugate
to the surviving marked long root under the residual local action. -/
theorem Preparation.unitary_short_root_ambient_quotient
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ ∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v := by
  obtain ⟨hm',hn,t,ht,z,hz,U,hV,hVc,hUc,hindex,hUV,hU,htU,hfusion⟩ :=
    d.unitary_short_root_quotient_orbits h hH hp m hm hc
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
  exact ⟨hm',hn,t,ht,z,hz,U,hU,hUc,hker,IsElementaryAbelian.map f,hcV,htU,htkill,hzne,hfusion⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
