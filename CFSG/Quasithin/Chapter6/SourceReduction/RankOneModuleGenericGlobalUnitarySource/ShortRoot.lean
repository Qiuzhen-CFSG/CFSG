module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import Theory.ElementaryAbelian.Injective

/-!
# The prepared unitary short-root three-space and its fixed line

The actual projective plane-residual comparison constructs short and long
involutions t,z in the original L. Inside C_L(t), the normal closure of z
is an elementary abelian three-space of order q³, embedded in the original
O₂(L). Its fixed subgroup under the actual O^{2′}(C_L(t)) is a central
line of order q, with index q² in the three-space. Since the prepared
comparison gives m>1, the line strictly contains the cyclic group of t.

All transports use the concrete SU₄ projectivization and the original
subgroup embedding. Both ordinary and degree-two comparisons, either
orientation and q=4 are retained, as is the original n=2m relation.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. This constructs the residual-local root-module input.
It does not replace C_G(t) by C_L(t) or by C_{N_G(L)}(t); the full ambient
unique-fixed-coset and normalizer arguments remain further obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
namespace UnitarySource
private theorem map_fixed_residual {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (V U : Subgroup X)
    (h : V ⊓ centralizer (primeToResidual 2 X : Set X) = U) :
    V.map e.toMonoidHom ⊓ centralizer (primeToResidual 2 Y : Set Y) = U.map e.toMonoidHom := by
  apply le_antisymm
  · rintro y ⟨⟨x,hx,rfl⟩,hy⟩
    refine ⟨x,h.le ⟨hx,?_⟩,rfl⟩
    intro a ha
    apply e.injective
    simp only [map_mul]
    exact hy (e a) ((map_primeToResidual e).le (mem_map_of_mem e.toMonoidHom ha))
  · rintro y ⟨x,hx,rfl⟩
    have hh := h.ge hx
    refine ⟨mem_map_of_mem e.toMonoidHom hh.1,?_⟩
    intro b hb
    obtain ⟨a,ha,rfl⟩ := (map_primeToResidual e).ge hb
    exact (e.map_mul a x).symm.trans ((congrArg e (hh.2 a ha)).trans (e.map_mul x a))
end UnitarySource

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The short-root centralizer in the original left residual contains the
actual long-root normal closure and its full fixed short-root line. -/
theorem Preparation.unitary_short_root_module
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
      V ⊓ centralizer (primeToResidual 2 (centralizer ({t} : Set L)) :
        Set (centralizer ({t} : Set L))) = U ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U := by
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
  refine ⟨IsElementaryAbelian.map a.toMonoidHom,?_,hVc,hUc,hindex,hUV,hUC,
    UnitarySource.map_fixed_residual a V₀ U₀ (SourceNormalizer.FourShortRoot.orthogonal_primeTo_fixed F σ hσ),?_⟩
  · rintro x ⟨y,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩
    apply mem_map_of_mem L.subtype
    have hwQ : w.val ∈ pCore 2 B := by
      rw [←radical_eq_twoCore F σ hσ]
      exact orthogonalRadical_le_radical F σ hσ hw
    exact (pCore_map_iso 2 f).le (mem_map_of_mem f.toMonoidHom hwQ)
  · have htmem : (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Y) ∈ U := by
      exact mem_map_of_mem a.toMonoidHom (SourceNormalizer.FourShortRoot.shortMark_mem_line F σ hσ)
    apply lt_of_le_of_ne (zpowers_le.mpr htmem)
    intro he
    have hh := congrArg (fun D : Subgroup Y => Nat.card D) he
    have ho : orderOf (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Y) = 2 :=
      (orderOf_coe _).symm.trans ht
    rw [Nat.card_zpowers,ho,hUc] at hh
    have hlarge : 2 < 2^m := (Nat.pow_lt_pow_right (by decide : 1 < 2) hm')
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
