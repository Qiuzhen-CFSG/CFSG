module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortRoot
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The full-normalizer short-root three-space

In the original prepared unitary-four rows, put Y=C_L(t) and
X=C_{N_G(L)}(t). The native symmetric Hermitian three-space has the
intrinsic description V=[O₂(L),Y]. Consequently X normalizes V and its
q-element local fixed line U=C_V(Y). The normal closure of the marked
long involution in the entire X is exactly V, of order q³: the closure
inside Y already supplies V, and X-invariance supplies the upper bound.

The construction uses the original subgroup embedding and the actual
SU₄ projectivization. It retains both comparison orientations, the
ordinary and degree-two rows, q=4, and the source relation n=2m with m>1.
The line U is fixed by Y and normalized by X. Identifying it with the
fixed subgroup of O^{2′}(X) requires the later outer transfer argument.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. The ambient unique-fixed-coset and normalizer
arguments in C_G(t) remain further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
namespace UnitarySource
private theorem short_normalizers {G : Type*} [Group G] (L : Subgroup G) (t : G) :
    let Y := L ⊓ centralizer ({t} : Set G)
    let V := ⁅L.pCoreIn 2,Y⁆
    let X := normalizer (L : Set G) ⊓ centralizer ({t} : Set G)
    X ≤ normalizer (V : Set G) ∧
    X ≤ normalizer (V ⊓ centralizer (Y : Set G) : Subgroup G) := by
  dsimp only
  let Y := L ⊓ centralizer ({t} : Set G)
  let V := ⁅L.pCoreIn 2,Y⁆
  let X := normalizer (L : Set G) ⊓ centralizer ({t} : Set G)
  have hXY : X ≤ normalizer (Y : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (centralizer ({t} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hXQ : X ≤ normalizer (L.pCoreIn 2 : Set G) :=
    inf_le_left.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hXV : X ≤ normalizer (V : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅L.pCoreIn 2,Y⁆).map (MulAut.conj x).toMonoidHom = _
    have hqmap : (L.pCoreIn 2).map (MulAut.conj x).toMonoidHom = L.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hXQ hx)
    have hymap : Y.map (MulAut.conj x).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp (hXY hx)
    rw [map_commutator,hqmap,hymap]
  exact ⟨hXV,(le_inf hXV (hXY.trans (normalizer_le_normalizer_centralizer Y))).trans
    inf_normalizer_le_normalizer_inf⟩
end UnitarySource

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original full-normalizer centralizer has the actual q³ long-root
normal closure and normalizes its q-element residual-local fixed line. -/
theorem Preparation.unitary_short_root_normalizer_module
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
      let Y := L ⊓ centralizer ({t.val} : Set G)
      let X := normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)
      let V := ⁅L.pCoreIn 2,Y⁆
      let U := V ⊓ centralizer (Y : Set G)
      IsElementaryAbelian 2 V ∧ V ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      zpowers t.val < U ∧ X ≤ normalizer (V : Set G) ∧ X ≤ normalizer (U : Set G) ∧
      ∃ z : X, orderOf z.val = 2 ∧
        (normalClosure ({z} : Set X)).map X.subtype = V := by
  obtain ⟨hm',hn,⟨e⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  let F := MatrixField m
  let σ := fieldConj m
  let hσ := fieldConj_involutive m hm
  let B := localFactor F (form F σ hσ)
  let C₀ := shortCentralizer F σ hσ
  let V₀ := orthogonalRadical F σ hσ
  let U₀ := SourceNormalizer.FourShortRoot.shortLine F σ hσ
  let f : B ≃* L := (L2ProjectIso m hm).trans e.symm
  let j : B →* G := L.subtype.comp f.toMonoidHom
  have hj : Function.Injective j := L.subtype_injective.comp f.injective
  let t := f (shortLocal F σ hσ)
  let Y := L ⊓ centralizer ({t.val} : Set G)
  let X := normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)
  let V := ⁅L.pCoreIn 2,Y⁆
  let U := V ⊓ centralizer (Y : Set G)
  have ht : orderOf t.val = 2 := by
    exact (orderOf_coe t).trans ((f.orderOf_eq _).trans
      ((orderOf_coe (SourceNormalizer.FourShortRoot.shortMark F σ hσ)).trans
        (SourceNormalizer.FourShortRoot.shortMark_order F σ hσ)))
  have hq : Nat.card (FixedBy.subfield F σ) = 2^m := PointLocal.fixedField_card m hm
  have hq2 : 2 < Nat.card (FixedBy.subfield F σ) := by
    rw [hq]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hm'
  have hQ : (radical F σ hσ).map j = L.pCoreIn 2 := by
    change (radical F σ hσ).map (L.subtype.comp f.toMonoidHom) = _
    rw [←map_map,radical_eq_twoCore,pCore_map_iso]
    rfl
  have hY : C₀.map j = Y := by
    change (centralizer ({shortLocal F σ hσ} : Set B)).map
      (L.subtype.comp f.toMonoidHom) = _
    rw [←map_map,CentralizerSmallKernelTransport.map_centralizer]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hV : V₀.map j = V := by
    change (orthogonalRadical F σ hσ).map j = _
    rw [SourceNormalizer.FourShortRoot.orthogonal_eq_commutator F σ hσ hq2,
      map_commutator,hQ,hY]
  have hU : U₀.map j = U := by
    apply le_antisymm
    · rintro x ⟨a,ha,rfl⟩
      have hh := (SourceNormalizer.FourShortRoot.shortLine_eq_orthogonal_inf_centralizer F σ hσ).le ha
      refine ⟨hV ▸ mem_map_of_mem j hh.1,?_⟩
      intro b hb
      obtain ⟨c,hc,rfl⟩ := hY ▸ hb
      exact (j.map_mul c a).symm.trans ((congrArg j (hh.2 c hc)).trans (j.map_mul a c))
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := hV ▸ hx.1
      apply mem_map_of_mem j
      apply (SourceNormalizer.FourShortRoot.shortLine_eq_orthogonal_inf_centralizer F σ hσ).ge
      refine ⟨ha,?_⟩
      intro b hb
      apply hj
      simpa only [map_mul] using hx.2 (j b) (hY ▸ mem_map_of_mem j hb)
  have hVc : Nat.card V = (2^m)^3 := by
    rw [←hV,card_map_of_injective hj]
    exact (orthogonalRadical_card F σ hσ).trans (congrArg (·^3) hq)
  have hUc : Nat.card U = 2^m := by
    rw [←hU,card_map_of_injective hj]
    exact (SourceNormalizer.FourShortRoot.shortLine_card F σ hσ).trans hq
  have hUV : U ≤ V := inf_le_left
  have hindex : U.relIndex V = (2^m)^2 := by
    have hi := (U.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv,hUc,hVc] at hi
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^m)
    exact hi.trans (by ring)
  have hVX : V ≤ X := by
    rw [←hV]
    rintro x ⟨a,ha,rfl⟩
    exact ⟨L.le_normalizer (f a).property,
      (hY ▸ mem_map_of_mem j (orthogonalRadical_le_shortCentralizer F σ hσ ha)).2⟩
  obtain ⟨hXV,hXU⟩ := UnitarySource.short_normalizers L t.val
  let : IsElementaryAbelian 2 V₀ := IsElementaryAbelian.of_injective
    (inclusion (orthogonalRadical_le_radical F σ hσ)) (inclusion_injective _)
  refine ⟨hm',hn,t,ht,?_,?_,hVc,hUc,hindex,?_,hXV,hXU,?_⟩
  · change IsElementaryAbelian 2 V
    rw [←hV]
    exact IsElementaryAbelian.map j
  · change V ≤ L.pCoreIn 2
    rw [←hV,←hQ]
    exact map_mono (orthogonalRadical_le_radical F σ hσ)
  · have htU : t.val ∈ U := by
      rw [←hU]
      exact mem_map_of_mem j (SourceNormalizer.FourShortRoot.shortMark_mem_line F σ hσ)
    apply lt_of_le_of_ne (zpowers_le.mpr htU)
    intro he
    have hh := congrArg (fun D : Subgroup G => Nat.card D) he
    rw [Nat.card_zpowers,ht,hUc] at hh
    rw [hq] at hq2
    omega
  · let b : C₀ →* X := (j.comp C₀.subtype).codRestrict X (by
      intro a
      exact ⟨L.le_normalizer (f a.val).property,(hY ▸ mem_map_of_mem j a.property).2⟩)
    let z := b (SourceNormalizer.FourShortRoot.longMark F σ hσ)
    have hb : Function.Injective b := by
      intro a c he
      apply Subtype.ext
      exact hj (congrArg (fun u : X => u.val) he)
    have hz : orderOf z.val = 2 := (orderOf_coe z).trans
      ((orderOf_injective b hb _).trans (SourceNormalizer.FourShortRoot.longMark_order F σ hσ))
    refine ⟨z,hz,?_⟩
    let N := normalClosure ({z} : Set X)
    let : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXV
    have hNV : N ≤ V.subgroupOf X := by
      apply normalClosure_le_normal
      rintro a rfl
      change j (SourceNormalizer.FourShortRoot.longMark F σ hσ).val ∈ V
      rw [←hV]
      exact mem_map_of_mem j ((SourceNormalizer.FourShortRoot.long_normalClosure F σ hσ).le
        (subset_normalClosure (Set.mem_singleton _)))
    have hVN : V₀.subgroupOf C₀ ≤ N.comap b := by
      rw [←SourceNormalizer.FourShortRoot.long_normalClosure F σ hσ]
      apply normalClosure_le_normal
      rintro a rfl
      exact subset_normalClosure (Set.mem_singleton z)
    apply le_antisymm
    · exact (map_mono hNV).trans (map_subgroupOf_eq_of_le hVX).le
    · change V ≤ N.map X.subtype
      rw [←hV]
      rintro x ⟨a,ha,rfl⟩
      let c : C₀ := ⟨a,orthogonalRadical_le_shortCentralizer F σ hσ ha⟩
      exact ⟨b c,hVN ha,rfl⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
