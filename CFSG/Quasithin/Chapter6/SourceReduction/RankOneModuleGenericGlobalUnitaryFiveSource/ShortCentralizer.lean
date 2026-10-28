module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortNormalizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortOrbit
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FourQuotient

/-!
# Full ambient containment for the original U₅ short-root centralizer

The first quotient identifies the normalizer of the full fixed line.
The residual short-root centralizer has odd index in the ambient one,
because S=T puts every local two-subgroup in the whole residual L.
Transport the native Sylow centralizing the compatible long root into the
ambient centralizer. The intrinsic four-element line lies in its perfect
local residual. The second maximal-normalizer quotient, with its central
involution kernel and trivial ambient odd core, forces C_G(t) into N_G(L).
Both endpoint equations and the same marking are retained.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Both F.4.42 quotients give the full ambient short-centralizer bound. -/
theorem Preparation.unitaryFive_short_centralizer_at
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val)
    (h1 : ∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val)
    (t : (normalizerAmalgam L (residual H)).M₁₂)
    (ht : t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (ht2 : orderOf t.val = 2)
    (hshort : (F.middle t).val = MulAut.conj U.shortInvolution.val) :
    centralizer ({t.val} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨tL,htL,j,hj,hzconj,hgeo,hVamb,hBamb⟩ :=
    d.unitaryFive_short_intrinsic_at h hH hp U hc r a F h0 t ht hshort
  obtain ⟨hVcard,hBcard,hline⟩ :=
    d.unitaryFive_short_line_normalizer_at h hH hp U hc r a F h0 h1 t ht ht2 hshort
  let Y := centralizer ({tL} : Set L)
  let M := centralizer ({tL.val} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf M
  let f := CentralizerLineQuotient.shortCentralizerEmbedding L tL
  have hf : Function.Injective f := CentralizerLineQuotient.shortCentralizerEmbedding_injective L tL
  let V := (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map j.toMonoidHom
  let B := (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map j.toMonoidHom
  let Bm := B.map f
  let zY := j (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)
  let z := f zY
  obtain ⟨hVz,hVE,hVc,hBc,hindex,hBV,hBcenter,hfixed,htB⟩ := hgeo
  have hrange : f.range = L.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.val.property
    · intro hx
      let y : L := ⟨x.val,hx⟩
      have hy : y ∈ Y := mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
      exact ⟨⟨y,hy⟩,rfl⟩
  have hBimage : Bm.map M.subtype = UnitaryFiveShortSpace.ambientLine L tL.val := by
    rw [map_map,map_map] at hBamb ⊢
    exact hBamb.trans (congrArg (UnitaryFiveShortSpace.ambientLine L) htL.symm)
  have hBmX : Bm ≤ X := by
    rintro b ⟨y,hy,rfl⟩
    exact L.le_normalizer y.val.property
  have hNB : normalizer (Bm : Set M) = X := by
    have he := congrArg (comap M.subtype) hline
    rw [←htL,←hBimage] at he
    rw [comap_inf,comap_normalizer_eq_of_le_range (map_le_range M.subtype Bm),
      comap_map_eq_self_of_injective M.subtype_injective] at he
    have hM : (centralizer ({tL.val} : Set G)).comap M.subtype = ⊤ := by
      ext x
      simp only [mem_comap,mem_top,iff_true]
      exact x.property
    simpa only [X,Subgroup.subgroupOf,comap_inf,hM,inf_top_eq] using he
  let : IsElementaryAbelian 2 V := hVE
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective (inclusion hBV) (inclusion_injective hBV)
  let : IsElementaryAbelian 2 Bm := IsElementaryAbelian.map f
  have hBmcard : Nat.card Bm = 4 := by
    rw [card_map_of_injective hf]
    exact hBc
  let tM : M := ⟨tL.val,mem_centralizer_singleton_iff.mpr rfl⟩
  let Z := zpowers tM
  have hZB : Z ≤ Bm := zpowers_le.mpr (mem_map_of_mem f htB)
  have hZcenter : Z ≤ center M := by
    apply zpowers_le.mpr
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_zpowers,←Subgroup.orderOf_coe]
    change orderOf tL.val = 2
    rwa [htL]
  obtain ⟨P₀,hP₀⟩ := d.unitaryFive_plane_center_centralizer_sylow h hH hp U hc
    tL.val (by simpa only [htL] using ht)
  have hPL := d.unitaryFive_normalizer_two_subgroup_le_left h hH hp U hc r
    ((P₀ : Subgroup M).map M.subtype) (P₀.isPGroup'.map M.subtype) hP₀
  have hP₀range : (P₀ : Subgroup M) ≤ f.range := by
    rw [hrange]
    intro x hx
    exact hPL (mem_map_of_mem M.subtype hx)
  have hoddIndex : ¬ 2 ∣ f.range.index := fun hd =>
    P₀.not_dvd_index (hd.trans (index_dvd_of_le hP₀range))
  let : Finite (ShortSpace.centralizer U.form) := Finite.of_injective j j.injective
  obtain ⟨R₀,hR₀⟩ := ShortSpace.exists_long_centralizing_sylow U.form U.rightLeviTrace U.rightLeviTrace_spec
  let R : Sylow 2 Y := R₀.mapSurjective (f := j.toMonoidHom) j.surjective
  have hRz : (R : Subgroup Y) ≤ centralizer ({zY} : Set Y) := by
    rintro y ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (j.map_mul _ _).symm.trans ((congrArg j
      (mem_centralizer_singleton_iff.mp (hR₀ hx))).trans (j.map_mul _ _))
  have hi : ¬ 2 ∣ ((R : Subgroup Y).map f).index := by
    rw [index_map_of_injective _ hf]
    exact Nat.prime_two.not_dvd_mul R.not_dvd_index hoddIndex
  let S : Sylow 2 M := (R.isPGroup'.map f).toSylow hi
  have hSX : (S : Subgroup M) ≤ X := by
    rintro x ⟨y,hy,rfl⟩
    exact L.le_normalizer y.val.property
  have hzcentral : ∀ x ∈ (S : Subgroup M), Commute z x := by
    rintro x ⟨y,hy,rfl⟩
    exact Commute.map ((mem_centralizer_singleton_iff.mp (hRz hy)).symm) f
  have hlong := d.unitaryFive_marked_long_mem_right_center h hH hp U hc a
  have hlong2 : orderOf (a.comparison.left.symm U.longInvolution).val = 2 := by
    rw [Subgroup.orderOf_coe,a.comparison.left.symm.orderOf_eq,U.longInvolution_order]
  have hz2 : orderOf z = 2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hzconj
    change orderOf zY.val.val = 2
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq _).trans hlong2
  have hzS : z ∈ (S : Subgroup M) := by
    have hzN : z ∈ normalizer (S : Set M) := Subgroup.centralizer_le_normalizer _
      (fun x hx => (hzcentral x hx).symm.eq)
    have hpz : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
      (by simpa only [Nat.card_zpowers,pow_one] using hz2)
    have hm : z ∈ zpowers z ⊓ normalizer (S : Set M) := ⟨mem_zpowers z,hzN⟩
    rw [hpz.inf_normalizer_sylow S] at hm
    exact hm.2
  let tN : normalizer (L : Set G) := ⟨tL.val,L.le_normalizer tL.property⟩
  have hfix : ∃! q : M ⧸ X, z • q = q := by
    apply UnitaryFiveFusion.marked_short_unique_fixed d h hH hp U hc r a F h0 h1
      tN (by change tL.val ∈ _; rwa [htL]) (by change orderOf tL.val = 2; rwa [htL]) ?_ _ hlong hlong2
    · exact hzconj
    · have he : tN = inclusion inf_le_left t := Subtype.ext htL
      rw [he]
      apply Subtype.ext
      exact (congrArg Subtype.val (F.left_commutes t)).trans hshort
  let P := (solvableResidual Y).map f
  let : Group.IsPerfect P := Group.IsPerfect.map f
  have hBP : Bm ≤ P := by
    apply map_mono
    have hk : 3 < Nat.card (FixedBy.subfield U.F U.form.conj) := by
      have hcard : Nat.card (FixedBy.subfield U.F U.form.conj) = 4 :=
        FiniteField.card_fixed_of_quadratic_frobenius U.form.conj 2 2 (by decide)
          (by simpa using U.card) U.conjugation
      omega
    have hv := map_mono (f := j.toMonoidHom)
      (ShortSpace.space_le_solvableResidual U.form U.rightLeviTrace U.rightLeviTrace_spec hk)
    rw [map_solvableResidual_eq j.toMonoidHom j.surjective] at hv
    exact hBV.trans hv
  have hPC : P ≤ centralizer (Bm : Set M) := by
    rintro p ⟨y,hy,rfl⟩ b ⟨w,hw,rfl⟩
    exact (f.map_mul _ _).symm.trans ((congrArg f
      (mem_center_iff.mp (hBcenter hw) y).symm).trans (f.map_mul _ _))
  have hodd : pPrimeCore 2 M = ⊥ := d.unitaryFive_involution_centralizer_oddCore
    h hH hp U hc tL.val (by simpa only [htL] using ht2)
  have hX := ChapterF.UnitaryFiveSource.eq_top_of_perfect_four X Bm Z hBmX hZB hZcenter hNB
    S hSX z hzS hzcentral hfix P hBP hPC hBmcard hZcard hodd
  intro x hx
  have hxM : x ∈ M := by change x ∈ centralizer ({tL.val} : Set G); rwa [htL]
  exact hX.ge (show (⟨x,hxM⟩ : M) ∈ (⊤ : Subgroup M) from mem_top _)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
