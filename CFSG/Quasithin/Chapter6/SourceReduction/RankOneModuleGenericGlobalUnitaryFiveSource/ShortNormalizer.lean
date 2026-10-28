module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortSpace
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.CentralizerLineQuotient
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.ShortLongMark
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.PerfectOrbit

/-!
# The full fixed-line normalizer for the marked U₅ short root

The transported orthogonal three-space is the commutator of the plane-core
center with the residual short-root centralizer. Its full fixed line is
intrinsic, so both are normalized by the full local stabilizer. In the
normalizer of the line, quotienting by all four elements produces a normal
module of order sixteen with a perfect transitive actor. The compatible
long root has a unique fixed coset, by its literal membership in the
opposite residual center and the existing ambient fusion theorem.
The perfect-orbit contradiction gives the first F.4.42 normalizer equality
on the same original marking and extension.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
namespace UnitaryFiveShortSpace
variable {G : Type*} [Group G]

/-- The intrinsic orthogonal space in the original ambient group. -/
def ambientSpace (L : Subgroup G) (t : G) : Subgroup G :=
  ⁅(center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype,
    L ⊓ centralizer ({t} : Set G)⁆

/-- The full line, described intrinsically by its local fixed points. -/
def ambientLine (L : Subgroup G) (t : G) : Subgroup G :=
  ambientSpace L t ⊓ centralizer (L ⊓ centralizer ({t} : Set G) : Set G)

theorem ambient_normalizers (L : Subgroup G) (t : G) :
    normalizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (ambientSpace L t : Set G) ∧
    normalizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (ambientLine L t : Set G) := by
  let Y := L ⊓ centralizer ({t} : Set G)
  let X := normalizer (L : Set G) ⊓ centralizer ({t} : Set G)
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  have hXY : X ≤ normalizer (Y : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (centralizer ({t} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hXZ : X ≤ normalizer (Z : Set G) :=
    inf_le_left.trans ((normalizer_le_normalizer_characteristic_image L (pCore 2 L)).trans
      (normalizer_le_normalizer_characteristic_image (L.pCoreIn 2) (center (L.pCoreIn 2))))
  have hXV : X ≤ normalizer (ambientSpace L t : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z,Y⁆).map (MulAut.conj x).toMonoidHom = _
    have hZmap : Z.map (MulAut.conj x).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp (hXZ hx)
    have hYmap : Y.map (MulAut.conj x).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp (hXY hx)
    rw [map_commutator,hZmap,hYmap]
    rfl
  exact ⟨hXV,(le_inf hXV (hXY.trans (normalizer_le_normalizer_centralizer Y))).trans
    inf_normalizer_le_normalizer_inf⟩

variable [Finite G] (U : Model 4) {P L : Subgroup G} (e : P ≃* U.rightParabolic)
    (hr : (solvableResidual P).map P.subtype = L)
    (t : L) (ht : t.val = (e.symm U.shortInvolution).val)

theorem space_map_intrinsic :
    ((ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map
      (centralizerCoordinates U e hr t ht).toMonoidHom).map
      (centralizer ({t} : Set L)).subtype =
        ⁅(center (pCore 2 L)).map (pCore 2 L).subtype,centralizer ({t} : Set L)⁆ := by
  let b := coordinates U e hr
  have hK : 2 < Nat.card (FixedBy.subfield U.F U.form.conj) := by
    have hcard : Nat.card (FixedBy.subfield U.F U.form.conj) = 4 :=
      FiniteField.card_fixed_of_quadratic_frobenius U.form.conj 2 2 (by decide)
        (by simpa using U.card) U.conjugation
    omega
  have hC : (ShortSpace.centralizer U.form).map b.toMonoidHom =
      centralizer ({t} : Set L) := by
    rw [ShortSpace.centralizer,CentralizerSmallKernelTransport.map_centralizer]
    congr 2
    apply Subtype.ext
    exact (coordinates_short_val U e hr).trans ht.symm
  rw [map_map]
  change (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map
    (b.toMonoidHom.comp (ShortSpace.centralizer U.form).subtype) = _
  rw [←map_map,ShortSpace.space_map_eq_commutator U.form U.rightLeviTrace U.rightLeviTrace_spec hK,
    map_commutator,map_embeddedCenter _ _ b.injective,pCore_map_iso,hC]

theorem space_map_ambient :
    (((ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map
      (centralizerCoordinates U e hr t ht).toMonoidHom).map
      (centralizer ({t} : Set L)).subtype).map L.subtype = ambientSpace L t.val := by
  rw [space_map_intrinsic,map_commutator,map_embeddedCenter _ _ L.subtype_injective,
    map_subtype_centralizer_singleton]
  rfl

theorem line_map_ambient :
    (((ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map
      (centralizerCoordinates U e hr t ht).toMonoidHom).map
      (centralizer ({t} : Set L)).subtype).map L.subtype = ambientLine L t.val := by
  let a := centralizerCoordinates U e hr t ht
  let Y := centralizer ({t} : Set L)
  let f := L.subtype.comp (Y.subtype.comp a.toMonoidHom)
  have hf : Function.Injective f := L.subtype_injective.comp (Y.subtype_injective.comp a.injective)
  have hV := space_map_ambient U e hr t ht
  rw [map_map,map_map] at hV ⊢
  change (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map f = _
  change (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map f = _ at hV
  have hY : f.range = L ⊓ centralizer ({t.val} : Set G) := by
    dsimp only [f]
    have ha : a.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr a.surjective
    rw [MonoidHom.range_comp,MonoidHom.range_comp,ha,
      ←MonoidHom.range_eq_map,range_subtype,map_subtype_centralizer_singleton]
  apply le_antisymm
  · rintro x ⟨b,hb,rfl⟩
    refine ⟨hV ▸ mem_map_of_mem f (ShortSpace.line_le_space U.form U.rightLeviTrace U.rightLeviTrace_spec hb),?_⟩
    intro y hy
    obtain ⟨d,rfl⟩ := hY.ge hy
    exact (f.map_mul d b).symm.trans ((congrArg f
      (mem_center_iff.mp (ShortSpace.line_le_center U.form U.rightLeviTrace U.rightLeviTrace_spec hb) d)).trans (f.map_mul b d))
  · rintro x ⟨hx,hfix⟩
    obtain ⟨b,hb,rfl⟩ := hV ▸ hx
    refine mem_map_of_mem f ((ShortSpace.line_eq_space_inf_center U.form U.rightLeviTrace U.rightLeviTrace_spec).ge ⟨hb,?_⟩)
    apply mem_center_iff.mpr
    intro d
    apply hf
    simpa only [map_mul] using hfix (f d) (hY.le ⟨d,rfl⟩)

end UnitaryFiveShortSpace
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The actual selected short root carries the native orthogonal space and
its entire fixed line, through the same original endpoint comparison. -/
theorem Preparation.unitaryFive_short_intrinsic_at
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
    (t : (normalizerAmalgam L (residual H)).M₁₂)
    (ht : t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hshort : (F.middle t).val = MulAut.conj U.shortInvolution.val) :
    ∃ tL : L, tL.val = t.val ∧
    ∃ j : ShortSpace.centralizer U.form ≃* Subgroup.centralizer ({tL} : Set L),
      (∀ x, (j x).val.val = (a.comparison.left.symm (U.rightLocalEquiv x.val).val).val) ∧
      IsConj (a.comparison.left.symm U.longInvolution).val
        (j (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)).val.val ∧
      UnitaryFiveShortSpace.Geometry U tL j ∧
      (((ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map j.toMonoidHom).map
        (centralizer ({tL} : Set L)).subtype).map L.subtype =
          UnitaryFiveShortSpace.ambientSpace L t.val ∧
      (((ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map j.toMonoidHom).map
        (centralizer ({tL} : Set L)).subtype).map L.subtype =
          UnitaryFiveShortSpace.ambientLine L t.val := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  let tL : L := ⟨t.val,pCoreIn_le 2 L (map_subtype_le _ ht)⟩
  let tP : P := ⟨t.val,hLP tL.property⟩
  have hmark : a.comparison.left tP = U.shortInvolution := by
    apply Subtype.ext
    apply five_conj_injective U
    calc
      _ = (F.left (inclusion r.left_le tP)).val := (h0 tP).symm
      _ = (F.middle t).val := congrArg Subtype.val (F.left_commutes t)
      _ = _ := hshort
  have htval : tL.val = (a.comparison.left.symm U.shortInvolution).val := by
    have he : tP = a.comparison.left.symm U.shortInvolution :=
      a.comparison.left.injective (hmark.trans (a.comparison.left.apply_symm_apply _).symm)
    exact congrArg Subtype.val he
  have hr : (solvableResidual P).map P.subtype = L :=
    d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
  let j := UnitaryFiveShortSpace.centralizerCoordinates U a.comparison.left hr tL htval
  refine ⟨tL,rfl,j,?_,UnitaryFiveShortSpace.longMark_isConj U a.comparison.left hr tL htval,
    UnitaryFiveShortSpace.geometry U a.comparison.left hr tL htval,
    UnitaryFiveShortSpace.space_map_ambient U a.comparison.left hr tL htval,
    UnitaryFiveShortSpace.line_map_ambient U a.comparison.left hr tL htval⟩
  intro x
  rw [show (j x).val = UnitaryFiveShortSpace.coordinates U a.comparison.left hr x.val from
    UnitaryFiveShortSpace.centralizerCoordinates_val U a.comparison.left hr tL htval x]
  exact UnitaryFiveShortSpace.coordinates_val U a.comparison.left hr x.val


namespace UnitaryFiveShortSpace
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)

private theorem quotient_module_normal
    (B : Subgroup (centralizer ({t} : Set L)))
    (hB : B ≤ center (centralizer ({t} : Set L)))
    (V : Subgroup (centralizer ({t} : Set L)))
    (hV : (V.map (centralizer ({t} : Set L)).subtype).map L.subtype = ambientSpace L t.val) :
    ((V.map (CentralizerLineQuotient.shortLineQuotientMap L t B hB)).subgroupOf
      (CentralizerLineQuotient.shortLineLocalQuotient L t B)).Normal := by
  let Y := centralizer ({t} : Set L)
  let r := CentralizerLineQuotient.shortLineNormalizerMap L t B hB
  let q := QuotientGroup.mk' (CentralizerLineQuotient.shortLineKernel L t B)
  constructor
  intro v hv g
  obtain ⟨a,ha,he⟩ := g.property
  obtain ⟨w,hw,hwq⟩ := hv
  change g.val * v.val * g.val⁻¹ ∈ V.map (CentralizerLineQuotient.shortLineQuotientMap L t B hB)
  change CentralizerLineQuotient.shortLineQuotientMap L t B hB w = v.val at hwq
  rw [←he,←hwq]
  change q a * q (r w) * (q a)⁻¹ ∈ V.map (CentralizerLineQuotient.shortLineQuotientMap L t B hB)
  have hn := (ambient_normalizers L t.val).1 ⟨ha,a.val.property⟩
  have hwG : w.val.val ∈ (V.map Y.subtype).map L.subtype :=
    mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype hw)
  have hreturn : a.val.val * w.val.val * a.val.val⁻¹ ∈
      (V.map Y.subtype).map L.subtype := by
    rw [hV] at hwG ⊢
    exact (mem_normalizer_iff.mp hn _).mp hwG
  obtain ⟨y,⟨b,hb,rfl⟩,hbval⟩ := hreturn
  have hconj : a * r w * a⁻¹ = r b := by
    apply Subtype.ext
    apply Subtype.ext
    exact hbval.symm
  rw [←map_inv,←map_mul,←map_mul,hconj]
  exact mem_map_of_mem (CentralizerLineQuotient.shortLineQuotientMap L t B hB) hb

variable [Finite G] (U : Model 4) {P : Subgroup G} (e : P ≃* U.rightParabolic)
    (hr : (solvableResidual P).map P.subtype = L)
    (ht : t.val = (e.symm U.shortInvolution).val)

/-- The first F.4.42 quotient, retaining the full four-element line. -/
theorem line_normalizer_le_of_unique
    (hfix : ∃! q : centralizer ({t.val} : Set G) ⧸
      (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
      CentralizerLineQuotient.shortCentralizerEmbedding L t
        (centralizerCoordinates U e hr t ht
          (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)) • q = q) :
    CentralizerLineQuotient.shortLineNormalizer L t
      ((ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map
        (centralizerCoordinates U e hr t ht).toMonoidHom) ≤
      (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) := by
  let a := centralizerCoordinates U e hr t ht
  let V := (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom
  let B := (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom
  let z := a (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)
  obtain ⟨hVz,hVE,hVc,hBc,hindex,hBV,hB,hfixed,htB⟩ := geometry U e hr t ht
  change V = normalClosure ({z} : Set _) at hVz
  let f := CentralizerLineQuotient.shortLineQuotientMap L t B hB
  let X := CentralizerLineQuotient.shortLineLocalQuotient L t B
  have hker : f.ker = B := CentralizerLineQuotient.shortLineQuotientMap_ker L t B hB
  let : IsElementaryAbelian 2 V := hVE
  let : IsElementaryAbelian 2 (V.map f) := IsElementaryAbelian.map f
  have hcard : Nat.card (V.map f) = 16 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have hVX : V.map f ≤ X := by
    rintro v ⟨w,hw,rfl⟩
    exact CentralizerLineQuotient.shortLineQuotientMap_mem_local L t B hB w
  let : ((V.map f).subgroupOf X).Normal :=
    quotient_module_normal L t B hB V (space_map_ambient U e hr t ht)
  obtain ⟨D,hD,hDf,hDorb⟩ := quotient_perfect_orbit U e hr t ht f hker.ge
  have hDX : D ≤ X := by
    rintro v hv
    obtain ⟨w,rfl⟩ := hDf hv
    exact CentralizerLineQuotient.shortLineQuotientMap_mem_local L t B hB w
  let R := CentralizerLineQuotient.shortLineNormalizer L t B
  let r := CentralizerLineQuotient.shortLineNormalizerMap L t B hB
  let X₀ := CentralizerLineQuotient.shortLineLocal L t B
  have hzX₀ : r z ∈ X₀ := L.le_normalizer z.val.property
  have hfixR : ∃! q : R ⧸ X₀, r z • q = q := by
    apply UniqueFixedCoset.unique_of_transporter hzX₀
    intro g hg
    exact UniqueFixedCoset.transporter_mem
      (M := (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)))
      (L.le_normalizer z.val.property) hfix (g := g.val) hg
  have hfixQ : ∃! q : (R ⧸ CentralizerLineQuotient.shortLineKernel L t B) ⧸ X,
      f z • q = q := UniqueFixedCoset.unique_map_of_surjective
    (QuotientGroup.mk' (CentralizerLineQuotient.shortLineKernel L t B))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact CentralizerLineQuotient.shortLineKernel_le_local L t B) hzX₀ hfixR
  let : Group.IsPerfect D := hD
  have htop := ChapterF.UnitarySource.eq_top_of_perfect_orbit
    (V.map f) X D hVX hDX (by rw [hcard]; decide) (f z)
    (mem_map_of_mem f (by rw [hVz]; exact subset_normalClosure (Set.mem_singleton _))) hDorb hfixQ
  intro b hb
  let c : R := ⟨b,hb⟩
  apply (CentralizerLineQuotient.shortLineLocalQuotient_mk_iff L t B c).mp
  change QuotientGroup.mk' (CentralizerLineQuotient.shortLineKernel L t B) c ∈ X
  rw [htop]
  exact mem_top _

end UnitaryFiveShortSpace

/-- The plane long mark pulls back to the center of the original opposite residual. -/
theorem Preparation.unitaryFive_marked_long_mem_right_center
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse) :
    (a.comparison.left.symm U.longInvolution).val ∈
      (center (residual H)).map (residual H).subtype := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  let f := U.leftParabolic.subtype.comp a.comparison.right.toMonoidHom
  have hf : Function.Injective f := U.leftParabolic.subtype_injective.comp a.comparison.right.injective
  have hR : ((residual H).subgroupOf P).map f = U.leftLocalImage := by
    have hres : (residual H).subgroupOf P = solvableResidual P := by
      have he : (solvableResidual P).map P.subtype = residual H :=
        d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 1
      rw [←he]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    rw [hres,←map_map,map_solvableResidual_eq a.comparison.right.toMonoidHom
      a.comparison.right.surjective]
    rfl
  have hcenter := U.longInvolution_mem_leftLocalImage_center
  have hleft : U.longInvolution.val ∈ U.leftParabolic := map_subtype_le _ (map_subtype_le _ hcenter)
  let z : U.leftParabolic := ⟨U.longInvolution.val,hleft⟩
  let zm : U.overlap := ⟨U.longInvolution.val,hleft,U.longInvolution.property⟩
  have hsame : (a.comparison.left.symm U.longInvolution).val =
      (a.comparison.right.symm z).val :=
    (congrArg Subtype.val (a.comparison.symm.left_commutes zm)).trans
      (congrArg Subtype.val (a.comparison.symm.right_commutes zm)).symm
  rw [hsame]
  have hcenterMap := map_embeddedCenter ((residual H).subgroupOf P) f hf
  rw [hR] at hcenterMap
  obtain ⟨y,hy,he⟩ := hcenterMap.ge hcenter
  have hye : y = a.comparison.right.symm z := by
    apply a.comparison.right.injective
    apply Subtype.ext
    exact he.trans (congrArg Subtype.val (a.comparison.right.apply_symm_apply z)).symm
  have hmap := map_embeddedCenter ((residual H).subgroupOf P) P.subtype P.subtype_injective
  rw [map_subgroupOf_eq_of_le hKP] at hmap
  rw [←hye]
  exact hmap.le (mem_map_of_mem P.subtype hy)

theorem Preparation.unitaryFive_short_line_normalizer_at
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
    Nat.card (UnitaryFiveShortSpace.ambientSpace L t.val) = 64 ∧
    Nat.card (UnitaryFiveShortSpace.ambientLine L t.val) = 4 ∧
    normalizer (UnitaryFiveShortSpace.ambientLine L t.val : Set G) ⊓ centralizer ({t.val} : Set G) =
      normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  let tL : L := ⟨t.val,pCoreIn_le 2 L (map_subtype_le _ ht)⟩
  let tP : P := ⟨t.val,hLP tL.property⟩
  have hmark : a.comparison.left tP = U.shortInvolution := by
    apply Subtype.ext
    apply five_conj_injective U
    calc
      _ = (F.left (inclusion r.left_le tP)).val := (h0 tP).symm
      _ = (F.middle t).val := congrArg Subtype.val (F.left_commutes t)
      _ = _ := hshort
  have htval : tL.val = (a.comparison.left.symm U.shortInvolution).val := by
    have he : tP = a.comparison.left.symm U.shortInvolution :=
      a.comparison.left.injective (hmark.trans (a.comparison.left.apply_symm_apply _).symm)
    exact congrArg Subtype.val he
  have hr : (solvableResidual P).map P.subtype = L :=
    d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
  let j := UnitaryFiveShortSpace.centralizerCoordinates U a.comparison.left hr tL htval
  let Y := centralizer ({tL} : Set L)
  let M := centralizer ({t.val} : Set G)
  let V := (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map j.toMonoidHom
  let B := (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map j.toMonoidHom
  let z := j (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)
  have hVamb : (V.map Y.subtype).map L.subtype = UnitaryFiveShortSpace.ambientSpace L t.val :=
    UnitaryFiveShortSpace.space_map_ambient U a.comparison.left hr tL htval
  have hBamb : (B.map Y.subtype).map L.subtype = UnitaryFiveShortSpace.ambientLine L t.val :=
    UnitaryFiveShortSpace.line_map_ambient U a.comparison.left hr tL htval
  obtain ⟨_,_,hVc,hBc,_⟩ := UnitaryFiveShortSpace.geometry U a.comparison.left hr tL htval
  have hVcard : Nat.card (UnitaryFiveShortSpace.ambientSpace L t.val) = 64 := by
    rw [←hVamb,card_map_of_injective L.subtype_injective,card_map_of_injective Y.subtype_injective]
    exact hVc
  have hBcard : Nat.card (UnitaryFiveShortSpace.ambientLine L t.val) = 4 := by
    rw [←hBamb,card_map_of_injective L.subtype_injective,card_map_of_injective Y.subtype_injective]
    exact hBc
  have hlong : (a.comparison.left.symm U.longInvolution).val ∈
      (center (residual H)).map (residual H).subtype :=
    d.unitaryFive_marked_long_mem_right_center h hH hp U hc a
  have hlong2 : orderOf (a.comparison.left.symm U.longInvolution).val = 2 := by
    rw [Subgroup.orderOf_coe,a.comparison.left.symm.orderOf_eq,U.longInvolution_order]
  have hfix : ∃! q : M ⧸ (normalizer (L : Set G)).subgroupOf M,
      CentralizerLineQuotient.shortCentralizerEmbedding L tL z • q = q := by
    apply UnitaryFiveFusion.marked_short_unique_fixed d h hH hp U hc r a F h0 h1
      (inclusion inf_le_left t) ht ht2 ?_ _ hlong hlong2
    · exact UnitaryFiveShortSpace.longMark_isConj U a.comparison.left hr tL htval
    · apply Subtype.ext
      exact (congrArg Subtype.val (F.left_commutes t)).trans hshort
  have hbound := UnitaryFiveShortSpace.line_normalizer_le_of_unique L tL U a.comparison.left hr htval hfix
  have hBimage : (B.map (CentralizerLineQuotient.shortCentralizerEmbedding L tL)).map M.subtype =
      UnitaryFiveShortSpace.ambientLine L t.val := by
    rw [map_map,map_map] at hBamb ⊢
    exact hBamb
  refine ⟨hVcard,hBcard,le_antisymm ?_ ?_⟩
  · rintro g ⟨hg,hgt⟩
    let gm : M := ⟨g,hgt⟩
    have hn : gm ∈ normalizer
        ((UnitaryFiveShortSpace.ambientLine L t.val).comap M.subtype : Set M) :=
      (le_normalizer_comap M.subtype) (show gm ∈
        (normalizer (UnitaryFiveShortSpace.ambientLine L t.val : Set G)).comap M.subtype from hg)
    rw [←hBimage,comap_map_eq_self_of_injective M.subtype_injective] at hn
    exact ⟨hbound hn,hgt⟩
  · intro g hg
    exact ⟨(UnitaryFiveShortSpace.ambient_normalizers L t.val).2 hg,hg.2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
