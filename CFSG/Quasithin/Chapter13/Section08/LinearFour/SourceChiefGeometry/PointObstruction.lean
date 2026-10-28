module
public import Theory.SpecificGroups.BinaryLinear.LineRadicalNormal
public import Theory.GroupTheory.PResidual.SimpleImageCentralizer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.LineAlignment
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Accounting
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne

/-!
# The point-parabolic contradiction in original 13.8.31(1)

The natural marking on U_H/V1 and the nontrivial central two-core action
identify the image of the actual line normalizer with the full binary
point stabilizer. Its nontrivial normal two-subgroup is the line radical,
of order eight. For the original g-conjugate of V_H, the marked tensor
and six-dimensional section compute the same index over U0, so the
literal kernel Q_H intersect V_H^g is U0.

The actual H_C centralizes the aligned line and therefore normalizes
V_H^g. The kernel equality puts their commutator inside V_H. The normal
section centralizer has nontrivial image in the simple H/O2(H), hence
surjects onto it; two-perfectness puts K in that section centralizer.
This gives [H_C,K] <= V_H, contradicting the existing three-chief-factor
obstruction. The final applications use the actual CriticalPair, retaining
the same conjugator selected by LineAlignment and the original quotient
maps. H_C/V_H is never assumed elementary abelian.

These are conditional source applications. The final marked-section
application still requires the first tensor and orthogonal markings,
the exact V_H/V_H^g intersection, and the actual three-factor bound from
CubicAccounting/LocalMatrixAccounting. Their construction, the extra-line
second-tensor row, and remaining critical geometry stay with
qt-d-138-linear-four-source. The endpoint placement and nontrivial image
are the earlier case-one conclusions of 13.8.27(3); the earlier setup is
owned by qt-d-138-six-g2-source. The final owner qt-d-1381-source must
discharge all these premises. This does not complete 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript (1 March 2004), 13.8.31(1), printed pp.964–965.
The source uses right conjugation; the specified conjugate here is g^-1.
-/

public section
open Subgroup Representation
open BinaryLinear BinaryLinear.OuterCyclic
open Theory.LinearAlgebra
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G]
private theorem natural_transitive
    (H : Subgroup G) (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w) :
    ∀ u v : Fin 4 → ZMod 2, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v := by
  intro u v hu hv
  obtain ⟨a,ha⟩ := exists_linearEquiv_apply_eq hu hv
  obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (pCore 2 H) (e.symm a)
  exact ⟨h,by rw [hact,hh,e.apply_symm_apply]; exact ha⟩

/-- Correcting representatives by the original two-core identifies the
actual line-normalizer image with its marked natural point stabilizer. -/
theorem source_point_normalizer_image
    (H UH Z A : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH Z ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hHZ : H ≤ centralizer (Z : Set G)) (hZ : Nat.card Z = 2)
    (hcomm : ⁅UH,H.pCoreIn 2⁆ ≤ Z) (hmove : ⁅UH,H.pCoreIn 2⁆ ≠ ⊥)
    (hA : Nat.card A = 2) (u : UH) (hu : (u:G) ∈ A) (huZ : (u:G) ∉ Z) :
    (Source.starImage H (normalizer (A : Set G))).map e.toMonoidHom =
      BinaryFivePointStabilizer.stabilizer (d.coordinates u).toAdd := by
  let : (Z.subgroupOf UH).Normal := d.kernel_normal
  obtain ⟨a⟩ := SolvableExclusion.Five.exists_starAction H UH Z d.normalized
    (hHZ.trans (Subgroup.centralizer_le_normalizer _)) hcomm
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp
    have he : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    rw [he]
    infer_instance
  have hc := d.centralizer_eq_kernel_of_transitive (H.pCoreIn 2) hHQ
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hHZ)) hmove
    (natural_transitive H ρ e hact)
  have hm : ∃ n ∈ Source.QH H, n * (u:G) ≠ (u:G) * n := by
    by_contra! hn
    apply huZ
    rw [←hc]
    exact ⟨u.property,hn⟩
  have hu1 : (u:G) ≠ 1 := fun he => huZ (he ▸ Z.one_mem)
  rw [A6Endgame.PointNormalizer.normalizer_image_eq_stabilizer a A hA u hu hu1
    hZ hcomm hm]
  have hfix (x : Source.Hstar H) :
      x ∈ A6Endgame.PointNormalizer.pointStabilizer a u ↔
      e x (d.coordinates u).toAdd = (d.coordinates u).toAdd := by
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    change a.action (QuotientGroup.mk' (pCore 2 H) h) (QuotientGroup.mk' _ u) =
      QuotientGroup.mk' _ u ↔ _
    rw [a.conjugation]
    have heq := d.equivariant h u
    rw [hact] at heq
    rw [←heq]
    exact ((d.quotientEquiv.injective.eq_iff).symm.trans
      Multiplicative.toAdd.injective.eq_iff.symm)
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hfix x).mp hx
  · intro hg
    exact ⟨e.symm g,(hfix _).mpr (by simpa using hg),e.apply_symm_apply g⟩


/-- The nontrivial two-image of a subgroup normal in the actual point
normalizer is the full line radical, with the original quotient marking. -/
theorem source_point_image_radical
    (H UH Z A B : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH Z ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hHZ : H ≤ centralizer (Z : Set G)) (hZ : Nat.card Z = 2)
    (hcomm : ⁅UH,H.pCoreIn 2⁆ ≤ Z) (hmove : ⁅UH,H.pCoreIn 2⁆ ≠ ⊥)
    (hA : Nat.card A = 2) (u : UH) (hu : (u:G) ∈ A) (huZ : (u:G) ∉ Z)
    (hB : IsPGroup 2 B) (hBH : B ≤ H) (hBP : B ≤ normalizer (A : Set G))
    (hnB : normalizer (A : Set G) ≤ normalizer (B : Set G))
    (hne : ¬ B ≤ H.pCoreIn 2) :
    (Source.starImage H B).map e.toMonoidHom =
      radical (Submodule.span (ZMod 2) {(d.coordinates u).toAdd}) ∧
      Nat.card (Source.starImage H B) = 8 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let R := (B.subgroupOf H).map f
  have hk : f.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
    constructor
    · intro hh
      exact (QuotientGroup.eq_one_iff x).mp (e.injective (hh.trans e.map_one.symm))
    · intro hx
      exact (congrArg e ((QuotientGroup.eq_one_iff x).mpr hx)).trans e.map_one
  have hR : (Source.starImage H B).map e.toMonoidHom = R := map_map _ _ _
  have hu0 : (d.coordinates u).toAdd ≠ 0 :=
    fun hh => huZ ((d.coordinates_eq_one_iff u).mp hh)
  have hP : ((normalizer (A : Set G)).subgroupOf H).map f =
      parabolic (Submodule.span (ZMod 2) {(d.coordinates u).toAdd}) := by
    rw [LineRadical.parabolic_eq_point_stabilizer _ hu0]
    exact (map_map _ _ _).symm.trans
      (source_point_normalizer_image H UH Z A ρ d e hact hHZ hZ hcomm hmove hA u hu huZ)
  have hRp : IsPGroup 2 R := hB.comap_subtype.map f
  have hRne : R ≠ ⊥ := by
    intro hz
    have hb := (map_eq_bot_iff (B.subgroupOf H)).mp hz
    rw [hk] at hb
    apply hne
    have hm := map_mono (f := H.subtype) hb
    rwa [map_subgroupOf_eq_of_le hBH] at hm
  have hRP : R ≤ parabolic (Submodule.span (ZMod 2) {(d.coordinates u).toAdd}) := by
    rw [←hP]
    exact map_mono (subgroupOf_mono H hBP)
  have hPR : parabolic (Submodule.span (ZMod 2) {(d.coordinates u).toAdd}) ≤
      normalizer (R : Set _) := by
    rw [←hP]
    exact (map_mono ((comap_mono hnB).trans (B.le_normalizer_comap H.subtype))).trans
      ((B.subgroupOf H).le_normalizer_map f)
  have he := LineRadical.normal_two_eq_radical _ hu0 R hRp hRne hRP hPR
  refine ⟨hR.trans he,?_⟩
  have hc : Nat.card ((Source.starImage H B).map e.toMonoidHom) =
      Nat.card (Source.starImage H B) := card_map_of_injective e.injective
  rw [←hc,hR,he,LineRadical.card _ hu0,Module.finrank_fin_fun]
  rfl

/-- Equality of the two source indices identifies the literal kernel E. -/
theorem source_point_kernel_eq [Finite G]
    (H B U0 : Subgroup G) (hBH : B ≤ H)
    (hU : U0 ≤ B ⊓ H.pCoreIn 2) (hindex : U0.relIndex B = 8)
    (himage : Nat.card (Source.starImage H B) = 8) :
    B ⊓ H.pCoreIn 2 = U0 := by
  have hi : (B ⊓ H.pCoreIn 2).relIndex B = 8 := by
    rw [inf_relIndex_left]
    change (Source.QH H).relIndex B = 8
    rw [←CriticalGeometry.starImage_card H B hBH]
    exact himage
  have hm := relIndex_mul_relIndex U0 (B ⊓ H.pCoreIn 2) B hU inf_le_left
  rw [hi,hindex] at hm
  have he : U0.relIndex (B ⊓ H.pCoreIn 2) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp he) hU

/-- A conjugate VH with the source kernel U0 forces K to centralize HC/VH.
The simple image and two-perfectness supply the source generation step. -/
theorem source_point_kernel_forces_centralization
    (H K HC VH B U0 : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hCH : HC ≤ H) (hVH : VH ≤ H)
    (hNC : H ≤ normalizer (HC : Set G)) (hNV : H ≤ normalizer (VH : Set G))
    (hCQ : HC ≤ H.pCoreIn 2) (hCB : HC ≤ normalizer (B : Set G))
    (hBH : B ≤ H) (hne : ¬ B ≤ H.pCoreIn 2)
    (hkernel : B ⊓ H.pCoreIn 2 = U0) (hUV : U0 ≤ VH) :
    ⁅HC,K⁆ ≤ VH := by
  have hBC : ⁅B,HC⁆ ≤ VH := by
    have hb : ⁅B,HC⁆ ≤ B := le_normalizer_iff_commutator_le_left.mp hCB
    have hc : ⁅B,HC⁆ ≤ HC := le_normalizer_iff_commutator_le_right.mp (hBH.trans hNC)
    exact (le_inf hb (hc.trans hCQ)).trans (hkernel.le.trans hUV)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup (LinearGroup 4) := (projectiveEquivLinear (by decide : 0<4)).symm.isSimpleGroup
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.isSimpleGroup
  let : (HC.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hNC
  let : (VH.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hNV
  have hK' : IsPPerfect 2 (K.subgroupOf H) := hK.of_surjective
    (subgroupOfEquivOfLe hKH).symm.toMonoidHom (subgroupOfEquivOfLe hKH).symm.surjective
  have hn : ¬ B.subgroupOf H ≤ (QuotientGroup.mk' (pCore 2 H)).ker := by
    intro hh
    apply hne
    have hm := map_mono (f := H.subtype) hh
    rwa [QuotientGroup.ker_mk',map_subgroupOf_eq_of_le hBH] at hm
  have hc' : ⁅B.subgroupOf H,HC.subgroupOf H⁆ ≤ VH.subgroupOf H := by
    apply (map_le_iff_le_comap).mp
    simpa only [map_commutator,map_subgroupOf_eq_of_le hBH,
      map_subgroupOf_eq_of_le hCH] using hBC
  have hc := commutator_le_of_nontrivial_simple_image
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (K.subgroupOf H) (HC.subgroupOf H) (VH.subgroupOf H) (B.subgroupOf H) hK' hc' hn
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hCH,
    map_subgroupOf_eq_of_le hVH,commutator_comm] at hm
  exact hm


/-- The specified source conjugate has the full point-radical image. Its
order-eight section identifies E with U0 and forces centralization of HC/VH. -/
theorem source_aligned_conjugate_centralizes [Finite G]
    (H K V V1 V2 V3 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G)) (hV1 : Nat.card V1 = 2)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hVH : Source.VH H V ≤ H) (hpVH : IsPGroup 2 (Source.VH H V))
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (g : G2 V2) (hg : (g:G) ∉ H)
    (hBH : (Source.VH H V).conjBy ((g:G)⁻¹) ≤ H)
    (hne : ¬ (Source.VH H V).conjBy ((g:G)⁻¹) ≤ H.pCoreIn 2)
    (hintersection : Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) =
      U0 (Source.UH H V3) V2)
    (hindex : (U0 (Source.UH H V3) V2).relIndex
      ((Source.VH H V).conjBy ((g:G)⁻¹)) = 8) :
    ⁅Source.HC H V3,K⁆ ≤ Source.VH H V := by
  let A := V1.conjBy ((g:G)⁻¹)
  let B := (Source.VH H V).conjBy ((g:G)⁻¹)
  have hAU : A ≤ Source.UH H V3 := by
    rintro _ ⟨x,hx,rfl⟩
    exact h2U ((mem_normalizer_iff.mp g⁻¹.property x).mp (h12 hx))
  have hAc : Nat.card A = 2 := by
    change Nat.card (V1.map _) = 2
    rw [card_map_of_injective (MulAut.conj _).injective,hV1]
  have hAZ : ¬ A ≤ V1 := by
    intro hh
    have he : A = V1 := eq_of_le_of_card_ge hh (by rw [hAc,hV1])
    have hn : (g:G)⁻¹ ∈ H := hH ▸ mem_normalizer_iff_map_conj_eq.mpr he
    exact hg (H.inv_mem_iff.mp hn)
  obtain ⟨u,hu,huZ⟩ := SetLike.not_le_iff_exists.mp hAZ
  have hP : normalizer (A : Set G) = H.conjBy ((g:G)⁻¹) := by
    rw [hH]
    exact (map_equiv_normalizer_eq V1 (MulAut.conj ((g:G)⁻¹))).symm
  have hBP : B ≤ normalizer (A : Set G) := by
    rw [hP]
    exact map_mono hVH
  have hnB : normalizer (A : Set G) ≤ normalizer (B : Set G) := by
    rw [hP]
    exact (map_mono (le_normalizer_conjugateSpanBy V H)).trans (le_normalizer_map _)
  have hHZ : H ≤ centralizer (V1 : Set G) := by
    rw [hH]
    exact normalizer_le_centralizer_of_card_two V1 hV1
  have hmove : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    exact hseed (bot_unique ((commutator_mono (le_conjugateSpanBy V3 H) le_rfl).trans_eq he))
  have himage := (source_point_image_radical H (Source.UH H V3) V1 A B ρ d e hact
    hHZ hV1 hcomm hmove hAc ⟨u,hAU hu⟩ hu huZ
    (hpVH.map _) hBH hBP hnB hne).2
  have hVQ : Source.VH H V ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hpVH hVH (le_normalizer_conjugateSpanBy V H)
  have hUV : U0 (Source.UH H V3) V2 ≤ Source.VH H V :=
    hintersection.symm.le.trans inf_le_left
  have hUB : U0 (Source.UH H V3) V2 ≤ B :=
    hintersection.symm.le.trans inf_le_right
  have hker := source_point_kernel_eq H B (U0 (Source.UH H V3) V2) hBH
    (le_inf hUB (hUV.trans hVQ)) hindex himage
  have hCQ : Source.HC H V3 ≤ H.pCoreIn 2 := by
    intro x hx
    let xH : H := ⟨x,hx.1⟩
    have he : e (QuotientGroup.mk' (pCore 2 H) xH) = 1 := by
      apply LinearEquiv.ext
      intro w
      change e (QuotientGroup.mk' (pCore 2 H) xH) w = w
      obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd w)
      have hw : (d.coordinates u).toAdd = w := congrArg Multiplicative.toAdd hu
      rw [←hw,←hact,←d.equivariant]
      apply congrArg (fun z => (d.coordinates z).toAdd)
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((hx.2 u u.property).symm)
    have hxQ : xH ∈ pCore 2 H :=
      (QuotientGroup.eq_one_iff xH).mp (e.injective (he.trans e.map_one.symm))
    exact mem_map_of_mem H.subtype hxQ
  have hNC : H ≤ normalizer (Source.HC H V3 : Set G) :=
    (le_inf H.le_normalizer (d.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hCB : Source.HC H V3 ≤ normalizer (B : Set G) :=
    (inf_le_right.trans ((centralizer_le hAU).trans
      (Subgroup.centralizer_le_normalizer _))).trans hnB
  exact source_point_kernel_forces_centralization H K (Source.HC H V3)
    (Source.VH H V) B (U0 (Source.UH H V3) V2) e hKH hK inf_le_left hVH
    hNC (le_normalizer_conjugateSpanBy V H) hCQ hCB hBH hne hker hUV


open CriticalGeometry NoncentralChiefRefinement
/-- Apply the point-parabolic calculation to the original critical pair.
The endpoint placement and nontrivial image are the earlier case-one
conclusions; the tensor intersection and its index are retained explicitly. -/
theorem source_critical_line_not_le_of_movement [Finite G]
    (L T H K V V1 V2 V3 : Subgroup G) (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G)) (hV1 : Nat.card V1 = 2)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hVH : Source.VH H V ≤ H) (hpVH : IsPGroup 2 (Source.VH H V))
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (hγH : c.Vgamma ≤ H) (hγQ : ¬ c.Vgamma ≤ H.pCoreIn 2)
    (g : G2 V2) (hg : (g:G) ∉ H)
    (hintersection : Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) =
      U0 (Source.UH H V3) V2)
    (hindex : (U0 (Source.UH H V3) V2).relIndex
      ((Source.VH H V).conjBy ((g:G)⁻¹)) = 8)
    (hmovement : ¬ ⁅Source.HC H V3,K⁆ ≤ Source.VH H V) :
    ¬ c.Aone V1 ≤ Source.UH H V3 := by
  intro hA
  obtain ⟨k,_,_,hk⟩ := source_critical_line_alignment L T H V V1 V2 V3 c
    ρ d e hact hH hV1 hcomm hseed hA hdisj h12 h2U g hg
  have hBH : (Source.VH H V).conjBy ((g:G)⁻¹) ≤ H := by
    rw [←hk]
    exact (map_mono hγH).trans_eq (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer k.property))
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hBQ : ¬ (Source.VH H V).conjBy ((g:G)⁻¹) ≤ H.pCoreIn 2 := by
    intro hh
    rw [←hk] at hh
    have hm := map_mono (f := (MulAut.conj ((k:G)⁻¹)).toMonoidHom) hh
    change (c.Vgamma.conjBy (k:G)).conjBy ((k:G)⁻¹) ≤
      (H.pCoreIn 2).conjBy ((k:G)⁻¹) at hm
    have hn : (H.pCoreIn 2).conjBy ((k:G)⁻¹) = H.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hnQ (H.inv_mem k.property))
    rw [conjBy_inv,hn] at hm
    exact hγQ hm
  exact hmovement (source_aligned_conjugate_centralizes H K V V1 V2 V3 ρ d e hact
    hH hV1 hcomm hseed hKH hK hVH hpVH h12 h2U g hg hBH hBQ hintersection hindex)

/-- The actual three-factor bound on the L0-intersection supplies the
movement contradiction for the same critical pair and the same conjugator. -/
theorem source_critical_line_not_le_of_chief_sections [Finite G]
    (L T H K D V V1 V2 V3 : Subgroup G) (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G)) (hV1 : Nat.card V1 = 2)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hVH : Source.VH H V ≤ H) (hpVH : IsPGroup 2 (Source.VH H V))
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (hγH : c.Vgamma ≤ H) (hγQ : ¬ c.Vgamma ≤ H.pCoreIn 2)
    (g : G2 V2) (hg : (g:G) ∉ H)
    (hintersection : Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) =
      U0 (Source.UH H V3) V2)
    (hindex : (U0 (Source.UH H V3) V2).relIndex
      ((Source.VH H V).conjBy ((g:G)⁻¹)) = 8)
    (hDK : D ≤ K) (Vn Cn : NormalNode D)
    (hVn : Vn.val = (Source.VH H V).subgroupOf D)
    (hCn : Cn.val = (Source.HC H V3).subgroupOf D)
    (hVC : Source.VH H V ≤ Source.HC H V3)
    (hthree : ∀ s : ChiefSeries D, s.head = Vn → s.last = Cn →
      3 ≤ s.noncentralTwoCount) :
    ¬ c.Aone V1 ≤ Source.UH H V3 :=
  source_critical_line_not_le_of_movement L T H K V V1 V2 V3 c ρ d e hact
    hH hV1 hcomm hseed hKH hK hVH hpVH h12 h2U hdisj hγH hγQ g hg hintersection hindex
    (source_component_moves_of_three_factors D K (Source.VH H V) (Source.HC H V3)
      hDK Vn Cn hVn hCn hVC hthree)


/-- The natural five-group, six-dimensional first tensor and orthogonal
section give the source index eight on the specified conjugate. -/
theorem source_tensor_conjugate_index [Finite G]
    {W E : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (H V V1 V2 V3 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (hV1 : Nat.card V1 = 2) (hV2 : Nat.card V2 = 4)
    (τ : Representation (ZMod 2) (G2 V2) W)
    (dt : BinaryConjugationSection (G2 V2) (U0 (Source.UH H V3) V2) V2 τ)
    (ht : Module.finrank (ZMod 2) W = 6)
    (ξ : Representation (ZMod 2) H E)
    (dx : BinaryConjugationSection H (Source.VH H V) (Source.UH H V3) ξ)
    (hx : Module.finrank (ZMod 2) E = 6)
    (g : G2 V2)
    (hU : U0 (Source.UH H V3) V2 ≤ (Source.VH H V).conjBy ((g:G)⁻¹)) :
    (U0 (Source.UH H V3) V2).relIndex ((Source.VH H V).conjBy ((g:G)⁻¹)) = 8 := by
  have hUH : Nat.card (Source.UH H V3) = 32 := by
    rw [d.card_section,hV1]
    norm_num
  have hU0 : Nat.card (U0 (Source.UH H V3) V2) = 256 := by
    rw [dt.card_section,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,ht,hV2]
    norm_num
  have hVH : Nat.card (Source.VH H V) = 2048 := by
    rw [dx.card_section,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hx,hUH]
    norm_num
  have hB : Nat.card ((Source.VH H V).conjBy ((g:G)⁻¹)) = 2048 := by
    change Nat.card ((Source.VH H V).map _) = _
    rw [card_map_of_injective (MulAut.conj _).injective,hVH]
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (U0 (Source.UH H V3) V2)
    ((Source.VH H V).conjBy ((g:G)⁻¹)) bot_le hU
  rw [relIndex_bot_left,relIndex_bot_left,hU0,hB] at hm
  omega

/-- Marked tensor and orthogonal sections discharge the index input in the
actual critical-pair/chief-section obstruction. The three-factor premise is
supplied by the existing cubic accounting on the literal L0-intersections. -/
theorem source_critical_line_not_le_of_marked_sections [Finite G]
    {W E : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (L T H K D V V1 V2 V3 : Subgroup G) (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G))
    (hV1 : Nat.card V1 = 2) (hV2 : Nat.card V2 = 4)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (hγH : c.Vgamma ≤ H) (hγQ : ¬ c.Vgamma ≤ H.pCoreIn 2)
    (g : G2 V2) (hg : (g:G) ∉ H)
    (hintersection : Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) =
      U0 (Source.UH H V3) V2)
    (τ : Representation (ZMod 2) (G2 V2) W)
    (dt : BinaryConjugationSection (G2 V2) (U0 (Source.UH H V3) V2) V2 τ)
    (ht : Module.finrank (ZMod 2) W = 6)
    (ξ : Representation (ZMod 2) H E)
    (dx : BinaryConjugationSection H (Source.VH H V) (Source.UH H V3) ξ)
    (hx : Module.finrank (ZMod 2) E = 6)
    (hDK : D ≤ K) (Vn Cn : NormalNode D)
    (hVn : Vn.val = (Source.VH H V).subgroupOf D)
    (hCn : Cn.val = (Source.HC H V3).subgroupOf D)
    (hthree : ∀ s : ChiefSeries D, s.head = Vn → s.last = Cn →
      3 ≤ s.noncentralTwoCount) :
    ¬ c.Aone V1 ≤ Source.UH H V3 := by
  have hindex := source_tensor_conjugate_index H V V1 V2 V3 ρ d hV1 hV2
    τ dt ht ξ dx hx g (hintersection.symm.le.trans inf_le_right)
  have hVC : Source.VH H V ≤ Source.HC H V3 := le_inf dx.section_le
    ((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (Source.VH H V)))).trans (centralizer_le dx.kernel_le))
  exact source_critical_line_not_le_of_chief_sections L T H K D V V1 V2 V3 c
    ρ d e hact hH hV1 hcomm hseed hKH hK dx.section_le
    (IsElementaryAbelian.isPGroup 2 (Source.VH H V)) h12 h2U hdisj hγH hγQ
    g hg hintersection hindex hDK Vn Cn hVn hCn hVC hthree

end CFSG.Quasithin.Chapter13.Section08.LinearFour
