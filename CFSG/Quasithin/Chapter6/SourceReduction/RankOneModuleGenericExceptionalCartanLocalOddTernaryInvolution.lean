module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOddTernaryRecognition
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SignedThree
/-!
# The canonical involution of the original odd-ternary residual

In each genuine odd-ternary containing row the preceding source reduction
identifies the literal residual image in Y/O₂(Y) with SL₂(5), and forces the
containing field parameter to be five. Its unique involution lies in the
center of the original Sylow image. The model bound on the derived
involution centralizer recovers that whole residual image, in all four
projective and central-cover rows.

Consequently its full ambient normalizer is the involution centralizer.
Perfect normalizer lifting through the original O₂(Y) identifies the
inverse image with the original relative residual normalizer. The same
source sieve therefore supplies an element of the entire original A ∩ Y
moving this involution, while the full Sylow and original right Hall fix it.
This is the concrete involution reduction for the remaining actor argument;
normalization by that entire actor, and the odd-ternary exclusion, remain open.

Source: Aschbacher--Smith A.3.21(a) and 5.1.13, printed pp.55,636
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
private theorem derived_bound_of_equiv {Y Z : Type*} [Group Y] [Group Z]
    (e : Y ≃* Z)
    (hb : ∀ z : Z, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Z))) ≤ 120) :
    ∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120 := by
  intro z hz
  let a := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e z
  have ha : (commutator (centralizer ({z} : Set Y))).map a.toMonoidHom =
      commutator (centralizer ({e z} : Set Z)) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective]
    rfl
  rw [Nat.card_congr ((a.subgroupMap (commutator (centralizer ({z} : Set Y)))).trans
    (MulEquiv.subgroupCongr ha)).toEquiv]
  exact hb (e z) ((e.orderOf_eq z).trans hz)

private theorem odd_ternary_five_bound {Q : Type*} [Group Q] [Finite Q]
    (hm : ClassicalGroup.IsPSL Q 3 5 ∨ ClassicalGroup.IsPSU Q 3 5 ∨
      IsSL Q 3 5 ∨ IsSU Q 3 5) :
    ∀ z : Q, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Q))) ≤ 120 := by
  open Theory.SpecificGroups.Classical.SylowMarkedSL2 in
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩ |
      ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  · apply derived_bound_of_equiv e
    let q := PSL3.projection F
    have hk : q.ker ≤ center SL(3,F) := by rw [PSL3.projection_ker]
    have hc : ∀ x ∈ q.ker, x^3 = 1 := by
      intro x hx
      exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
        ((_root_.orderOf_dvd_natCard (⟨x,hk hx⟩ : center SL(3,F))).trans
          (SL3.card_center_dvd_three F)))
    exact derived_centralizer_bound_of_central_cube_cover q (PSL3.projection_surjective F)
      hk hc (linear_derived_centralizer_card_le hF)
  · apply derived_bound_of_equiv e
    exact derived_centralizer_bound_of_central_cube_cover
      J.specialToProjective J.specialToProjective_surjective J.specialToProjective_ker_le_center
      (fun x hx => congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩))
      (unitary_derived_centralizer_card_le J hF hc)
  · exact derived_bound_of_equiv e (linear_derived_centralizer_card_le hF)
  · exact derived_bound_of_equiv e (unitary_derived_centralizer_card_le J hF hc)

variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem sl2_five_unique_involution (R : Subgroup G) (hR : IsSL R 2 5) :
    ∃ z : G, z ∈ R ∧ orderOf z = 2 ∧ ∀ x : G, x ∈ R → orderOf x = 2 → x = z := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hR
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide)
  let zR := e.symm (-1)
  have hz : orderOf zR = 2 := (e.symm.orderOf_eq _).trans
    (SpecialLinearGroup.orderOf_neg_one_eq_two h2)
  refine ⟨zR,zR.property,(orderOf_injective R.subtype R.subtype_injective zR).trans hz,?_⟩
  intro x hx hx2
  have ho : orderOf (e ⟨x,hx⟩) = 2 := (e.orderOf_eq _).trans
    ((orderOf_injective R.subtype R.subtype_injective ⟨x,hx⟩).symm.trans hx2)
  have hp : (e ⟨x,hx⟩)^2 = 1 := by simpa only [ho] using pow_orderOf_eq_one (e ⟨x,hx⟩)
  have hd : (SpecialLinearGroup.toGL (e ⟨x,hx⟩)).det = 1 := by
    apply Units.ext
    exact (e ⟨x,hx⟩).property
  have he : e ⟨x,hx⟩ = -1 := by
    rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
      (SpecialLinearGroup.toGL (e ⟨x,hx⟩)) (by rw [←map_pow,hp,map_one]) hd with he | he
    · have hh : e ⟨x,hx⟩ = 1 := SpecialLinearGroup.toGL_injective (by simpa using he)
      simp [hh] at ho
    · exact Subtype.ext (congrArg Units.val he)
  exact congrArg R.subtype (e.injective (he.trans (e.apply_symm_apply _).symm))

omit [Finite G] in
private theorem normalizer_le_centralizer_of_unique_involution
    (R : Subgroup G) (z : G) (hz : z ∈ R) (ho : orderOf z = 2)
    (hu : ∀ x : G, x ∈ R → orderOf x = 2 → x = z) :
    normalizer (R : Set G) ≤ centralizer ({z} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have he := hu (x*z*x⁻¹) ((mem_normalizer_iff.mp hx z).mp hz)
    (((MulAut.conj x).orderOf_eq z).trans ho)
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem sl2_five_derived_centralizer
    (C R : Subgroup G) (hRC : R ≤ C) (hR : IsSL R 2 5)
    (hb : ∀ z : C, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set C))) ≤ 120)
    (z : G) (hz : z ∈ R) (ho : orderOf z = 2)
    (hu : ∀ x : G, x ∈ R → orderOf x = 2 → x = z) :
    R = ⁅C ⊓ centralizer ({z} : Set G),C ⊓ centralizer ({z} : Set G)⁆ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hR
  let : Group.IsPerfect SL(2,F) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard : Nat.card R = 120 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hF]
    norm_num
  let zC : C := ⟨z,hRC hz⟩
  have hzC : orderOf zC = 2 := (orderOf_injective C.subtype C.subtype_injective zC).symm.trans ho
  have hc : (centralizer ({zC} : Set C)).map C.subtype = C ⊓ centralizer ({z} : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.property,?_⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg C.subtype (mem_centralizer_singleton_iff.mp ha))
    · rintro ⟨hx,hxz⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hxz))
  apply eq_of_le_of_card_ge
  · rw [←R.commutator_eq_self]
    have hle : R ≤ C ⊓ centralizer ({z} : Set G) := le_inf hRC
      (R.le_normalizer.trans (normalizer_le_centralizer_of_unique_involution R z hz ho hu))
    exact commutator_mono hle hle
  · rw [←hc,←map_commutator,card_map_of_injective C.subtype_injective,
      ←map_subtype_commutator,card_map_of_injective (centralizer ({zC} : Set C)).subtype_injective]
    exact (hb zC hzC).trans_eq hcard.symm

omit [Finite G] in
private theorem normalizer_eq_centralizer_of_derived
    (C R : Subgroup G) [C.Normal] (z : G) (hz : z ∈ R) (ho : orderOf z = 2)
    (hu : ∀ x : G, x ∈ R → orderOf x = 2 → x = z)
    (he : R = ⁅C ⊓ centralizer ({z} : Set G),C ⊓ centralizer ({z} : Set G)⁆) :
    normalizer (R : Set G) = centralizer ({z} : Set G) := by
  apply le_antisymm (normalizer_le_centralizer_of_unique_involution R z hz ho hu)
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq,he,map_commutator]
  have hn : (C ⊓ centralizer ({z} : Set G)).map (MulAut.conj x).toMonoidHom =
      C ⊓ centralizer ({z} : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp (inf_normalizer_le_normalizer_inf
      ⟨(show (⊤ : Subgroup G) ≤ normalizer (C : Set G) from le_normalizer_of_normal) (mem_top x),
        (centralizer ({z} : Set G)).le_normalizer hx⟩)
  rw [MulEquiv.toMonoidHom_eq_coe] at hn
  rw [hn]

/-- The four genuine odd-ternary rows recover the original residual image
from its unique involution. Its full relative normalizer is exactly that
involution's centralizer, with the original two-core map retained. -/
theorem residual_involution_of_odd_ternary
    {T : Sylow 2 G} {L W H Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (hHY : H ≤ Y)
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) :
    let q := QuotientGroup.mk' (pCore 2 Y)
    let Rbar := ((residual H).subgroupOf Y).map q
    let Cbar := C.map q
    let Tbar := ((T : Subgroup G).subgroupOf Y).map q
    ∃ z : Y ⧸ pCore 2 Y,
      z ∈ Rbar ∧ orderOf z = 2 ∧
      (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) ∧
      z ∈ Tbar ∧ Tbar ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) ∧
      Rbar = ⁅Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y)),
        Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y))⁆ ∧
      normalizer (Rbar : Set (Y ⧸ pCore 2 Y)) = centralizer ({z} : Set _) ∧
      (normalizer (residual H : Set G)).subgroupOf Y =
        (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q := by
  intro q Rbar Cbar Tbar
  obtain ⟨hp5,_,hsl⟩ := residual_section_of_odd_ternary h hH hgen hHY hR C hC hRC hp ho hm
  subst p
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let e := (cComponentTwoCoreQuotientEquiv hC).symm
  have hb : ∀ z : Cbar, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Cbar))) ≤ 120 :=
    derived_bound_of_equiv e (odd_ternary_five_bound hm)
  obtain ⟨z,hz,hz2,hu⟩ := sl2_five_unique_involution Rbar hsl
  have hder := sl2_five_derived_centralizer Cbar Rbar hle hsl hb z hz hz2 hu
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  have hnorm := normalizer_eq_centralizer_of_derived Cbar Rbar z hz hz2 hu hder
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hHY
  have hTN : Tbar ≤ normalizer (Rbar : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hTC : Tbar ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) := hTN.trans hnorm.le
  have hzT : z ∈ Tbar := by
    let P := (T.subtype (hH.1.1.2.trans hHY)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
    have hc : z ∈ centralizer (Tbar : Set (Y ⧸ pCore 2 Y)) := by
      apply mem_centralizer_iff.mpr
      intro t ht
      exact mem_centralizer_singleton_iff.mp (hTC ht)
    have h2 : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hz2,pow_one])
    have hP : (P : Subgroup (Y ⧸ pCore 2 Y)) = Tbar := rfl
    have hnz : z ∈ normalizer (Tbar : Set (Y ⧸ pCore 2 Y)) :=
      Subgroup.centralizer_le_normalizer (Tbar : Set (Y ⧸ pCore 2 Y)) hc
    have hh : z ∈ zpowers z ⊓ normalizer (P : Set (Y ⧸ pCore 2 Y)) := by
      change z ∈ zpowers z ⊓ normalizer ((P : Subgroup (Y ⧸ pCore 2 Y)) : Set _)
      rw [hP]
      exact ⟨mem_zpowers z,hnz⟩
    rw [h2.inf_normalizer_sylow P] at hh
    exact hh.2
  refine ⟨z,hz,hz2,hu,hzT,hTC,hder,hnorm,?_⟩
  rw [←residual_twoCore_normalizer h.qtke h.sylow_normalizes hH hgen hHY,hnorm]

/-- The entire original escaping Cartan intersection moves the distinguished
involution of the literal residual image. Both the right Hall and the full
original Sylow centralize it. -/
theorem odd_ternary_escape_moves_involution
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) :
    let q := QuotientGroup.mk' (pCore 2 Y)
    let Rbar := ((residual H).subgroupOf Y).map q
    let Cbar := C.map q
    let Tbar := ((T : Subgroup G).subgroupOf Y).map q
    ∃ z : Y ⧸ pCore 2 Y,
      z ∈ Rbar ∧ orderOf z = 2 ∧
      (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) ∧
      z ∈ Tbar ∧
      Tbar ⊔ (B.subgroupOf Y).map q ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) ∧
      Rbar = ⁅Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y)),
        Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y))⁆ ∧
      (normalizer (residual H : Set G)).subgroupOf Y =
        (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q ∧
      ∃ a : (A ⊓ Y : Subgroup G), q ⟨a.val,a.property.2⟩ * z * (q ⟨a.val,a.property.2⟩)⁻¹ ≠ z := by
  intro q Rbar Cbar Tbar
  obtain ⟨z,hz,hz2,hu,hzT,hTC,hder,hnorm,hnormY⟩ :=
    residual_involution_of_odd_ternary h hH hgen hY.2 hR C hC hCn hRC hp ho hm
  have hBC : (B.subgroupOf Y).map q ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) := by
    rw [←hnorm]
    exact (map_mono (comap_mono (Global.right_cartan_le_residual c))).trans Rbar.le_normalizer
  refine ⟨z,hz,hz2,hu,hzT,sup_le hTC hBC,hder,hnormY,?_⟩
  by_contra hfix
  apply hescape
  intro a ha
  have hh : q ⟨a,ha.2⟩ * z * (q ⟨a,ha.2⟩)⁻¹ = z := by
    by_contra hn
    exact hfix ⟨⟨a,ha⟩,hn⟩
  have hc : (⟨a,ha.2⟩ : Y) ∈ (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
  rw [←hnormY] at hc
  exact hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original sieve carries the canonical residual involution and an actual
element of the original Cartan intersection moving it in every odd-ternary row. -/
theorem localCartan_escape_seed_oddTernary_involution_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) →
          K = residual H ∧ p = 5 ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
            IsSL (((residual H).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 2 5 ∧
            Nat.card B = 3 ∧
            let q := QuotientGroup.mk' (pCore 2 Y)
            let Rbar := ((residual H).subgroupOf Y).map q
            let Cbar := C.map q
            let Tbar := ((T : Subgroup G).subgroupOf Y).map q
            ∃ z : Y ⧸ pCore 2 Y,
              z ∈ Rbar ∧ orderOf z = 2 ∧
              (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) ∧
              z ∈ Tbar ∧
              Tbar ⊔ (B.subgroupOf Y).map q ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) ∧
              Rbar = ⁅Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y)),
                Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y))⁆ ∧
              (normalizer (residual H : Set G)).subgroupOf Y =
                (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q ∧
              ∃ a : (A ⊓ Y : Subgroup G), q ⟨a.val,a.property.2⟩ * z * (q ⟨a.val,a.property.2⟩)⁻¹ ≠ z) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd⟩ :=
    localCartan_escape_seed_oddTernary_section_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,?_⟩
  intro p hp ho hm
  obtain ⟨he,hp5,hfour,hsl,hB⟩ := hOdd p hp ho hm
  exact ⟨he,hp5,hfour,hsl,hB,
    LocalSieve.odd_ternary_escape_moves_involution h hH hgen c hY hescape
      (he ▸ hKL) C hC hCn (he ▸ hKC) hp ho hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
