module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.Reciprocal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.Duality

/-!
# Restricted characters and the two rank-three core axes

The perfect F.9.7 pairing is used on the literal relative subgroups of `H`.
A displacement character of an automorphism of the literal commutator is
factored through its point quotient, extended across the radical embedding,
and represented by an actual element of the literal two-core.  The reciprocal
axis is transported through the actual source conjugator.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
14.7.70, printed pp.1073--1074 (PDF pp.1090--1091), using F.9.7.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree

open Subgroup Representation Chapter12.Section08
open scoped commutatorElement IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem restricted_axis_of_duality
    (d : Data T L V F W) (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (A : Subgroup G)
    (hAB : A ≤ F.U) (hPB : F.Vi 1 ≤ F.U) (hPA : F.Vi 1 ≤ A)
    (hPcentralB : F.Vi 1 ≤ centralizer (F.U : Set G))
    (hPcentralQ : F.Vi 1 ≤ centralizer (F.H.pCoreIn 2 : Set G))
    (hrad : A ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1) :
    RealizesAxis A (F.Vi 1) (F.H.pCoreIn 2) := by
  let := (original_U_pairing_conditions d).1
  let := (original_U_pairing_conditions d).2
  obtain ⟨eZ, e, heval⟩ := original_commutator_duality d h21
  have hPN : ((F.Vi 1).subgroupOf A).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hPA).mpr
    exact hAB.trans ((le_centralizer_iff.mp hPcentralB).trans (_root_.centralizer_le_normalizer _))
  let := hPN
  let := d.U_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAB
  intro f hdisp hfix
  let delta : A →* F.Vi 1 := {
    toFun := fun x => ⟨(f x : G) * (x : G)⁻¹, hdisp x⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change (f (x * y) : G) * ((x * y : A) : G)⁻¹ =
        ((f x : G) * (x : G)⁻¹) * ((f y : G) * (y : G)⁻¹)
      rw [map_mul]
      change (f x : G) * (f y : G) * ((x : G) * (y : G))⁻¹ = _
      rw [mul_inv_rev]
      have hc0 : (x : G) * ((f y : G) * (y : G)⁻¹) =
          ((f y : G) * (y : G)⁻¹) * (x : G) :=
        mem_centralizer_iff.mp (hPcentralB (hdisp y)) (x : G) (hAB x.property)
      have hc : Commute (x : G)⁻¹ ((f y : G) * (y : G)⁻¹) := by
        exact (show Commute (x : G) ((f y : G) * (y : G)⁻¹) from hc0).inv_left
      calc
        _ = (f x : G) * ((f y : G) * (y : G)⁻¹) * (x : G)⁻¹ := by group
        _ = (f x : G) * ((x : G)⁻¹ * ((f y : G) * (y : G)⁻¹)) := by
          simpa [mul_assoc] using congrArg (fun z : G => (f x : G) * z) hc.eq.symm
        _ = _ := by group }
  have hdeltaP : ((F.Vi 1).subgroupOf A) ≤ delta.ker := by
    intro x hx
    apply Subtype.ext
    change (f (x : A) : G) * (x : G)⁻¹ = 1
    rw [hfix (x : A) hx]
    simp
  let deltaQ : (A ⧸ (F.Vi 1).subgroupOf A) →* F.Vi 1 :=
    QuotientGroup.lift ((F.Vi 1).subgroupOf A) delta hdeltaP
  let deltaH : F.Vi 1 →* (F.Vi 1).subgroupOf F.H := {
    toFun := fun x =>
      let xH : F.H := ⟨(x : G), d.conjugationSection.section_le (hPB x.property)⟩
      ⟨xH, x.property⟩
    map_one' := by rfl
    map_mul' := by intro x y; rfl }
  let char : (A ⧸ (F.Vi 1).subgroupOf A) →* Multiplicative (ZMod 2) :=
    eZ.toMonoidHom.comp (deltaH.comp deltaQ)
  let : IsElementaryAbelian 2 (A ⧸ (F.Vi 1).subgroupOf A) :=
    IsElementaryAbelian.quotient ((F.Vi 1).subgroupOf A)
  let charLin : Additive (A ⧸ (F.Vi 1).subgroupOf A) →ₗ[ZMod 2] ZMod 2 :=
    (MonoidHom.binaryCharacterEquivLinearDual char).toAdd
  let C : Subgroup (F.U.subgroupOf F.H) :=
    (centralizer ((pCore 2 F.H : Subgroup F.H) : Set F.H)).subgroupOf
      (F.U.subgroupOf F.H)
  let i : A →* (F.U.subgroupOf F.H) := {
    toFun := fun x => ⟨⟨(x : G), d.conjugationSection.section_le (hAB x.property)⟩,
      hAB x.property⟩
    map_one' := by rfl
    map_mul' := by intro x y; rfl }
  let phi : A →* ((F.U.subgroupOf F.H) ⧸ C) :=
    (QuotientGroup.mk' C).comp i
  have hphiP : ((F.Vi 1).subgroupOf A) ≤ phi.ker := by
    intro x hx
    change QuotientGroup.mk' C (i (x : A)) = 1
    apply (QuotientGroup.eq_one_iff (N := C) (i (x : A))).mpr
    change (i (x : A) : F.H) ∈ centralizer (pCore 2 F.H : Set F.H)
    intro q hq
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hPcentralQ (show (x : G) ∈ F.Vi 1 from hx)) (q : G)
      (mem_map.mpr ⟨q, hq, rfl⟩))
  let j : (A ⧸ (F.Vi 1).subgroupOf A) →* ((F.U.subgroupOf F.H) ⧸ C) :=
    QuotientGroup.lift ((F.Vi 1).subgroupOf A) phi hphiP
  have hphiKer : phi.ker = (F.Vi 1).subgroupOf A := by
    apply le_antisymm
    · intro x hx
      have hxC : (x : G) ∈ centralizer (F.H.pCoreIn 2 : Set G) := by
        have hx' := (QuotientGroup.eq_one_iff (N := C) (i x)).mp hx
        have hxH : (i x : F.H) ∈ centralizer (pCore 2 F.H : Set F.H) := hx'
        intro q hq
        obtain ⟨qH', hqH', rfl⟩ := mem_map.mp hq
        have hh := congrArg (fun z : F.H => (z : G))
          (mem_centralizer_iff.mp hxH (qH' : F.H) hqH')
        simpa [i] using hh
      have hxP : (x : G) ∈ F.Vi 1 := by
        have : (x : G) ∈ A ⊓ centralizer (F.H.pCoreIn 2 : Set G) := ⟨x.property, hxC⟩
        rwa [hrad] at this
      exact hxP
    · exact hphiP
  have hj : Function.Injective j :=
    (QuotientGroup.injective_lift_iff ((F.Vi 1).subgroupOf A) phi hphiP).mpr hphiKer.symm
  let jlin : Additive (A ⧸ (F.Vi 1).subgroupOf A) →ₗ[ZMod 2]
      Additive ((F.U.subgroupOf F.H) ⧸ C) :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditiveLeft j)
  have hjlin : Function.Injective jlin := by
    intro x y hxy
    apply Additive.ofMul.injective
    apply hj
    exact congrArg Additive.toMul hxy
  let erange := LinearEquiv.ofInjective jlin hjlin
  let charRange : LinearMap.range jlin →ₗ[ZMod 2] ZMod 2 :=
    charLin.comp erange.symm.toLinearMap
  obtain ⟨charFull, hcharFull⟩ := LinearMap.exists_extend charRange
  obtain ⟨qbar, hqbar⟩ := e.surjective (by simpa [C] using (Multiplicative.ofAdd charFull))
  obtain ⟨qH, hqH⟩ := QuotientGroup.mk'_surjective _ qbar
  have hchar_x (x : A) :
      charFull (Additive.ofMul (QuotientGroup.mk' C (i x))) =
        charLin (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x)) := by
    have hx := LinearMap.congr_fun hcharFull
      (jlin.rangeRestrict (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x)))
    have hx' : charFull (jlin (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x))) =
        charRange (jlin.rangeRestrict (Additive.ofMul
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x))) := hx
    calc
      _ = charFull (jlin (Additive.ofMul
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x))) := by rfl
      _ = _ := hx'
      _ = _ := by
        have her : erange.symm (jlin.rangeRestrict
            (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x))) =
            Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x) := by
          change erange.symm (erange _) = _
          exact erange.left_inv _
        change charLin (erange.symm (jlin.rangeRestrict
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x)))) = _
        rw [her]
  have hchar_delta (x : A) :
      charLin (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x)) =
        (eZ (deltaH (delta x))).toAdd := by
    rfl
  have hchar_q (x : A) :
      (e (QuotientGroup.mk' _ qH)).toAdd
          (Additive.ofMul (QuotientGroup.mk' C (i x))) =
        (eZ (deltaH (delta x))).toAdd := by
    calc
      _ = (e qbar).toAdd (Additive.ofMul (QuotientGroup.mk' C (i x))) := by rw [hqH]
      _ = charFull (Additive.ofMul (QuotientGroup.mk' C (i x))) := by
        rw [hqbar]
        rfl
      _ = charLin (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf A) x)) :=
        hchar_x x
      _ = _ := hchar_delta x
  have hcomm_delta (x : A) :
      (f x : G) * (x : G)⁻¹ = (qH : G) * (x : G) * (qH : G)⁻¹ * (x : G)⁻¹ := by
    let xH : F.U.subgroupOf F.H := i x
    have he := heval qH xH
    have he' := hchar_q x
    have hz : eZ (deltaH (delta x)) =
        eZ ⟨⁅(qH : F.H), (xH : F.H)⁆, by
          change ⁅((qH : F.H) : G), ((xH : F.H) : G)⁆ ∈ F.Vi 1
          rw [← h21, commutator_comm]
          exact commutator_mem_commutator (mem_map_of_mem F.H.subtype qH.property) xH.property⟩ := by
      apply Multiplicative.toAdd.injective
      simpa [C, i] using he'.symm.trans he
    have hz' := eZ.injective hz
    have hz'' := congrArg (fun z : (F.Vi 1).subgroupOf F.H => (z : G)) hz'
    change (f x : G) * (x : G)⁻¹ = ⁅(qH : G), (x : G)⁆ at hz''
    simpa only [commutatorElement_def] using hz''
  have hformula (x : A) :
      (qH : G) * (x : G) * (qH : G)⁻¹ = (f x : G) := by
    calc
      (qH : G) * (x : G) * (qH : G)⁻¹ =
          ((qH : G) * (x : G) * (qH : G)⁻¹ * (x : G)⁻¹) * (x : G) := by group
      _ = ((f x : G) * (x : G)⁻¹) * (x : G) := by rw [← hcomm_delta]
      _ = (f x : G) := by group
  refine ⟨(qH : G), ?_, ?_, ?_⟩
  · exact mem_map.mpr ⟨qH, qH.property, rfl⟩
  · rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      simp [hformula ⟨y, hy⟩]
    · intro hy
      let z : A := ⟨(qH : G) * y * (qH : G)⁻¹, hy⟩
      obtain ⟨x, hx⟩ := f.surjective z
      have he := hformula x
      have he' : (qH : G) * (x : G) * (qH : G)⁻¹ =
          (qH : G) * y * (qH : G)⁻¹ := by simpa [z, hx] using he
      have hxy : (x : G) = y := by
        have hh := congrArg (fun w : G => (qH : G)⁻¹ * w * (qH : G)) he'
        simpa [mul_assoc] using hh
      simpa [hxy] using x.property
  · intro x
    exact hformula x

theorem restricted_axes
    (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (h : Preliminary d c) (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    CoreAxes c := by
  have hFUH : F.U ≤ F.H := d.conjugationSection.section_le
  have hpointU : F.Vi 1 ≤ centralizer (F.U : Set G) := by
    apply le_centralizer_iff.mpr
    rw [point_centralizer d]
    exact hFUH
  have hpointQ : F.Vi 1 ≤ centralizer (F.H.pCoreIn 2 : Set G) :=
    (point_le_core_centralizer d).trans inf_le_right
  have horiginal : RealizesAxis (Fcomm c) (F.Vi 1) (F.H.pCoreIn 2) :=
    restricted_axis_of_duality d h21 (Fcomm c)
      (Fcomm_le_U d c h.earlier) d.conjugationSection.kernel_le h.point_le
      hpointU hpointQ (h.commutator_inf_core_centralizer s h21)

  let Aα : Subgroup G := conjugate (Fcomm c) c.conjugator⁻¹
  have hUα : conjugate c.Uα c.conjugator⁻¹ = F.U := by
    simpa only [CriticalPath.Uα, inv_inv] using
      conjugate_conjugate_inv F.U c.conjugator⁻¹
  have hAαU : Aα ≤ F.U := by
    exact (map_mono (h.commutator_le.trans inf_le_right)).trans_eq hUα
  have hPα : F.Vi 1 ≤ Aα := by
    have hp := map_mono (f := (MulAut.conj (c.conjugator⁻¹)⁻¹).toMonoidHom)
      h.opposite_le
    change conjugate c.Zα c.conjugator⁻¹ ≤ Aα at hp
    have hZ : conjugate c.Zα c.conjugator⁻¹ = F.Vi 1 := by
      simpa only [CriticalPath.Zα, inv_inv] using
        conjugate_conjugate_inv (F.Vi 1) c.conjugator⁻¹
    exact hZ ▸ hp
  have hradα : Aα ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 := by
    apply le_antisymm
    · have hle : Aα ⊓ centralizer (F.H.pCoreIn 2 : Set G) ≤
          Aα ⊓ d.U₀ :=
        le_inf inf_le_left ((inf_le_inf hAαU le_rfl).trans
          (core_centralizer_le_U₀ d s h21))
      have hrec := h.reciprocal_commutator_inf_fixed s a ha t ht hmark
      change Aα ⊓ d.U₀ = F.Vi 1 at hrec
      exact hle.trans_eq hrec
    · exact le_inf hPα hpointQ
  have hacore : RealizesAxis Aα (F.Vi 1) (F.H.pCoreIn 2) :=
    restricted_axis_of_duality d h21 Aα hAαU d.conjugationSection.kernel_le hPα
      hpointU hpointQ hradα
  refine ⟨horiginal, ?_⟩
  intro f hdisp hfix
  let eA : Fcomm c ≃* Aα := {
    toFun := fun x => ⟨c.conjugator * (x : G) * c.conjugator⁻¹, by
      exact ⟨(x : G), x.property, by simp [mul_assoc]⟩⟩
    invFun := fun y => ⟨c.conjugator⁻¹ * (y : G) * c.conjugator, by
      obtain ⟨x, hx, he⟩ := y.property
      rw [← he]
      simpa [mul_assoc] using hx⟩
    left_inv := by intro x; apply Subtype.ext; simp [mul_assoc]
    right_inv := by intro y; apply Subtype.ext; simp [mul_assoc]
    map_mul' := by intro x y; apply Subtype.ext; simp [mul_assoc] }
  let fα : MulAut Aα := eA.symm.trans (f.trans eA)
  have hZ : conjugate c.Zα c.conjugator⁻¹ = F.Vi 1 := by
    simpa only [CriticalPath.Zα, inv_inv] using
      conjugate_conjugate_inv (F.Vi 1) c.conjugator⁻¹
  have hdispα : ∀ y : Aα, (fα y : G) * (y : G)⁻¹ ∈ F.Vi 1 := by
    intro y
    let x : Fcomm c := eA.symm y
    have hx := hdisp x
    have hmap : (c.conjugator * ((f x : G) * (x : G)⁻¹) * c.conjugator⁻¹) ∈
        conjugate c.Zα c.conjugator⁻¹ := ⟨(f x : G) * (x : G)⁻¹, hx, by
          simp [mul_assoc]⟩
    rw [hZ] at hmap
    simpa [fα, eA, x, mul_inv_rev, mul_assoc] using hmap
  have hfixα : ∀ y : Aα, (y : G) ∈ F.Vi 1 → fα y = y := by
    intro y hy
    let x : Fcomm c := eA.symm y
    have hxZ : (x : G) ∈ c.Zα := by
      have hZ' : conjugate (F.Vi 1) c.conjugator = c.Zα := by
        rw [← hZ]
        exact conjugate_conjugate_inv c.Zα c.conjugator
      rw [← hZ']
      exact ⟨(y : G), hy, by
        change (MulAut.conj c.conjugator⁻¹) (y : G) = (x : G)
        rw [MulAut.conj_apply]
        simp [x, eA, mul_assoc]⟩
    have hfx : f x = x := hfix x hxZ
    apply eA.symm.injective
    simpa [fα, x] using hfx
  obtain ⟨q0, hq0, hq0norm, hq0formula⟩ := hacore fα hdispα hfixα
  let qα : G := c.conjugator⁻¹ * (q0 : G) * c.conjugator
  have hQα : qα ∈ c.Qα := by
    have hQ : conjugate (F.H.pCoreIn 2) c.conjugator = c.Qα := by
      exact map_pCoreIn_of_injective 2 F.H _ (MulAut.conj _).injective
    rw [← hQ]
    exact ⟨q0, hq0, by simp [qα, mul_assoc]⟩
  have hformulaα : ∀ x : Fcomm c,
      qα * (x : G) * qα⁻¹ = (f x : G) := by
    intro x
    let y : Aα := eA x
    have hy := hq0formula y
    have hh := congrArg (fun z : G => c.conjugator⁻¹ * z * c.conjugator) hy
    simpa [qα, y, eA, fα, mul_assoc] using hh
  have hnormα : qα ∈ normalizer (Fcomm c : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hformulaα ⟨y, hy⟩]
      exact (f ⟨y, hy⟩).property
    · intro hy
      let z : Fcomm c := ⟨qα * y * qα⁻¹, hy⟩
      obtain ⟨x, hx⟩ := f.surjective z
      have he := hformulaα x
      have he' : qα * (x : G) * qα⁻¹ = qα * y * qα⁻¹ := by simpa [z, hx] using he
      have hh := congrArg (fun w : G => qα⁻¹ * w * qα) he'
      have hxy : (x : G) = y := by simpa [mul_assoc] using hh
      change y ∈ Fcomm c
      rw [← hxy]
      exact x.property
  exact ⟨qα, hQα, hnormα, hformulaα⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
