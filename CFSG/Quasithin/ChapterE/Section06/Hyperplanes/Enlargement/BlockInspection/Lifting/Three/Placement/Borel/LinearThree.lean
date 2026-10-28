module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel.LocalAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional.ModelCentralizers
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCorePrimeToIndex
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SpecificGroups.KleinFourResidualAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.ElementaryAbelian.AbelianNormalClosure

set_option linter.style.haveILetI false

/-!
# Triviality of the marked action on PSL₃(4)

The marked involution identifies its centralizer with the specified Sylow
2-subgroup, so the whole actor normalizes that Sylow subgroup. Its center is
a Klein four. Two-perfection and the marked nonidentity fixed point force the
block to centralize this center. Subnormality puts the Sylow–block commutator
in the elementary image of U(D); the commuting-action fixed-point lemma and
commutator idempotence then make it trivial. The pointwise Sylow-fixer theorem
puts the remaining action in a two-group, where two-perfection kills it.
Faithful descent through the center handles the perfect central covers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8 and
E.6.23, printed pp.247–248 and 254–255; C.1.7–12, pp.123–124.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional

/-- The actual alternating quotient has order three. -/
private theorem alternatingThree_quotient_card {D : Type*} [Group D]
    (h : IsAlternatingBlock D 3) : Nat.card (D ⧸ pCore 2 D) = 3 := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

/-- Two-perfection removes the central two-kernel above the cyclic quotient. -/
private theorem alternatingThree_core_eq_blockU {D : Type*} [Group D]
    (h : IsAlternatingBlock D 3) : pCore 2 D = blockU D := by
  let : Finite D := h.2.1.finite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := alternatingThree_quotient_card h
  let : IsCyclic (D ⧸ pCore 2 D) := isCyclic_of_prime_card hcard
  let f : (D ⧸ blockU D) →* (D ⧸ pCore 2 D) :=
    QuotientGroup.map (blockU D) (pCore 2 D) (MonoidHom.id D) blockU_le_core
  have hk : f.ker = (pCore 2 D).map (QuotientGroup.mk' (blockU D)) := by
    exact QuotientGroup.ker_map (blockU D) (pCore 2 D) (MonoidHom.id D) blockU_le_core
  have hi : Function.Injective f :=
    f.injective_of_isPPerfect_of_coprime_abelian_image
      (h.2.1.quotient_twoPerfect (blockU D))
      (by rw [hk]; exact blockU_core_image_le_center)
      (by rw [hk]; exact pCore_isPGroup.map _)
      (fun _ _ => mul_comm' _ _) (by decide : Nat.Coprime 2 3)
      (fun x => by simpa only [hcard] using (pow_card_eq_one' (x := f x)))
  apply le_antisymm _ blockU_le_core
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  exact (QuotientGroup.eq_one_iff x).mpr hx

private theorem center_eq_bot_of_isPSL {X : Type*} [Group X]
    (hm : ClassicalGroup.IsPSL X 3 4) : center X = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  letI : Fintype F := Fintype.ofFinite F
  letI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Atlas.sl_perfect 3 (by decide)
  have hc : center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa using congrArg e (mem_center_iff.mp hx z)
  rw [hc, mem_bot] at he
  exact e.injective (he.trans (map_one e).symm)

private theorem isKleinFour_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) [IsKleinFour H] : IsKleinFour G where
  card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two

private theorem isKleinFour_map {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) [IsKleinFour A] (f : G →* H)
    (hf : Function.Injective f) : IsKleinFour (A.map f) :=
  isKleinFour_of_equiv (A.equivMapOfInjective f hf).symm

private theorem center_sylow_isKleinFour {X : Type*} [Group X] [Finite X]
    (hm : ClassicalGroup.IsPSL X 3 4) (S : Sylow 2 X) :
    IsKleinFour (center S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  letI : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := by
    have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
      rw [← Nat.card_eq_fintype_card, hF])
    exact ringChar.of_eq hc
  letI : CharP F 2 := hchar
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let eS : S ≃* R :=
    (S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
  let eR : R ≃* Matrix.PSL3.LinearThree.unipotent F :=
    R.equiv (Matrix.PSL3.LinearThree.unipotentSylow F (n := 2) (by decide) hF)
  letI : IsElementaryAbelian 2 (Matrix.PSL3Even.UnipotentGeometry.Z F) := by
    apply IsElementaryAbelian.of_le (B := Matrix.PSL3Even.UnipotentGeometry.V₁ F)
    intro z hz
    rw [Matrix.PSL3Even.UnipotentGeometry.mem_V₁,
      Matrix.PSL3Even.UnipotentGeometry.mem_Z] at *
    exact hz.2
  have hZcard : Nat.card (Matrix.PSL3Even.UnipotentGeometry.Z F) = 4 := by
    rw [Matrix.PSL3Even.UnipotentGeometry.card_Z, hF]

  letI : Nontrivial (Matrix.PSL3Even.UnipotentGeometry.Z F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : IsKleinFour (Matrix.PSL3Even.UnipotentGeometry.Z F) := {
    card_four := hZcard
    exponent_two := IsElementaryAbelian.exponent_eq_prime
  }
  letI : IsKleinFour (center (Matrix.PSL3Even.UnipotentGeometry.U F)) := by
    rw [← Matrix.PSL3Even.UnipotentGeometry.Z_eq_center F]
    infer_instance
  letI : IsKleinFour (center (Matrix.PSL3.LinearThree.unipotent F)) :=
    isKleinFour_of_equiv
      (centerCongr (Matrix.PSL3.LinearThree.unipotentEquiv F)).symm
  letI : IsKleinFour (center R) := isKleinFour_of_equiv (centerCongr eR)
  exact isKleinFour_of_equiv (centerCongr eS)

private theorem linear_three_action_centerless
    {X : Type*} [Group X] [Finite X]
    (hm : ClassicalGroup.IsPSL X 3 4) (hcenter : center X = ⊥) :
    FixedSylowActionTrivial X := by
  intro H D _ _ _ _ hD ι hι hsub ρ S hS t ht ht2 hfix
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := by
    intro ht1
    exact ht (ht1 ▸ (center X).one_mem)
  have hcent : IsPGroup 2 (centralizer ({t} : Set X)) :=
    linear_four_centralizer_isTwoGroup hm t ht1 ht2
  have hScent : (S : Subgroup X) ≤ centralizer ({t} : Set X) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    obtain ⟨a, ha⟩ := hS s hs
    have hh := hfix a
    rw [ha] at hh
    exact mul_inv_eq_iff_eq_mul.mp (by simpa only [MulAut.conj_apply] using hh)
  have hct : centralizer ({t} : Set X) = (S : Subgroup X) :=
    S.is_maximal' hcent hScent
  have hmapS (a : H) : (S : Subgroup X).map (ρ a).toMonoidHom = S := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [← hct] at hx ⊢
      change (ρ a) x ∈ centralizer ({t} : Set X)
      rw [mem_centralizer_singleton_iff]
      have hx' : x * t = t * x := mem_centralizer_singleton_iff.mp hx
      have hh := congrArg (ρ a) hx'
      simpa only [map_mul, hfix a] using hh
    · rintro y hy
      let β : MulAut X := (ρ a).symm
      refine ⟨β y, ?_, ?_⟩
      · rw [← hct] at hy ⊢
        change β y ∈ centralizer ({t} : Set X)
        rw [mem_centralizer_singleton_iff]
        have hy' : y * t = t * y := mem_centralizer_singleton_iff.mp hy
        have hh := congrArg β hy'
        have hfixinv : β t = t := by
          have hh := congrArg β (hfix a)
          simpa only [β, MulEquiv.symm_apply_apply] using hh.symm
        rw [map_mul, map_mul, hfixinv] at hh
        exact hh
      · exact MulEquiv.apply_symm_apply (ρ a) y
  let Y := ρ.range
  let rρ := ρ.rangeRestrict
  let f := rρ.comp ι
  let B : Subgroup Y := f.range
  let inner : X →* MulAut X := MulAut.conj
  let I : Subgroup (MulAut X) := (S : Subgroup X).map inner
  have hIY : I ≤ Y := by
    rintro z ⟨s, hs, rfl⟩
    exact hS s hs
  let Q : Subgroup Y := I.subgroupOf Y
  have hQp : IsPGroup 2 Q := by
    let hI : IsPGroup 2 I := (S.isPGroup').map inner
    exact hI.of_equiv (Subgroup.subgroupOfEquivOfLe hIY).symm
  have hconj (a : MulAut X) (z : X) :
      MulAut.conj (a z) = a * MulAut.conj z * a⁻¹ := by
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
      map_mul, map_inv]
    rw [MulEquiv.apply_symm_apply]
  have hYQ : (⊤ : Subgroup Y) ≤ normalizer (Q : Set Y) := by
    intro a ha
    obtain ⟨a0, ha0⟩ := a.property
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hqI : (q : MulAut X) ∈ I := mem_subgroupOf.mp hq
      obtain ⟨z, hz, hzq⟩ := mem_map.mp hqI
      apply mem_subgroupOf.mpr
      apply mem_map.mpr
      have hzs : (ρ a0) z ∈ (S : Subgroup X) := by
        rw [← hmapS a0]
        exact ⟨z, hz, rfl⟩
      refine ⟨(ρ a0) z, hzs, ?_⟩
      change MulAut.conj ((ρ a0) z) =
        (a : MulAut X) * (q : MulAut X) * (a : MulAut X)⁻¹
      rw [← hzq, ← ha0]
      exact hconj (ρ a0) z
    · intro hq
      have hqI : (a * q * a⁻¹ : Y) ∈ I.subgroupOf Y := hq
      have hqI' : ((a * q * a⁻¹ : Y) : MulAut X) ∈ I := mem_subgroupOf.mp hqI
      obtain ⟨z, hz, hzr⟩ := mem_map.mp hqI'
      apply mem_subgroupOf.mpr
      apply mem_map.mpr
      refine ⟨(ρ a0).symm z, ?_, ?_⟩
      · have hzmap : z ∈ (S : Subgroup X).map (ρ a0).toMonoidHom :=
          (hmapS a0).symm ▸ hz
        obtain ⟨s, hs, hsmap⟩ := hzmap
        have hsz : s = (ρ a0).symm z := by
          rw [← hsmap]
          simp
        exact hsz ▸ hs
      · have hqeq : (q : MulAut X) = (ρ a0)⁻¹ * MulAut.conj z * ρ a0 := by
          have hzr' : MulAut.conj z =
              (a : MulAut X) * (q : MulAut X) * (a : MulAut X)⁻¹ := hzr
          calc
            (q : MulAut X) = (a : MulAut X)⁻¹ *
                ((a : MulAut X) * (q : MulAut X) * (a : MulAut X)⁻¹) * (a : MulAut X) := by group
            _ = (a : MulAut X)⁻¹ * MulAut.conj z * (a : MulAut X) := by rw [← hzr']
            _ = (ρ a0)⁻¹ * MulAut.conj z * ρ a0 := by rw [← ha0]
        rw [hqeq]
        exact hconj (ρ a0).symm z
  have hBQ : B ≤ normalizer (Q : Set Y) := fun b hb => hYQ (show b ∈ (⊤ : Subgroup Y) from trivial)
  have hBsub : B.IsSubnormal := by
    have hh : (ι.range.map rρ).IsSubnormal :=
      hsub.map (MonoidHom.rangeRestrict_surjective ρ)
    simpa only [f, B, MonoidHom.range_comp] using hh
  have hBP : IsPPerfect 2 B := by
    exact hD.2.1.twoPerfect.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hinj : Function.Injective (inner : X →* MulAut X) := by
    apply (MonoidHom.ker_eq_bot_iff inner).mp
    apply le_bot_iff.mp
    intro x hx
    have hc : x ∈ center X := by
      rw [mem_center_iff]
      intro y
      have hy := congrArg (fun a : MulAut X => a y) hx
      change x * y * x⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    rw [hcenter, mem_bot] at hc
    exact hc
  let iS : S ≃* I :=
    (S : Subgroup X).equivMapOfInjective inner hinj
  let iQ : I ≃* Q := (Subgroup.subgroupOfEquivOfLe hIY).symm
  let iSQ : S ≃* Q := iS.trans iQ
  letI : IsKleinFour (center S) := center_sylow_isKleinFour hm S
  letI : IsKleinFour (center Q) :=
    isKleinFour_of_equiv (centerCongr iSQ).symm
  let Z : Subgroup Y := (center Q).map Q.subtype
  have hBZ : B ≤ normalizer (Z : Set Y) :=
    hBQ.trans (normalizer_le_normalizer_characteristic_image Q (center Q))
  let act : B →* MulAut Z :=
    Z.normalizerMonoidHom.comp (Subgroup.inclusion hBZ)
  have htS : t ∈ (S : Subgroup X) := by
    rw [← hct]
    rw [mem_centralizer_singleton_iff]
  let itY : Y := ⟨inner t, hIY (mem_map.mpr ⟨t, htS, rfl⟩)⟩
  have htQ : itY ∈ Q := by
    apply mem_subgroupOf.mpr
    exact mem_map.mpr ⟨t, htS, rfl⟩
  have htZ : itY ∈ Z := by
    apply mem_map.mpr
    refine ⟨⟨itY, htQ⟩, ?_, rfl⟩
    rw [mem_center_iff]
    intro q
    obtain ⟨s, hs, hseq⟩ := mem_map.mp (mem_subgroupOf.mp q.property)
    have hst : s * t = t * s := by
      exact mem_centralizer_singleton_iff.mp (hScent hs)
    apply Subtype.ext
    apply Subtype.ext
    change ((q : Y) : MulAut X) * (itY : MulAut X) =
      (itY : MulAut X) * ((q : Y) : MulAut X)
    rw [← hseq]
    simpa only [map_mul] using congrArg inner hst
  let zt : Z := ⟨itY, htZ⟩
  have hzt1 : zt ≠ 1 := by
    intro hz
    apply ht1
    apply hinj
    simpa [zt, itY] using congrArg (fun z : Z => ((z : Y) : MulAut X)) hz
  have hactfix : ∀ b : B, act b zt = zt := by
    intro b
    have hbmem : (b : Y) ∈ f.range := by
      exact b.property
    let d : D := Classical.choose hbmem
    have hdb : f d = (b : Y) := Classical.choose_spec hbmem
    apply Subtype.ext
    change (b : Y) * (zt : Y) * (b : Y)⁻¹ = (zt : Y)
    have hbval : (b : Y) = f d := hdb.symm
    rw [hbval]
    apply Subtype.ext
    change ((f d : Y) : MulAut X) * ((itY : Y) : MulAut X) *
        ((f d : Y) : MulAut X)⁻¹ = (itY : Y)
    change (ρ (ι d)) * inner t * (ρ (ι d))⁻¹ = inner t
    rw [← hconj, hfix (ι d)]
  letI : IsKleinFour Z :=
    isKleinFour_map (center Q) Q.subtype Q.subtype_injective
  have hact : act = 1 :=
    IsKleinFour.action_eq_one_of_twoPerfect_of_fixed_ne_one act hBP hzt1 hactfix
  have hZcentral : Z ≤ centralizer (B : Set Y) := by
    intro z hz b hb
    have hh := congrArg (fun a : MulAut Z => a ⟨z, hz⟩)
      (DFunLike.congr_fun hact ⟨b, hb⟩)
    have hh' := congrArg Subtype.val hh
    change b * (z : Y) * b⁻¹ = (z : Y) at hh'
    exact mul_inv_eq_iff_eq_mul.mp hh'
  let fB : D →* B := f.rangeRestrict
  let W : Subgroup B := (blockU D).map fB
  letI : IsElementaryAbelian 2 (blockU D) := hD.2.1.elementary
  letI : IsElementaryAbelian 2 W := IsElementaryAbelian.map fB
  have hUindex : (blockU D).index = 3 := by
    rw [← alternatingThree_core_eq_blockU hD]
    exact alternatingThree_quotient_card hD
  have hWindex : W.index ∣ (blockU D).index :=
    Subgroup.index_map_dvd (blockU D) f.rangeRestrict_surjective
  have hWodd : ¬ 2 ∣ W.index := by
    intro htwo
    have htwo' : 2 ∣ (blockU D).index := htwo.trans hWindex
    rw [hUindex] at htwo'
    norm_num at htwo'
  have hpW : pCore 2 B ≤ W := by
    have hh := pCore_le_map_pCore_of_prime_not_dvd_index W hWodd
    have hWtop : IsPGroup 2 (⊤ : Subgroup W) :=
      (IsElementaryAbelian.isPGroup 2 W).of_equiv Subgroup.topEquiv.symm
    have htop : pCore 2 W = ⊤ := by
      apply top_unique
      exact le_sSup ⟨(inferInstance : (⊤ : Subgroup W).Normal),
        hWtop⟩
    have hmaptop : (⊤ : Subgroup W).map W.subtype = W := by
      apply le_antisymm (map_subtype_le _)
      intro w hw
      exact mem_map.mpr ⟨⟨w, hw⟩, mem_top _, rfl⟩
    rw [htop, hmaptop] at hh
    exact hh
  let W' : Subgroup Y := W.map B.subtype
  let C : Subgroup Y := ⁅Q, B⁆
  have hCW : C ≤ W' := by
    have hc := Subgroup.commutator_le_core_commutator_of_isSubnormal B Q hBsub hBP hQp hBQ
    exact hc.trans (Subgroup.map_mono ((commutator_le_left _ _).trans hpW))
  letI : IsElementaryAbelian 2 W' := IsElementaryAbelian.map B.subtype
  letI : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCW
  have hCcomm : C ≤ centralizer (C : Set Y) := by
    intro c hc d hd
    exact congrArg Subtype.val (mul_comm' (⟨d, hd⟩ : C) (⟨c, hc⟩ : C))
  have hCQ : C ≤ Q := le_normalizer_iff_commutator_le_left.mp hBQ
  have hCZ : C ⊓ centralizer (Q : Set Y) ≤ Z := by
    rintro c ⟨hc, hcq⟩
    refine ⟨⟨c, hCQ hc⟩, ?_, rfl⟩
    change (⟨c, hCQ hc⟩ : Q) ∈ center Q
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (hcq q q.property)
  have hCB : ⁅C, B⁆ = ⊥ := IsPPerfect.centralizes_of_commuting_fixed
    B Q C hBP hQp (normalizer_commutator_ge_right Q B)
      (normalizer_commutator_ge_left Q B) hCcomm
      (commutator_eq_bot_iff_le_centralizer.mpr (hCZ.trans hZcentral))
  have hCbot : C = ⊥ := by
    exact (Subgroup.commutator_isPPerfect_idempotent B Q hBP hQp hBQ).symm.trans hCB
  have hQcentral : Q ≤ centralizer (B : Set Y) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact hCbot
  have hBfix : ∀ b : B, ∀ s : X, s ∈ (S : Subgroup X) →
      ((b : Y) : MulAut X) s = s := by
    intro b s hs
    have hsi : inner s ∈ I := mem_map.mpr ⟨s, hs, rfl⟩
    let sy : Y := ⟨inner s, hIY hsi⟩
    have hsq : sy ∈ Q := mem_subgroupOf.mpr hsi
    have hcomm := mem_centralizer_iff.mp (hQcentral hsq) b b.property
    let α : MulAut X := ((b : Y) : MulAut X)
    have hc : α * inner s = inner s * α :=
      congrArg (fun y : Y => (y : MulAut X)) hcomm
    have hinner : inner (α s) = inner s := by
      change MulAut.conj (α s) = inner s
      rw [hconj, hc, mul_inv_cancel_right]
    exact hinj hinner
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let K0 : Subgroup X := (center S).map (S : Subgroup X).subtype
  let K : Subgroup (MulAut X) := K0.map inner
  have hKI : K ≤ I := by
    intro a ha
    obtain ⟨z, hz, hza⟩ := mem_map.mp ha
    obtain ⟨s, hs, hsz⟩ := mem_map.mp hz
    apply mem_map.mpr
    exact ⟨(s : X), s.property, (congrArg inner hsz).trans hza⟩
  have hKXY : K ≤ Y := hKI.trans hIY
  let L : Subgroup Y := K.subgroupOf Y
  have hBL : B ≤ L := by
    intro b hb
    obtain ⟨z, hz, hbz⟩ :=
      Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv F
        (n := 2) (by decide) hF e S ((b : Y) : MulAut X)
        (fun s hs => hBfix ⟨b, hb⟩ s hs)
    apply mem_subgroupOf.mpr
    exact mem_map.mpr ⟨z, hz, hbz.symm⟩
  have hLp : IsPGroup 2 L := by
    let hKp0 : IsPGroup 2 K0 :=
      (S.isPGroup'.to_subgroup (center S)).map (S : Subgroup X).subtype
    exact hKp0.map inner |>.of_equiv (Subgroup.subgroupOfEquivOfLe hKXY).symm
  have hBpg : IsPGroup 2 B := by
    exact (hLp.to_subgroup (B.subgroupOf L)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hBL)
  have hBbot : B = ⊥ := by
    have hid : (MonoidHom.id B) = 1 := hBP.hom_eq_one_of_isPGroup hBpg (MonoidHom.id B)
    apply le_bot_iff.mp
    intro b hb
    have heq := DFunLike.congr_fun hid ⟨b, hb⟩
    exact mem_bot.mpr (by simpa using heq)
  have hf : f = 1 := by
    apply MonoidHom.ext
    intro d
    have hd' : f d ∈ B := ⟨d, rfl⟩
    have hd : f d ∈ (⊥ : Subgroup Y) := by rw [← hBbot]; exact hd'
    have heq := mem_bot.mp hd
    exact heq
  apply MonoidHom.ext
  intro d
  have heq := congrArg Subtype.val (DFunLike.congr_fun hf d)
  simpa [f, rρ] using heq

/-- Every marked A₃ action on an actual PSL₃(4) component is trivial. -/
theorem linearThree_projective_fixedSylowActionTrivial {X : Type*} [Group X] [Finite X]
    (hm : ClassicalGroup.IsPSL X 3 4) : FixedSylowActionTrivial X := by
  exact linear_three_action_centerless hm (center_eq_bot_of_isPSL hm)

/-- Automorphism actions on a perfect central cover descend faithfully. The
marked involution stays noncentral because the projective quotient is centerless.
No restriction on the order of the center is needed for this reduction. -/
theorem linearThree_cover_fixedSylowActionTrivial
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hm : ClassicalGroup.IsPSL (X ⧸ center X) 3 4) :
    FixedSylowActionTrivial X := by
  intro H D _ _ _ _ hD ι hι hsub ρ S hS t ht ht2 hfix
  let q := QuotientGroup.mk' (center X)
  let a := MulAut.centralQuotientAction (MulEquiv.refl (X ⧸ center X))
  let β := a.comp ρ
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSbar : ∀ s ∈ (Sbar : Subgroup (X ⧸ center X)),
      MulAut.conj s ∈ β.range := by
    rintro s ⟨x, hx, rfl⟩
    obtain ⟨h, hh⟩ := hS x hx
    refine ⟨h, ?_⟩
    change a (ρ h) = MulAut.conj (q x)
    rw [hh]
    exact MulAut.centralQuotientAction_conj (MulEquiv.refl _) x
  have htbar : q t ∉ center (X ⧸ center X) := by
    rw [center_eq_bot_of_isPSL hm, mem_bot]
    exact fun he => ht ((QuotientGroup.eq_one_iff t).mp he)
  have htbar2 : q t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hfixbar (h : H) : β h (q t) = q t := by
    change a (ρ h) (q t) = q t
    exact (MulAut.centralQuotientAction_apply (MulEquiv.refl _) (ρ h) t).trans
      (congrArg q (hfix h))
  have he := linearThree_projective_fixedSylowActionTrivial hm
    H D hD ι hι hsub β Sbar hSbar (q t) htbar htbar2 hfixbar
  apply MonoidHom.ext
  intro d
  apply MulAut.centralQuotientAction_injective (MulEquiv.refl (X ⧸ center X))
  have hd := DFunLike.congr_fun he d
  simpa only [β, a, MonoidHom.comp_apply, MonoidHom.one_apply, map_one] using hd

/-- The complete parameter-four linear branch of the Borel model action,
including every quasisimple central two-cover supplied by E.6.8(1). -/
theorem linearThree_fixedSylowActionTrivial {X : Type*} [Group X] [Finite X]
    (hq : IsQuasisimple X)
    (hm : ClassicalGroup.IsPSL X 3 4 ∨
      (IsPGroup 2 (center X) ∧ ClassicalGroup.IsPSL (X ⧸ center X) 3 4)) :
    FixedSylowActionTrivial X := by
  letI : IsQuasisimple X := hq
  rcases hm with hm | ⟨_, hm⟩
  · exact linearThree_projective_fixedSylowActionTrivial hm
  · exact linearThree_cover_fixedSylowActionTrivial hm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
