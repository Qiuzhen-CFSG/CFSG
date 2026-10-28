module
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.GroupTheory.TwoPerfectCubicKernel
public import Theory.GroupTheory.PPerfectCubicImage

/-!
# Cubic residuals in a binary two-factor wreath product

No two-perfect subgroup of SL₃(2) ≀ C₂ with cubic two-core quotient is
normalized by a Sylow two-subgroup of the whole wreath product. The
coordinate interchange makes both coordinate images nontrivial. Independent
coordinate Sylow elements force the commutator of one image into the
two-group kernel of the other image, contradicting commutator generation
of the cubic residual.

This supplies the intrinsic two-factor obstruction in the proof of
Aschbacher–Smith 12.7.16, while retaining the supplied Sylow subgroup.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Two.WreathPair

private theorem right_eq_one (J : Subgroup Actor) (hJ : IsPPerfect 2 J)
    (j : J) : j.val.right = 1 := by
  have hp : IsPGroup 2 Bit := IsPGroup.of_card (n := 1) (Nat.card_zmod 2)
  exact DFunLike.congr_fun (hJ.hom_eq_one_of_isPGroup hp
    ((RegularWreathProduct.rightHom : Actor →* Bit).comp J.subtype)) j

private def coordinate (J : Subgroup Actor) (hJ : IsPPerfect 2 J) (i : Bit) : J →* SL where
  toFun j := j.val.left i
  map_one' := rfl
  map_mul' a b := by simp [right_eq_one J hJ a]

private theorem coordinate_ne_one (J : Subgroup Actor) (hJ : IsPPerfect 2 J)
    (hc : Nat.card (J ⧸ pCore 2 J) = 3)
    (hn : borel ≤ normalizer (J : Set Actor)) (i : Bit) : coordinate J hJ i ≠ 1 := by
  intro hz
  have hleft (j : J) (k : Bit) : j.val.left k = 1 := by
    let q : Bit := i * k⁻¹
    let w : Actor := RegularWreathProduct.inl q
    have hw : w ∈ borel := fun _ => one_mem _
    have hm : w * j.val * w⁻¹ ∈ J :=
      (mem_normalizer_iff.mp (hn hw) j.val).mp j.property
    have hh := DFunLike.congr_fun hz (⟨_,hm⟩ : J)
    change (w * j.val * w⁻¹).left i = 1 at hh
    simpa [w,q,coordinate,right_eq_one J hJ j] using hh
  have hbot : J = ⊥ := by
    apply bot_unique
    intro j hj
    apply mem_bot.mpr
    apply RegularWreathProduct.ext
    · exact funext (hleft ⟨j,hj⟩)
    · exact right_eq_one J hJ ⟨j,hj⟩
  have hd := card_quotient_dvd_card (pCore 2 J)
  rw [hc] at hd
  rw [hbot,card_bot] at hd
  norm_num at hd

private def single (i : Bit) (s : SL) : Actor := ⟨Pi.mulSingle i s,1⟩

private theorem single_mem (i : Bit) (s : SL) (hs : s ∈ borelSL) : single i s ∈ borel := by
  intro k
  by_cases hk : i = k
  · subst k
    simpa [single] using hs
  · simp [single,Pi.mulSingle_eq_of_ne (Ne.symm hk)]

private theorem coordinate_normalized (J : Subgroup Actor) (hJ : IsPPerfect 2 J)
    (hn : borel ≤ normalizer (J : Set Actor)) (i : Bit) :
    borelSL ≤ normalizer ((coordinate J hJ i).range : Set SL) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a,⟨j,rfl⟩,rfl⟩
    let w := single i s
    have hw : w ∈ normalizer (J : Set Actor) := hn (single_mem i s hs)
    have hm : w * j.val * w⁻¹ ∈ J := (mem_normalizer_iff.mp hw j.val).mp j.property
    refine ⟨⟨_,hm⟩,?_⟩
    change (w*j.val*w⁻¹).left i = s * j.val.left i * s⁻¹
    simp [w,single,right_eq_one J hJ j]
  · rw [card_map_of_injective (MulAut.conj s).injective]

private theorem standard_obstruction (J : Subgroup Actor) (hJ : IsPPerfect 2 J)
    (hc : Nat.card (J ⧸ pCore 2 J) = 3)
    (hn : borel ≤ normalizer (J : Set Actor)) : False := by
  classical
  let i : Bit := 1
  let k : Bit := Multiplicative.ofAdd (1 : ZMod 2)
  have hik : i ≠ k := by decide +kernel
  let p := coordinate J hJ i
  let q := coordinate J hJ k
  have hpne : p ≠ 1 := coordinate_ne_one J hJ hc hn i
  have hqne : q ≠ 1 := coordinate_ne_one J hJ hc hn k
  have hqp : IsPGroup 2 q.ker := q.kernel_isTwoGroup_of_twoPerfect_cubic hJ hc hqne
  let K := q.ker.map p
  have hK : IsPGroup 2 K := hqp.map p
  have hcomm : ⁅p.range,borelSL⁆ ≤ K := by
    apply commutator_le.mpr
    rintro a ⟨j,rfl⟩ s hs
    let w := single i s
    have hw : w ∈ borel := single_mem i s hs
    have hm : ⁅j.val,w⁆ ∈ J :=
      le_normalizer_iff_commutator_le_left.mp hn
        (commutator_mem_commutator j.property hw)
    let c : J := ⟨⁅j.val,w⁆,hm⟩
    have hck : c ∈ q.ker := by
      change (⁅j.val,w⁆).left k = 1
      simp [commutatorElement_def,w,single,right_eq_one J hJ j,hik.symm]
    refine mem_map.mpr ⟨c,hck,?_⟩
    change (⁅j.val,w⁆).left i = ⁅j.val.left i,s⁆
    simp [commutatorElement_def,w,single,right_eq_one J hJ j]
  have hp : IsPPerfect 2 p.range := hJ.of_surjective p.rangeRestrict p.rangeRestrict_surjective
  have hpc : Nat.card (p.range ⧸ pCore 2 p.range) = 3 :=
    Theory.GroupTheory.cubic_core_quotient_of_twoPerfect_image hJ hc
      p.rangeRestrict p.rangeRestrict_surjective (by
        intro he
        apply hpne
        apply MonoidHom.ext
        intro j
        exact congrArg Subtype.val (DFunLike.congr_fun he j))
  let S : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL,card_SL]
    decide +kernel)
  have he : ⁅p.range,borelSL⁆ = p.range :=
    ResidualRecognition.commutator_sylow_eq p.range S hp hpc
      (coordinate_normalized J hJ hn i)
  have hp2 : IsPGroup 2 p.range := hK.to_le (he ▸ hcomm)
  have hz := hJ.hom_eq_one_of_isPGroup hp2 p.rangeRestrict
  apply hpne
  apply MonoidHom.ext
  intro j
  exact congrArg Subtype.val (DFunLike.congr_fun hz j)

/-- A full Sylow subgroup cannot normalize a two-perfect cubic residual. -/
theorem not_sylow_normalized_cubic_residual (J : Subgroup Actor) (S : Sylow 2 Actor)
    (hJ : IsPPerfect 2 J) (hc : Nat.card (J ⧸ pCore 2 J) = 3)
    (hn : (S : Subgroup Actor) ≤ normalizer (J : Set Actor)) : False := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor S sylow
  let e := MulAut.conj g
  let J' := J.map e.toMonoidHom
  let eJ : J ≃* J' := J.equivMapOfInjective e.toMonoidHom e.injective
  have hJ' : IsPPerfect 2 J' := hJ.of_surjective eJ.toMonoidHom eJ.surjective
  have hc' : Nat.card (J' ⧸ pCore 2 J') = 3 := by
    rw [←Nat.card_congr (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)).toEquiv]
    exact hc
  have he : (S : Subgroup Actor).map e.toMonoidHom = borel :=
    (congrArg Sylow.toSubgroup hg).trans sylow_eq
  have hn' : borel ≤ normalizer (J' : Set Actor) :=
    he ▸ (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  exact standard_obstruction J' hJ' hc' hn'
end Matrix.PSL3Two.WreathPair
