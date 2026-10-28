module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryPermutationAlternatingActions
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import Theory.Representation.G2BinaryFixedBounds

/-!
# Fixed-space bounds for the ordinary A₇ and binary G₂ blocks

A subgroup of index at most two in an A₇ Sylow fixes at most eight vectors
on its natural six-space. Sylow conjugacy reduces this to the explicit
order-eight permutation subgroup. Two distinct nonidentity elements already
have at most eight common fixed vectors in the augmentation core; the
finite calculation checks only the eight Sylow words and 128 binary vectors.

For G₂(2)′, the existing octonion calculation bounds Sylow fixed points by
two. Both bounds are transported through the literal intrinsic two-core
quotient and module marking. Disjointness from the center makes projection
of the original subgroup into the block module injective.

The Chapter12 SixSpaceBlocks consumer applies these bounds to the original
residual four-space and its Sylow fixed subgroup. It keeps the ordinary
six-dimensional A₇ module separate from the exceptional four-space, and
G₂(2)′ separate from the full G₂(2) group.
Source: Aschbacher--Smith, proof of Proposition 7.7.3 after Lemma 7.7.10,
printed p.709, refs/quasithin.pdf; block conventions are C.1.12 and C.1.30.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySixSpaceBlocks
open AlternatingSeven.DihedralLocals

private def commonVectors (i j : Fin 8) : Finset (Fin 7 → ZMod 2) :=
  Finset.univ.filter fun v => (∑ k, v k) = 0 ∧
    (∀ k, v ((tWord i)⁻¹ k) = v k) ∧ (∀ k, v ((tWord j)⁻¹ k) = v k)

private theorem commonVectors_card (i j : Fin 8) (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) : (commonVectors i j).card ≤ 8 := by
  revert hi hj hij
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem fixed_marked_card (R : Subgroup A7) (hR : R ≤ fixedTwoGroup)
    (hcard : 4 ≤ Nat.card R) :
    Nat.card (fixedSpace (alternatingCoreRepresentation (Fin 7)) R) ≤ 8 := by
  classical
  let : Fintype R := Fintype.ofFinite R
  obtain ⟨a,b,c,hab,hac,hbc⟩ := Fintype.two_lt_card_iff.mp
    (show 2 < Fintype.card R by rw [←Nat.card_eq_fintype_card]; omega)
  let x : R := a⁻¹*b
  let y : R := a⁻¹*c
  have hx : x ≠ 1 := by intro he; exact hab (inv_mul_eq_one.mp he)
  have hy : y ≠ 1 := by intro he; exact hac (inv_mul_eq_one.mp he)
  have hxy : x ≠ y := by intro he; exact hbc (mul_left_cancel he)
  obtain ⟨i,hi⟩ := hR x.property
  obtain ⟨j,hj⟩ := hR y.property
  change tWord i = x.val.val at hi
  change tWord j = y.val.val at hj
  have hi0 : i ≠ 0 := by
    intro he
    subst i
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact hi.symm
  have hj0 : j ≠ 0 := by
    intro he
    subst j
    apply hy
    apply Subtype.ext
    apply Subtype.ext
    exact hj.symm
  have hij : i ≠ j := by
    intro he
    apply hxy
    exact Subtype.ext (Subtype.ext (hi.symm.trans (he ▸ hj)))
  let f : fixedSpace (alternatingCoreRepresentation (Fin 7)) R →
      {v // v ∈ commonVectors i j} := fun v => ⟨v.val.val,by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,v.val.property,?_,?_⟩
    · intro k
      have hh := congrArg (fun w : core (Fin 7) => w.val k) (v.property x)
      change v.val.val ((x.val.val)⁻¹ k) = v.val.val k at hh
      rwa [←hi] at hh
    · intro k
      have hh := congrArg (fun w : core (Fin 7) => w.val k) (v.property y)
      change v.val.val ((y.val.val)⁻¹ k) = v.val.val k at hh
      rwa [←hj] at hh⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {v // v ∈ commonVectors i j} => z.val) he
  exact (Nat.card_le_card_of_injective f hf).trans (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using commonVectors_card i j hi0 hj0 hij)

/-- A subgroup of index at most two in an A₇ Sylow fixes at most an
order-eight subgroup of the natural six-space. -/
theorem seven_half_sylow_fixed_card (P : Sylow 2 A7) (Q : Subgroup A7)
    (hindex : Q.relIndex (P : Subgroup A7) ≤ 2) :
    Nat.card (fixedSpace (alternatingCoreRepresentation (Fin 7)) Q) ≤ 8 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 fixedSylow P
  have hP : (P : Subgroup A7) = fixedTwoGroup.map (MulAut.conj g).toMonoidHom :=
    (congrArg Sylow.toSubgroup hg).symm
  have hPg : (P : Subgroup A7).map (MulAut.conj g⁻¹).toMonoidHom = fixedTwoGroup := by
    rw [hP,map_map]
    have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id A7 := by
      apply MonoidHom.ext
      intro a
      change g⁻¹*(g*a*g⁻¹)*(g⁻¹)⁻¹ = a
      group
    rw [hc,map_id]
  have hPc : Nat.card P = 8 := by
    rw [hP,card_map_of_injective (MulAut.conj g).injective,fixedTwoGroup_card]
  let R := Q ⊓ (P : Subgroup A7)
  have hRc : 4 ≤ Nat.card R := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup A7) R (P : Subgroup A7) bot_le inf_le_right
    simp only [relIndex_bot_left,R,inf_relIndex_right] at he
    rw [hPc] at he
    nlinarith
  let R₀ := R.map (MulAut.conj g⁻¹).toMonoidHom
  have hR₀ : R₀ ≤ fixedTwoGroup := hPg ▸ map_mono (show R ≤ (P : Subgroup A7) from inf_le_right)
  have hR₀c : 4 ≤ Nat.card R₀ := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hRc
  have hh := fixed_marked_card R₀ hR₀ hR₀c
  rw [←Nat.card_congr (fixedSpaceConjEquiv (alternatingCoreRepresentation (Fin 7)) R g⁻¹).toEquiv] at hh
  let f : fixedSpace (alternatingCoreRepresentation (Fin 7)) Q →
      fixedSpace (alternatingCoreRepresentation (Fin 7)) R :=
    Submodule.inclusion (by intro v hv r; exact hv ⟨r,r.property.1⟩)
  exact (Nat.card_le_card_of_injective f (Submodule.inclusion_injective _)).trans hh

private theorem image_relIndex_le {X Y : Type*} [Group X] [Finite X] [Group Y]
    (f : X →* Y) (Q P : Subgroup X) : (Q.map f).relIndex (P.map f) ≤ Q.relIndex P := by
  rw [←relIndex_comap]
  exact relIndex_le_of_le_left (le_comap_map f Q) index_ne_zero_of_finite

/-- Literal central-quotient transport of the A₇ bound to a block. -/
theorem seven_block_fixed_card {L : Type*} [Group L] [Finite L]
    (hb : ChapterC.IsAlternatingBlock L 7) (S : Sylow 2 L) (Q D : Subgroup L)
    (hindex : Q.relIndex (S : Subgroup L) ≤ 2)
    (hDU : D ≤ ChapterC.blockU L) (hDZ : Disjoint D (center L))
    (hDQ : D ≤ centralizer (Q : Set L)) : Nat.card D ≤ 8 := by
  obtain ⟨_,_,r,⟨m⟩,hm⟩ := hb
  let q : L →* A7 := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  have hi : (Q.map q).relIndex (P : Subgroup A7) ≤ 2 := by
    change (Q.map q).relIndex ((S : Subgroup L).map q) ≤ 2
    exact (image_relIndex_le q Q (S : Subgroup L)).trans hindex
  let f : D →* Multiplicative (natural (Fin 7)) := m.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (ChapterC.blockFixed L)).comp (inclusion hDU))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro d hd
    change f d = 1 at hd
    have hz : QuotientGroup.mk' (ChapterC.blockFixed L) (inclusion hDU d) = 1 :=
      m.moduleIso.injective (by change f d = m.moduleIso 1; simpa only [map_one] using hd)
    have hc : (d : L) ∈ center L := (QuotientGroup.eq_one_iff (inclusion hDU d)).mp hz
    have hh : (d : L) ∈ D ⊓ center L := ⟨d.property,hc⟩
    rw [hDZ.eq_bot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  let e := coreEquivNatural (Fin 7) (by decide)
  let j : D → fixedSpace (alternatingCoreRepresentation (Fin 7)) (Q.map q) := fun d =>
    ⟨e.symm (f d).toAdd,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      apply e.injective
      rw [e.apply_symm_apply]
      change e (coreRepresentation (Fin 7) a.val.val _) = _
      rw [coreEquivNatural_equivariant,e.apply_symm_apply]
      have hd : ChapterC.blockConjugate L l (inclusion hDU d) = inclusion hDU d := by
        apply Subtype.ext
        change l*(d : L)*l⁻¹ = (d : L)
        rw [hDQ d.property l hl,mul_inv_cancel_right]
      have hh := congrArg Multiplicative.toAdd (m.intertwining l (inclusion hDU d))
      rw [hd,hm] at hh
      change (f d).toAdd = alternatingNaturalRepresentation (Fin 7) (q l) (f d).toAdd at hh
      rw [he] at hh
      exact hh.symm⟩
  have hj : Function.Injective j := by
    intro x y he
    apply hf
    apply Multiplicative.toAdd.injective
    exact e.symm.injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective j hj).trans (seven_half_sylow_fixed_card P (Q.map q) hi)

/-- A Sylow fixes at most two elements in a subgroup embedded in the
natural binary G₂ block module. The quotient actor is G₂(2)′. -/
theorem g2_block_sylow_fixed_card {L : Type*} [Group L] [Finite L]
    (hb : ChapterC.IsG2TwoBlock L) (S : Sylow 2 L) (D : Subgroup L)
    (hDU : D ≤ ChapterC.blockU L) (hDZ : Disjoint D (center L))
    (hDS : D ≤ centralizer (S : Set L)) : Nat.card D ≤ 2 := by
  obtain ⟨_,r,⟨m⟩,hm⟩ := hb
  let q : L →* commutator (Atlas.G2.Model (ZMod 2)) :=
    m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  let : Finite (Atlas.G2.Natural.Space (ZMod 2)) := Finite.of_injective
    (fun v => m.moduleIso.symm (Multiplicative.ofAdd v))
    (m.moduleIso.symm.injective.comp Multiplicative.ofAdd.injective)
  let f : D →* Multiplicative (Atlas.G2.Natural.Space (ZMod 2)) := m.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (ChapterC.blockFixed L)).comp (inclusion hDU))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro d hd
    change f d = 1 at hd
    have hz : QuotientGroup.mk' (ChapterC.blockFixed L) (inclusion hDU d) = 1 :=
      m.moduleIso.injective (by change f d = m.moduleIso 1; simpa only [map_one] using hd)
    have hc : (d : L) ∈ center L := (QuotientGroup.eq_one_iff (inclusion hDU d)).mp hz
    have hh : (d : L) ∈ D ⊓ center L := ⟨d.property,hc⟩
    rw [hDZ.eq_bot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  let j : D → fixedSpace (g2DerivedNatural (ZMod 2)) (P : Subgroup _) := fun d =>
    ⟨(f d).toAdd,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      have hd : ChapterC.blockConjugate L l (inclusion hDU d) = inclusion hDU d := by
        apply Subtype.ext
        change l*(d : L)*l⁻¹ = (d : L)
        rw [hDS d.property l hl,mul_inv_cancel_right]
      have hh := congrArg Multiplicative.toAdd (m.intertwining l (inclusion hDU d))
      rw [hd,hm] at hh
      change (f d).toAdd = g2DerivedNatural (ZMod 2) (q l) (f d).toAdd at hh
      rw [he] at hh
      exact hh.symm⟩
  have hj : Function.Injective j := by
    intro x y he
    apply hf
    exact Multiplicative.toAdd.injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective j hj).trans
    (Atlas.G2.Natural.BinarySylowFixedSpace.card_derived_sylow_fixed_le_two P)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySixSpaceBlocks
