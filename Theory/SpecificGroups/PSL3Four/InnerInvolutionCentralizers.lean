module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.FourElementField
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.PSL3Four.InnerInvolutionCentralizers.UnipotentCubic


/-!
# Inner involution centralizers in PSL₃(4)

Conjugation faithfully identifies PSL₃(4) with its inner automorphism group.
Every projective involution is conjugate to the highest-root element, whose
full projective centralizer is the faithfully embedded UT₃(F₄). Consequently
the relative inner centralizer in the actual automorphism group has order 64.

For a commuting nonidentity cubic automorphism, conjugate the involution to
the marked root and restrict the automorphism to this unitriangular group.
The restriction remains nonidentity: the proved pointwise Sylow-fixer theorem
identifies its kernel with highest-root conjugations, which have exponent two.
The common inner centralizer is transported to the fixed subgroup of this
literal coordinate action. The local UT₃(F₄) calculation identifies that fixed
subgroup with the order-four center, giving the common-centralizer bound.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137 (PDF p.1154),
`refs/quasithin.pdf`; the matrix automorphisms used by the Sylow-fixer theorem
are those of GLS3, Theorem 2.5.12(a) and §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup
open Matrix.PSL3.EvenInnerCentralizers
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Four.InnerInvolutionCentralizers
noncomputable section

abbrev innerCentralizer (t : MulAut PSL) : Subgroup (MulAut PSL) :=
  MulAut.innerSubgroup PSL ⊓ Subgroup.centralizer ({t} : Set (MulAut PSL))

private theorem conj_injective : Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  exact MulAut.conj_injective_of_center_eq_bot
    (Group.IsPerfect.center_quotient_center_eq_bot SL)

/-- The marked root centralizer is the actual upper-unitriangular group. -/
noncomputable def rootCentralizerEquiv : U F ≃* centralizer F :=
  MulEquiv.ofBijective (unipotentInCentralizer F)
    ⟨unipotentInCentralizer_injective F,
      unipotentInCentralizer_surjective_of_card_four F card_F⟩

private theorem conj_conj (t : MulAut PSL) (x : PSL) :
    MulAut.conj (t x) = t * MulAut.conj x * t⁻¹ := by
  ext y
  simp

private theorem fixed_iff_conj_centralizes (t : MulAut PSL) (x : PSL) :
    t x = x ↔ MulAut.conj x ∈ Subgroup.centralizer ({t} : Set (MulAut PSL)) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h := conj_conj t x
    rw [hx] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  · intro hx
    apply conj_injective
    rw [conj_conj, ← hx, mul_inv_cancel_right]

private theorem innerCentralizer_eq_map (t : MulAut PSL) :
    innerCentralizer t = t.fixedSubgroup.map (MulAut.conj : PSL →* MulAut PSL) := by
  ext a
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, (MulAut.mem_fixedSubgroup t x).mpr
      ((fixed_iff_conj_centralizes t x).mpr hx), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (fixed_iff_conj_centralizes t x).mp
      ((MulAut.mem_fixedSubgroup t x).mp hx)⟩

/-- An inner involution centralizer has precisely 64 elements. -/
theorem card_innerCentralizer (t : MulAut PSL)
    (hi : t ∈ MulAut.innerSubgroup PSL) (hne : t ≠ 1) (hsq : t ^ 2 = 1) :
    Nat.card (innerCentralizer t) = 64 := by
  obtain ⟨x, rfl⟩ := hi
  have hx : x ≠ 1 := by intro h; exact hne (h ▸ map_one MulAut.conj)
  have hx2 : x ^ 2 = 1 := by
    apply conj_injective
    rw [map_pow, hsq, map_one]
  rw [innerCentralizer_eq_map, Subgroup.card_map_of_injective conj_injective,
    MulAut.fixedSubgroup_conj]
  rw [Nat.card_congr (involutionCentralizerEquiv F (n := 2) (by decide)
    (by simpa using card_F) x hx hx2).toEquiv]
  rw [← Nat.card_congr rootCentralizerEquiv.toEquiv, card_U, card_F]
  rfl

/-- The actual inner involution centralizer is a two-group. -/
theorem innerCentralizer_isTwoGroup (t : MulAut PSL)
    (hi : t ∈ MulAut.innerSubgroup PSL) (hne : t ≠ 1) (hsq : t ^ 2 = 1) :
    IsPGroup 2 (innerCentralizer t) :=
  IsPGroup.of_card (n := 6) (card_innerCentralizer t hi hne hsq)

private theorem map_rootCentralizer (b : MulAut PSL) (hb : b (root F) = root F) :
    (centralizer F).map b.toMonoidHom = centralizer F := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change b.symm y ∈ Subgroup.centralizer {root F} ↔ y ∈ Subgroup.centralizer {root F}
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    ← b.injective.eq_iff, map_mul, map_mul, hb, b.apply_symm_apply]

private def rootAction (b : MulAut PSL) (hb : b (root F) = root F) :
    MulAut (centralizer F) :=
  (b.subgroupMap (centralizer F)).trans (MulEquiv.subgroupCongr (map_rootCentralizer b hb))

private def coordinateAction (b : MulAut PSL) (hb : b (root F) = root F) : MulAut (U F) :=
  (rootCentralizerEquiv.trans (rootAction b hb)).trans rootCentralizerEquiv.symm

private theorem projective_coordinateAction (b : MulAut PSL) (hb : b (root F) = root F)
    (u : U F) : projective F (coordinateAction b hb u) = b (projective F u) := by
  change (rootCentralizerEquiv (coordinateAction b hb u) : PSL) = _
  have he := rootCentralizerEquiv.apply_symm_apply (rootAction b hb (rootCentralizerEquiv u))
  exact congrArg Subtype.val he

private theorem coordinateAction_cube (b : MulAut PSL) (hb : b (root F) = root F)
    (hb3 : b ^ 3 = 1) : coordinateAction b hb ^ 3 = 1 := by
  apply MulEquiv.ext
  intro u
  apply projective_injective F
  change projective F (coordinateAction b hb (coordinateAction b hb (coordinateAction b hb u))) =
    projective F u
  rw [projective_coordinateAction, projective_coordinateAction, projective_coordinateAction]
  exact MulEquiv.congr_fun hb3 (projective F u)

private theorem coordinateAction_root (b : MulAut PSL) (hb : b (root F) = root F) :
    coordinateAction b hb ⟨0,0,1⟩ = ⟨0,0,1⟩ := by
  apply projective_injective F
  rw [projective_coordinateAction]
  exact hb

private theorem coordinateAction_ne_one (b : MulAut PSL) (hb : b (root F) = root F)
    (hne : b ≠ 1) (hb3 : b ^ 3 = 1) : coordinateAction b hb ≠ 1 := by
  intro he
  have hfix : ∀ u ∈ PSL3.LinearThree.unipotent F, b u = u := by
    intro u hu
    rw [← PSL3.LinearThree.projective_range] at hu
    obtain ⟨v, rfl⟩ := hu
    rw [← projective_coordinateAction b hb, he]
    rfl
  obtain ⟨z,hz,rfl⟩ := PSL3.LinearThree.exists_projectiveCenter_of_fixes_unipotent F
    (n := 2) (by decide) (by simpa using card_F) b hfix
  obtain ⟨c,rfl⟩ := (mem_projectiveCenter F z).mp hz
  have hz2 : (MulAut.conj (projective F ⟨0,0,c⟩)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, (square_eq_one_iff F _).mpr (Or.inl rfl), map_one, map_one]
  apply hne
  have h := hb3
  rw [pow_succ, hz2, one_mul] at h
  exact h

private theorem root_common_bound
    (hlocal : ∀ β : MulAut (U F), β ≠ 1 → β ^ 3 = 1 →
      β ⟨0,0,1⟩ = ⟨0,0,1⟩ → Nat.card β.fixedSubgroup ≤ 4)
    (b : MulAut PSL) (hb : b (root F) = root F) (hne : b ≠ 1) (hb3 : b ^ 3 = 1) :
    Nat.card ↥(centralizer F ⊓ b.fixedSubgroup) ≤ 4 := by
  let β := coordinateAction b hb
  let f : (centralizer F ⊓ b.fixedSubgroup : Subgroup PSL) → β.fixedSubgroup := fun x =>
    ⟨rootCentralizerEquiv.symm ⟨x, x.property.1⟩, by
      apply (MulAut.mem_fixedSubgroup β _).mpr
      apply projective_injective F
      rw [projective_coordinateAction]
      have he : projective F (rootCentralizerEquiv.symm ⟨x, x.property.1⟩) = x :=
        congrArg Subtype.val (rootCentralizerEquiv.apply_symm_apply ⟨x,x.property.1⟩)
      rw [he]
      exact (MulAut.mem_fixedSubgroup b x).mp x.property.2⟩
  have hf : Function.Injective f := by
    intro x y h
    have h' : rootCentralizerEquiv.symm ⟨x,x.property.1⟩ =
        rootCentralizerEquiv.symm ⟨y,y.property.1⟩ := congrArg Subtype.val h
    have he := rootCentralizerEquiv.symm.injective h'
    exact Subtype.ext (congrArg (fun v : centralizer F => (v : PSL)) he)
  exact (Nat.card_le_card_of_injective f hf).trans
    (hlocal β (coordinateAction_ne_one b hb hne hb3) (coordinateAction_cube b hb hb3)
      (coordinateAction_root b hb))

private theorem inner_common_eq_map (t b : MulAut PSL) :
    innerCentralizer t ⊓ Subgroup.centralizer ({b} : Set (MulAut PSL)) =
      (t.fixedSubgroup ⊓ b.fixedSubgroup).map (MulAut.conj : PSL →* MulAut PSL) := by
  ext a
  constructor
  · rintro ⟨⟨⟨x, rfl⟩, hx⟩, hb⟩
    exact ⟨x, ⟨(MulAut.mem_fixedSubgroup t x).mpr
      ((fixed_iff_conj_centralizes t x).mpr hx),
      (MulAut.mem_fixedSubgroup b x).mpr ((fixed_iff_conj_centralizes b x).mpr hb)⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨⟨x, rfl⟩, (fixed_iff_conj_centralizes t x).mp
      ((MulAut.mem_fixedSubgroup t x).mp hx.1)⟩,
      (fixed_iff_conj_centralizes b x).mp ((MulAut.mem_fixedSubgroup b x).mp hx.2)⟩

private theorem map_common (x : PSL) (e : MulAut PSL) (he : e x = root F)
    (b : MulAut PSL) :
    (Subgroup.centralizer ({x} : Set PSL) ⊓ b.fixedSubgroup).map e.toMonoidHom =
      centralizer F ⊓ (MulAut.congr e b).fixedSubgroup := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change (e.symm y ∈ Subgroup.centralizer {x} ∧ e.symm y ∈ b.fixedSubgroup) ↔
    (y ∈ Subgroup.centralizer {root F} ∧ y ∈ (MulAut.congr e b).fixedSubgroup)
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
  constructor
  · rintro ⟨hc,hf⟩
    constructor
    · simpa only [map_mul, he, e.apply_symm_apply] using congrArg e hc
    · change e (b (e.symm y)) = y
      rw [hf, e.apply_symm_apply]
  · rintro ⟨hc,hf⟩
    constructor
    · apply e.injective
      simpa only [map_mul, he, e.apply_symm_apply] using hc
    · apply e.injective
      exact hf.trans (e.apply_symm_apply y).symm

/-- The cubic common-centralizer bound follows from the intrinsic fixed-point
calculation on the unitriangular group. This reduction keeps the local input
explicit; `card_commonCentralizer_le` discharges it below. -/
theorem card_commonCentralizer_le_of_unipotent
    (hlocal : ∀ β : MulAut (U F), β ≠ 1 → β ^ 3 = 1 →
      β ⟨0,0,1⟩ = ⟨0,0,1⟩ → Nat.card β.fixedSubgroup ≤ 4)
    (t b : MulAut PSL) (hi : t ∈ MulAut.innerSubgroup PSL)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) (hb : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hbt : Commute b t) :
    Nat.card ↥(innerCentralizer t ⊓ Subgroup.centralizer ({b} : Set (MulAut PSL))) ≤ 4 := by
  obtain ⟨x,rfl⟩ := hi
  have hx : x ≠ 1 := by intro h; exact ht (h ▸ map_one MulAut.conj)
  have hx2 : x ^ 2 = 1 := by
    apply conj_injective
    rw [map_pow, ht2, map_one]
  have hbx : b x = x := (fixed_iff_conj_centralizes b x).mpr
    (mem_centralizer_singleton_iff.mpr hbt.eq.symm)
  obtain ⟨g,hg⟩ := exists_conjugator_root F (n := 2) (by decide)
    (by simpa using card_F) x hx hx2
  let e := MulAut.conj g
  have he : e x = root F := hg
  let β := MulAut.congr e b
  have hβroot : β (root F) = root F := by
    change e (b (e.symm (root F))) = root F
    rw [← he, e.symm_apply_apply, hbx]
  have hβ : β ≠ 1 := fun h => hb ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hβ3 : β ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  rw [inner_common_eq_map, Subgroup.card_map_of_injective conj_injective,
    MulAut.fixedSubgroup_conj]
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, map_common x e he b]
  exact root_common_bound hlocal β hβroot hβ hβ3

/-- The common inner centralizer of an inner involution and a commuting
nonidentity cubic automorphism of PSL₃(4) has at most four elements. -/
theorem card_commonCentralizer_le
    (t b : MulAut PSL) (hi : t ∈ MulAut.innerSubgroup PSL)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) (hb : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hbt : Commute b t) :
    Nat.card ↥(innerCentralizer t ⊓ Subgroup.centralizer ({b} : Set (MulAut PSL))) ≤ 4 :=
  card_commonCentralizer_le_of_unipotent UnipotentCubic.card_fixedSubgroup_le
    t b hi ht ht2 hb hb3 hbt

end
end Matrix.PSL3Four.InnerInvolutionCentralizers
