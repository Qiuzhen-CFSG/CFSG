module
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-!
# An intrinsic pair of Sylow overgroups in A₇

Use the eight-word dihedral Sylow already constructed in `DihedralLocals`.
Every automorphism preserving it is induced by a permutation fixing its unique
fixed point and preserving the support of its central involution. Thus it fixes
both the A₆ point stabilizer and the four-block stabilizer. These are proper;
the second moves the distinguished point, so maximality of the first shows
that they generate A₇. All finite checks involve only eight words or seven
points, never an enumeration of the ambient group.

Source: Aschbacher–Smith B.6.9, printed p.116; the standard A₇ seven-point
geometry and Aut(A₇) = S₇ (GLS3, Theorem 5.2.1).
-/


@[expose] public section
open Equiv Equiv.Perm Subgroup
open scoped Pointwise
namespace AlternatingSeven.InvariantParabolicPair
open DihedralLocals

def pointParabolic : Subgroup A7 := MulAction.stabilizer A7 (6 : Fin 7)
def blockParabolic : Subgroup A7 :=
  (MulAction.stabilizer Perm7 block).comap (alternatingGroup (Fin 7)).subtype

private theorem words_fixed (i : Fin 8) : tWord i 6 = 6 :=
  (by decide +kernel : ∀ i : Fin 8, tWord i 6 = 6) i
private theorem words_block (i : Fin 8) : tWord i • block = block :=
  (by decide +kernel : ∀ i : Fin 8, tWord i • block = block) i
private theorem r_fixed (x : Fin 7) : r x = x ↔ x = 6 :=
  (by decide +kernel : ∀ x : Fin 7, r x = x ↔ x = 6) x
private theorem word_square (i : Fin 8) (h : tWord i ^ 2 ≠ 1) : tWord i ^ 2 = r ^ 2 :=
  (by decide +kernel : ∀ i : Fin 8, tWord i ^ 2 ≠ 1 → tWord i ^ 2 = r ^ 2) i h
private theorem square_support : (r ^ 2).support = block := by decide +kernel

private theorem normalizer_geometry (p : Perm7)
    (hp : twoGroup.map (MulAut.conj p).toMonoidHom = twoGroup) :
    p 6 = 6 ∧ p • block = block := by
  have hr : p*r*p⁻¹ ∈ twoGroup := by
    rw [← hp]
    exact mem_map_of_mem _ r_mem_twoGroup
  obtain ⟨i,hi⟩ := hr
  have h6 : p 6 = 6 := by
    have hpre := congrArg (fun q : Perm7 => q 6) hi
    change tWord i 6 = p (r (p⁻¹ 6)) at hpre
    rw [words_fixed] at hpre
    have hf : r (p⁻¹ 6) = p⁻¹ 6 := by
      apply p.injective
      simpa using hpre.symm
    simpa using (congrArg p ((r_fixed _).mp hf)).symm
  have hsq : p * r ^ 2 * p⁻¹ = r ^ 2 := by
    have hs : tWord i ^ 2 = p * r ^ 2 * p⁻¹ := by
      rw [hi, ← MulAut.conj_apply, ← map_pow]
      rfl
    have hn : tWord i ^ 2 ≠ 1 := by
      rw [hs]
      intro h
      apply r_square_ne
      have := congrArg (fun q : Perm7 => p⁻¹*q*p) h
      simpa [mul_assoc] using this
    exact hs.symm.trans (word_square i hn)
  have hs := congrArg Perm.support hsq
  rw [Perm.support_conj, square_support] at hs
  refine ⟨h6, ?_⟩
  simpa only [Finset.map_eq_image, Finset.smul_finset_def, Equiv.Perm.smul_def, Equiv.coe_toEmbedding] using hs

private theorem parabolic_geometry :
    pointParabolic ⊔ blockParabolic = ⊤ ∧ pointParabolic ≠ ⊤ ∧ blockParabolic ≠ ⊤ := by
  have hp : IsCoatom pointParabolic := by
    have hh := alternatingGroup.isCoatom_stabilizer_singleton (α := Fin 7)
      (by simp : 3 ≤ Nat.card (Fin 7)) (Set.singleton_nonempty (6 : Fin 7))
      (Set.subsingleton_singleton)
    simpa [MulAction.stabilizer_singleton, pointParabolic] using hh
  let a : A7 := ⟨swap 4 5 * swap 5 6, by rw [mem_alternatingGroup]; decide +kernel⟩
  have ha : a ∈ blockParabolic := by
    change (a : Perm7) • block = block
    decide +kernel
  have haP : a ∉ pointParabolic := by
    change (a : Perm7) 6 ≠ 6
    decide +kernel
  have hb : blockParabolic ≠ ⊤ := by
    let b : A7 := ⟨swap 0 1 * swap 1 6, by rw [mem_alternatingGroup]; decide +kernel⟩
    have h : b ∉ blockParabolic := by
      change (b : Perm7) • block ≠ block
      decide +kernel
    intro he
    exact h (he ▸ mem_top b)
  refine ⟨hp.2 _ ?_, hp.1, hb⟩
  apply lt_of_le_of_ne le_sup_left
  intro he
  have hh : a ∈ pointParabolic ⊔ blockParabolic := (le_sup_right : blockParabolic ≤ pointParabolic ⊔ blockParabolic) ha
  rw [← he] at hh
  exact haP hh

private theorem fixedSylow_le :
    (fixedSylow : Subgroup A7) ≤ pointParabolic ∧
    (fixedSylow : Subgroup A7) ≤ blockParabolic := by
  constructor
  · rintro ⟨g,hg⟩ ⟨i,hi⟩
    change g 6 = 6
    change tWord i = g at hi
    rw [← hi]
    exact words_fixed i
  · rintro ⟨g,hg⟩ ⟨i,hi⟩
    change g • block = block
    change tWord i = g at hi
    rw [← hi]
    exact words_block i

private theorem invariant (a : MulAut A7)
    (ha : (fixedSylow : Subgroup A7).map a.toMonoidHom = fixedSylow) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∧
    blockParabolic.map a.toMonoidHom = blockParabolic := by
  obtain ⟨p,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).2 a
  have hp : twoGroup.map (MulAut.conj p).toMonoidHom = twoGroup := by
    have hmap : (fixedSylow : Subgroup A7).map (alternatingGroup (Fin 7)).subtype = twoGroup := by
      change (twoGroup.subgroupOf (alternatingGroup (Fin 7))).map _ = _
      rw [subgroupOf_map_subtype, inf_eq_left.mpr twoGroup_le_alternating]
    have he := congrArg (fun H : Subgroup A7 => H.map (alternatingGroup (Fin 7)).subtype) ha
    rw [map_map] at he
    have hcomp : (alternatingGroup (Fin 7)).subtype.comp (MulAut.conjNormal p).toMonoidHom =
        (MulAut.conj p).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype := by
      ext x
      rfl
    rw [hcomp, ← map_map, hmap] at he
    exact he
  obtain ⟨h6,hb⟩ := normalizer_geometry p hp
  have mapP : pointParabolic.map (MulAut.conjNormal p).toMonoidHom ≤ pointParabolic := by
    rintro x ⟨y,hy,rfl⟩
    change (p * (y : Perm7) * p⁻¹) 6 = 6
    change (y : Perm7) 6 = 6 at hy
    have h6i : p⁻¹ 6 = 6 := by apply p.injective; simpa using h6.symm
    simpa [Perm.mul_apply,h6i,hy] using h6
  have mapQ : blockParabolic.map (MulAut.conjNormal p).toMonoidHom ≤ blockParabolic := by
    rintro x ⟨y,hy,rfl⟩
    change (p * (y : Perm7) * p⁻¹) • block = block
    change (y : Perm7) • block = block at hy
    have hbi : p⁻¹ • block = block := by rw [inv_smul_eq_iff, hb]
    rw [mul_smul,mul_smul,hbi,hy,hb]
  exact ⟨eq_of_le_of_card_ge mapP (Nat.card_congr
    (pointParabolic.equivMapOfInjective (MulAut.conjNormal p).toMonoidHom (MulAut.conjNormal p).injective).toEquiv).le,
    eq_of_le_of_card_ge mapQ (Nat.card_congr
    (blockParabolic.equivMapOfInjective (MulAut.conjNormal p).toMonoidHom (MulAut.conjNormal p).injective).toEquiv).le⟩

/-- The literal standard A₇ Sylow has two proper generating overgroups fixed
by every automorphism preserving that Sylow. -/
theorem exists_intrinsic_pair :
    ∃ P Q : Subgroup A7, P ⊔ Q = ⊤ ∧ P ≠ ⊤ ∧ Q ≠ ⊤ ∧
      (fixedSylow : Subgroup A7) ≤ P ∧ (fixedSylow : Subgroup A7) ≤ Q ∧
      ∀ a : MulAut A7, (fixedSylow : Subgroup A7).map a.toMonoidHom = fixedSylow →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q :=
  ⟨pointParabolic,blockParabolic,parabolic_geometry.1,parabolic_geometry.2.1,
    parabolic_geometry.2.2,fixedSylow_le.1,fixedSylow_le.2,invariant⟩
end AlternatingSeven.InvariantParabolicPair
