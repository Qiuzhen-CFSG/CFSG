module

public import Theory.Representation.CharacteristicTwoIrreducibleRank
public import Mathlib.Tactic.Group

/-!
# Inner involutions in a characteristic-two linear normalizer

In a faithful characteristic-two representation, an involution centralizing an irreducibly
acting subgroup is trivial. Consequently the square map on the finite center
is bijective. If a normalizer involution acts as conjugation by a, divide a by
a central square root of a² to obtain an involution in the subgroup with the
same conjugation action. Their quotient is a centralizing involution, hence
trivial.

This treats every finite characteristic-two coefficient field without
restricting scalars. Innerness can first be established on the central quotient
of a perfect group, then lifted through its actual covering map.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.13, printed pp.73–74 / PDF pp.84–85, combined 1 March 2004 manuscript.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.CharacteristicTwoIrreducible
variable {E G V : Type*} [Field E] [CharP E 2] [Group G]
  [AddCommGroup V] [Module E V]
  (ρ : Representation E G V) (L : Subgroup G)
  [Finite L] [IsIrreducible (ρ.comp L.subtype)]

/-- The center of a finite faithfully and irreducibly acting characteristic-two group
has a surjective square map: Schur's lemma eliminates its involutions. -/
theorem center_square_surjective (hf : Function.Injective ρ) :
    Function.Surjective (powMonoidHom 2 : center L →* center L) := by
  apply Finite.surjective_of_injective
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro z hz
  apply Subtype.ext
  apply Subtype.ext
  apply centralizing_square_one_eq_one ρ L hf
  · exact congrArg (fun w : center L => ((w : L) : G)) (show (powMonoidHom 2 : center L →* center L) z = 1 from hz)
  · intro l hl
    exact congrArg (fun w : L => (w : G)) ((mem_center_iff.mp z.property) ⟨l, hl⟩)

/-- An involution in the normalizer of a finite irreducibly acting subgroup
belongs to that subgroup whenever its conjugation action is inner. -/
theorem involution_mem_of_inner (hf : Function.Injective ρ)
    (t : normalizer (L : Set G)) (ht : (t : G) ^ 2 = 1)
    (hinner : ∃ a : L, L.normalizerMonoidHom t = MulAut.conj a) :
    (t : G) ∈ L := by
  obtain ⟨a, ha⟩ := hinner
  have hconj (b : L) : (t : G) * (b : G) * (t : G)⁻¹ =
      (a : G) * (b : G) * (a : G)⁻¹ :=
    congrArg (fun f : MulAut L => ((f b : L) : G)) ha
  have ht' : t ^ 2 = 1 := Subtype.ext ht
  have hasq : MulAut.conj (a ^ 2) = 1 := by
    rw [map_pow, ← ha, ← map_pow, ht', map_one]
  have hac : a ^ 2 ∈ center L := by
    apply mem_center_iff.mpr
    intro b
    have h := congrArg (fun f : MulAut L => f b) hasq
    change (a ^ 2) * b * (a ^ 2)⁻¹ = b at h
    have h' := congrArg (fun x => x * a ^ 2) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'.symm
  obtain ⟨z, hz⟩ := center_square_surjective ρ L hf ⟨a ^ 2, hac⟩
  have hz' : (z : L) ^ 2 = a ^ 2 := congrArg Subtype.val hz
  let b : L := a * (z : L)⁻¹
  have haz : Commute a (z : L) := (mem_center_iff.mp z.property) a
  have hb : b ^ 2 = 1 := by
    dsimp [b]
    rw [haz.inv_right.mul_pow, inv_pow, hz', mul_inv_cancel]
  have hba : MulAut.conj b = MulAut.conj a := by
    apply MulEquiv.ext
    intro l
    change (a * (z : L)⁻¹) * l * (a * (z : L)⁻¹)⁻¹ = a * l * a⁻¹
    have hzl : Commute (z : L) l := ((mem_center_iff.mp z.property) l).symm
    simp only [mul_inv_rev, inv_inv]
    calc
      _ = a * ((z : L)⁻¹ * l * (z : L)) * a⁻¹ := by group
      _ = _ := by rw [hzl.inv_left.eq]; group
  have htc : Commute (t : G) (b : G) := by
    have h := hconj b
    have hab : a * b * a⁻¹ = b := by
      have h := congrArg (fun f : MulAut L => f b) hba.symm
      simpa only [MulAut.conj_apply, mul_inv_cancel_right] using h
    rw [← L.coe_mul, ← L.coe_inv, ← L.coe_mul, hab] at h
    exact (mul_inv_eq_iff_eq_mul.mp h)
  have htb : (t : G) * (b : G)⁻¹ = 1 := by
    apply centralizing_square_one_eq_one ρ L hf
    · rw [htc.inv_right.mul_pow, ht, inv_pow]
      have hb' : (b : G) ^ 2 = 1 := congrArg Subtype.val hb
      rw [hb', inv_one, one_mul]
    · intro l hl
      have h := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : G)) (ha.trans hba.symm)
      change (t : G) * l * (t : G)⁻¹ = (b : G) * l * (b : G)⁻¹ at h
      have h' : (b : G)⁻¹ * (t : G) * l = l * ((b : G)⁻¹ * (t : G)) := by
        calc
          _ = (b : G)⁻¹ * ((t : G) * l * (t : G)⁻¹) * (t : G) := by group
          _ = _ := by rw [h]; group
      rw [htc.inv_right.eq]
      exact h'.symm
  exact (mul_inv_eq_one.mp htb) ▸ b.property
end Representation.CharacteristicTwoIrreducible
