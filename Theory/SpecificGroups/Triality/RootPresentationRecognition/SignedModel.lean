module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveWeylModel
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl

/-!
# All signed Weyl equations on genuine binary triality

The native longest Weyl element acts by opposition. Its square is one and it
commutes with both simple representatives, by the faithful dihedral model.
Following the checked positive-root tables identifies its values on A and B
with the existing negative simple-root curves, without changing their scalars.
Conjugating the positive additive maps therefore constructs all negative maps
and proves every signed Weyl equation, including the F² and F shifts on C,D.
The defined simple root words are the native representatives and satisfy the
finite braid. All positive binary exponents, including q=2 and q=4, are covered.

Source: GLS3 2.4.8(e,g), using the orbit origins of `FoldedRoots.lean`.
This verifies the signed Weyl part of the presentation; torus verification and
presentation faithfulness are separate obligations.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.SignedModel
open Parabolics ConcreteBruhat PositiveWeylModel RadicalCoordinates.LeviCommutators

def longest (P : Parameters) (hp : P.prime = 2) : Carrier P :=
  weylRepresentativeHom P hp (.r 3)

theorem longest_sq (P : Parameters) (hp : P.prime = 2) : longest P hp * longest P hp = 1 := by
  rw [longest, ← map_mul]
  exact (congrArg (weylRepresentativeHom P hp)
    (show (DihedralGroup.r 3 : DihedralGroup 6) * .r 3 = 1 by decide)).trans (map_one _)

theorem longest_commute (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Commute (longest P hp) (simpleRepresentative P hp a) := by
  have h : Commute (DihedralGroup.r 3 : DihedralGroup 6) (relativeReflection a) := by
    change (DihedralGroup.r 3 : DihedralGroup 6) * relativeReflection a = relativeReflection a * .r 3
    cases a <;> decide
  simpa only [longest, weylRepresentativeHom_apply, weylRepresentative_simple]
    using h.map (weylRepresentativeHom P hp)

def opposition (P : Parameters) (hp : P.prime = 2) : MulAut (Carrier P) :=
  MulAut.conj (longest P hp)

theorem opposition_involutive (P : Parameters) (hp : P.prime = 2) :
    Function.Involutive (opposition P hp) := by
  intro x
  change longest P hp * (longest P hp * x * (longest P hp)⁻¹) * (longest P hp)⁻¹ = x
  have h := longest_sq P hp
  calc
    _ = (longest P hp * longest P hp) * x * (longest P hp * longest P hp)⁻¹ := by group
    _ = x := by rw [h]; simp

theorem opposition_simple (P : Parameters) (hp : P.prime = 2) (a : Node) :
    opposition P hp (simpleRepresentative P hp a) = simpleRepresentative P hp a := by
  simp only [opposition, MulAut.conj_apply]
  rw [(longest_commute P hp a).eq, mul_inv_cancel_right]

private theorem conj_mul {G : Type*} [Group G] (a b x : G) :
    (a*b)*x*(a*b)⁻¹ = a*(b*x*b⁻¹)*a⁻¹ := by group

theorem opposition_short_zero (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    opposition P hp (short P hp 0 t) = rootElement P hp false .arms t := by
  have he : longest P hp = (simpleRepresentative P hp .arms * simpleRepresentative P hp .central)^3 := by
    simp only [longest, weylRepresentativeHom_apply, weylRepresentative, weylElementary,
      map_pow, map_mul, simpleRepresentative]
    rfl
  simp only [opposition, MulAut.conj_apply]
  rw [he]
  simp only [pow_succ, pow_zero, one_mul, conj_mul]
  simp only [central_short, arms_short_one, arms_short_two, arms_short_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fieldFrobenius_three]

theorem opposition_long_zero (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    opposition P hp (long P hp 0 t) = rootElement P hp false .central t := by
  have he : longest P hp = (simpleRepresentative P hp .central * simpleRepresentative P hp .arms)^3 := by
    have h : (DihedralGroup.r 3 : DihedralGroup 6) =
        (relativeReflection .central * relativeReflection .arms)^3 := by decide
    simpa only [longest, map_pow, map_mul, weylRepresentativeHom_apply, weylRepresentative_simple]
      using congrArg (weylRepresentativeHom P hp) h
  simp only [opposition, MulAut.conj_apply]
  rw [he]
  simp only [pow_succ, pow_zero, one_mul, conj_mul]
  simp [arms_long, central_long P hp 1 (by decide),
    central_long P hp 2 (by decide), central_long_zero]

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

def roots : SignedRoots (n := n) (hn := hn) (BinaryCarrier n hn) where
  positive := nativePositiveRoots n hn
  negativeShort i := (opposition P rfl).toMonoidHom.comp ((nativePositiveRoots n hn).shortRoot i)
  negativeLong i := (opposition P rfl).toMonoidHom.comp ((nativePositiveRoots n hn).longRoot i)

theorem negative_short (i : Fin 3) (t : ExtensionField P) :
    (roots n hn).negativeShortValue i t = opposition P rfl (short P rfl i t) := rfl

theorem negative_long (i : Fin 3) (t : fixedField P) :
    (roots n hn).negativeLongValue i t = opposition P rfl (long P rfl i t) := rfl

theorem nA_one : (roots n hn).nA 1 = simpleRepresentative P rfl .arms := by
  change short P rfl 0 1 * opposition P rfl (short P rfl 0 1) * short P rfl 0 1 = _
  rw [opposition_short_zero P rfl, PositiveWeylModel.short_zero P rfl]
  exact (simpleRepresentative_eq_root_word P rfl _).symm

theorem nB_one : (roots n hn).nB 1 = simpleRepresentative P rfl .central := by
  change long P rfl 0 1 * opposition P rfl (long P rfl 0 1) * long P rfl 0 1 = _
  rw [opposition_long_zero P rfl, PositiveWeylModel.long_zero P rfl]
  exact (simpleRepresentative_eq_root_word P rfl _).symm

theorem weylRelations : (roots n hn).WeylRelations where
  positiveRelations := native_relations n hn
  nA_sq := by rw [nA_one]; exact simpleRepresentative_sq P rfl .arms
  nB_sq := by rw [nB_one]; exact simpleRepresentative_sq P rfl .central
  braid := by
    rw [nA_one, nB_one, ← orderOf_simpleProduct P rfl]
    exact pow_orderOf_eq_one _

private theorem opposed_conjugate (a : Node) (x y : Carrier P)
    (h : simpleRepresentative P rfl a * x * (simpleRepresentative P rfl a)⁻¹ = y) :
    simpleRepresentative P rfl a * opposition P rfl x * (simpleRepresentative P rfl a)⁻¹ =
      opposition P rfl y := by
  simpa only [map_mul, map_inv, opposition_simple P rfl] using congrArg (opposition P rfl) h

theorem actionRelations : (roots n hn).ActionRelations where
  arms_short0 := by
    intro s t
    rw [nA_one]
    cases s
    · change simpleRepresentative P rfl .arms * opposition P rfl (short P rfl 0 t) *
        (simpleRepresentative P rfl .arms)⁻¹ = short P rfl 0 t
      have h := opposed_conjugate n hn .arms _ _ (arms_short_zero P rfl t)
      rw [← opposition_short_zero P rfl] at h
      exact h.trans (opposition_involutive P rfl _)
    · exact arms_short_zero P rfl t |>.trans (opposition_short_zero P rfl t).symm
  arms_short1 := by
    intro s t
    rw [nA_one]
    cases s
    · exact opposed_conjugate n hn .arms _ _ (arms_short_one P rfl t)
    · exact arms_short_one P rfl t
  arms_short2 := by
    intro s t
    rw [nA_one]
    cases s
    · exact opposed_conjugate n hn .arms _ _ (arms_short_two P rfl t)
    · exact arms_short_two P rfl t
  arms_long := by
    intro s i t
    rw [nA_one]
    cases s
    · exact opposed_conjugate n hn .arms _ _ (arms_long P rfl i t)
    · exact arms_long P rfl i t
  central_short := by
    intro s i t
    rw [nB_one]
    cases s
    · exact opposed_conjugate n hn .central _ _ (central_short P rfl i t)
    · exact central_short P rfl i t
  central_long0 := by
    intro s t
    rw [nB_one]
    cases s
    · change simpleRepresentative P rfl .central * opposition P rfl (long P rfl 0 t) *
        (simpleRepresentative P rfl .central)⁻¹ = long P rfl 0 t
      have h := opposed_conjugate n hn .central _ _ (central_long_zero P rfl t)
      rw [← opposition_long_zero P rfl] at h
      exact h.trans (opposition_involutive P rfl _)
    · exact central_long_zero P rfl t |>.trans (opposition_long_zero P rfl t).symm
  central_long1 := by
    intro s t
    rw [nB_one]
    cases s
    · exact opposed_conjugate n hn .central _ _ (central_long P rfl 1 (by decide) t)
    · exact central_long P rfl 1 (by decide) t
  central_long2 := by
    intro s t
    rw [nB_one]
    cases s
    · exact opposed_conjugate n hn .central _ _ (central_long P rfl 2 (by decide) t)
    · exact central_long P rfl 2 (by decide) t

end Triality.Standard.RootPresentationRecognition.SignedModel
