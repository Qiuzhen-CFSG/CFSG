module
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.Algebra.CharP.Two

/-!
# Two-elements fixing the full natural root line

A semilinear two-element fixing the natural root line pointwise has trivial
field automorphism. Its lower diagonal entry has two-power order, hence is
one in characteristic two. The element therefore acts as an upper root.
This is the full-normalizer calculation needed by C.5.6: no inner-action
hypothesis is imposed on the ambient two-subgroup.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {F H : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Group H]

/-- The pointwise stabilizer of the full root line among semilinear
2-elements is the natural upper root group. -/
theorem natural_fixed_line_two_element
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (a : H)
    (hsemi : ∃ σ : F ≃+* F, ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = σ c • ρ a v)
    (hfix : ∀ c : F, ρ a ![c,0] = ![c,0])
    (n : ℕ) (hpow : a ^ (2 ^ n) = 1) :
    ∃ t : F, ∀ v : Fin 2 → F, ρ a v = ![v 0 + t * v 1,v 1] := by
  obtain ⟨σ,hσ⟩ := hsemi
  have hσid (c : F) : σ c = c := by
    have hh := congrFun (hσ c ![1,0]) 0
    have he : c • (![1,0] : Fin 2 → F) = ![c,0] := by ext i; fin_cases i <;> simp
    rw [he,hfix,hfix] at hh
    simpa using hh.symm
  have hlin (c : F) (v : Fin 2 → F) : ρ a (c • v) = c • ρ a v := by rw [hσ,hσid]
  let b := ρ a ![0,1] 0
  let c := ρ a ![0,1] 1
  have hform (v : Fin 2 → F) : ρ a v = ![v 0 + b * v 1,c * v 1] := by
    have he : v = v 0 • (![1,0] : Fin 2 → F) + v 1 • ![0,1] := by
      ext i
      fin_cases i <;> simp
    calc
      ρ a v = v 0 • ![1,0] + v 1 • ρ a ![0,1] := by
        conv_lhs => rw [he]
        rw [map_add,hlin,hlin,hfix]
      _ = _ := by ext i; fin_cases i <;> simp [b,c,mul_comm]
  have hp (k : ℕ) (v : Fin 2 → F) : ρ (a ^ k) v 1 = c ^ k * v 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',map_mul,Module.End.mul_apply,hform]
      simp only [Matrix.cons_val_one,Matrix.cons_val_fin_one,ih,pow_succ']
      ring
  have hc : c ^ (2 ^ n) = 1 := by
    have hh := hp (2 ^ n) ![0,1]
    rw [hpow] at hh
    simpa using hh.symm
  have hc1 : c = 1 := by
    have he : (c - 1) ^ (2 ^ n) = 0 := by rw [sub_pow_char_pow,hc,one_pow,sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero he)
  exact ⟨b,fun v => by simpa only [hc1,one_mul] using hform v⟩

variable [Finite F]

/-- The actual normalizer of a natural SL₂ layer supplies the semilinearity
used above, rather than assuming an internal ambient action. -/
theorem natural_normalizer_fixed_line_two_element
    (L : Subgroup H) [L.Normal] (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (a : H) (hfix : ∀ c : F, ρ a ![c,0] = ![c,0])
    (n : ℕ) (hpow : a ^ (2 ^ n) = 1) :
    ∃ t : F, ∀ v : Fin 2 → F, ρ a v = ![v 0 + t * v 1,v 1] :=
  natural_fixed_line_two_element ρ a
    (Representation.SL2NaturalOffenders.normalizer_semilinear L e ρ hnat a) hfix n hpow
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
