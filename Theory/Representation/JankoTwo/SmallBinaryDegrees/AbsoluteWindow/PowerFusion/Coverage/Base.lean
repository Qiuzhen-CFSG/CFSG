module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data

/-!
# Four-point certificates for conjugacy in the literal Hall--Janko carrier

The certified four transversals show that a carrier element is determined by
its images of 0, 1, 2, 3. Thus a conjugacy certificate needs only four checks
of `c * x = y * c`, provided all three permutations are actual carrier elements.
This is used by the centralizer coverage certificates, without enlarging the
conjugating group to the symmetric group.

Source: the ATLAS `J2G1-p100B0` normal forms certified in
`ExceptionalParabolics.FirstParabolic.Order` and its `OrderData`.
-/

public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate
open ExceptionalParabolics.FirstParabolic.OrderData

theorem carrier_ext_base {x y : Carrier}
    (h : ∀ k : Fin 4, inclusion x (k.castLE (by decide)) =
      inclusion y (k.castLE (by decide))) : x = y := by
  obtain ⟨⟨i₀, i₁, i₂, i₃⟩, hi⟩ := element_surjective x
  obtain ⟨⟨j₀, j₁, j₂, j₃⟩, hj⟩ := element_surjective y
  subst x
  subst y
  have h0 : normalForm (i₀, i₁, i₂, i₃) 0 =
      normalForm (j₀, j₁, j₂, j₃) 0 := h 0
  have h1 : normalForm (i₀, i₁, i₂, i₃) 1 =
      normalForm (j₀, j₁, j₂, j₃) 1 := h 1
  have h2 : normalForm (i₀, i₁, i₂, i₃) 2 =
      normalForm (j₀, j₁, j₂, j₃) 2 := h 2
  have h3 : normalForm (i₀, i₁, i₂, i₃) 3 =
      normalForm (j₀, j₁, j₂, j₃) 3 := h 3
  simp only [normalForm, Equiv.Perm.mul_apply] at h0 h1 h2 h3
  have e0 := congrArg decode0 h0
  simp only [rep3_fix0, rep2_fix0, rep1_fix0, decode0_spec] at e0
  subst j₀
  have e1 := congrArg decode1 ((rep0 i₀).injective h1)
  simp only [rep3_fix1, rep2_fix1, decode1_spec] at e1
  subst j₁
  have e2 := congrArg decode2 ((rep1 i₁).injective ((rep0 i₀).injective h2))
  simp only [rep3_fix2, decode2_spec] at e2
  subst j₂
  have e3 := congrArg decode3
    ((rep2 i₂).injective ((rep1 i₁).injective ((rep0 i₀).injective h3)))
  simp only [decode3_spec] at e3
  subst j₃
  rfl

theorem isConj_of_base (x y c : Carrier)
    (h : ∀ k : Fin 4,
      inclusion c (inclusion x (k.castLE (by decide))) =
      inclusion y (inclusion c (k.castLE (by decide)))) : IsConj x y := by
  have he : c * x = y * c := carrier_ext_base h
  exact isConj_iff.mpr ⟨c, by rw [he, mul_inv_cancel_right]⟩

theorem representative_zero : representative 0 = 1 := by
  apply carrier_ext_base
  decide +kernel

end Sporadic.LeechRelated.J2.PowerFusionCertificate
