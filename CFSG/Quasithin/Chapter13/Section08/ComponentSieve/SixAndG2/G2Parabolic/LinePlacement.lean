module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import Theory.Representation.G2NaturalOffenders
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# The endpoint line from the strict G₂ offender ratio

An elementary actor of rank less than three cannot offend on the binary
natural G₂ module. A surjective equivariant projection therefore gives the
same strict inequality on the original central section. If A₁ were outside
U_H, the literal D_H image would be fixed, contradicting the selected rank
comparison. Thus A₁ lies in U_H. The projection must intertwine the whole
star actor; a marking of only the component does not supply that hypothesis.

Source: Aschbacher–Smith, 13.8.27, printed p.963, using B.4.6(13),
F.9.13(6), and the choice in 13.8.8(2).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry

variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A literal natural quotient excludes offenders of rank less than three.
The injection retains the rank of the original actor. -/
theorem strict_codimension_of_natural_projection
    (ρ : Representation (ZMod 2) J W)
    (f : J →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (p : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (p v))
    (A : Subgroup J) (hA : IsElementaryTwo A) (hr : rank A < 3) :
    rank A < fixedCodim ρ A := by
  let τ := Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2)
  have hq := fixedCodim_le_of_equivariant_surjection ρ (τ.comp f) p hp he A
  by_contra! hn
  have ho : IsOffender (τ.comp f) A := ⟨hA, hq.trans hn⟩
  have hm := ho.map_equivariant (τ.comp f) τ f hf
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl)
  have heq := Atlas.G2.NaturalOffenders.natural_offender_rank
    (n := 1) (by norm_num) (by decide) (A.map f) hm
  rw [rank_map_injective f hf] at heq
  omega

variable {G : Type*} [Group G] [Finite G] {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

/-- The selected source rank comparison and a strict action ratio force the
actual conjugate endpoint line into U_H. -/
theorem Aone_le_of_strict_codimension
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hstrict : rank (Source.starImage H (c.Ugamma V₃)) <
      fixedCodim ρ (Source.starImage H (c.Ugamma V₃))) :
    c.Aone V₁ ≤ Source.UH H V₃ := by
  by_contra hn
  have hline : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj (c.gb : G)).injective, hcard]
  have hnorm : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    hreverse.trans ((s.centralizes_conjugate_line (c.gb : G)).trans
      (centralizer_le_normalizer _))
  have hfixed := s.critical_fixed_of_line_not_le (c.Ugamma V₃) (c.Aone V₁) hnorm hline hn
  have hm := Submodule.finrank_mono hfixed
  have hd := (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃)
    (c.Aone V₁))).finrank_quotient_add_finrank
  have hf := fixedCodim_add_finrank ρ (Source.starImage H (c.Ugamma V₃))
  rw [s.quotient_finrank _ (s.line_le_DH _ _ hUg)] at hd
  omega

/-- Application to the same critical pair and the literal natural projection.
The whole-actor equivariance is retained for the parabolic marking owner. -/
theorem Aone_le_of_natural_projection
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (f : Source.Hstar H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (p : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (p v))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hr : rank (Source.starImage H (c.Ugamma V₃)) < 3) :
    c.Aone V₁ ≤ Source.UH H V₃ :=
  Aone_le_of_strict_codimension c s hUg hreverse hcard hcompare
    (strict_codimension_of_natural_projection ρ f hf p hp he _ hA hr)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
