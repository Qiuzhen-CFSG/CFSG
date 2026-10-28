module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.PointLift

/-!
# Nonvanishing of the transported line in the natural quotient

If the actual A₁ image vanished under the natural projection, its
line-valued critical displacements would vanish there. The image of D_H
would then be fixed by Uγ*, with quotient dimension bounded by the
selected critical comparison. This contradicts the strict natural
offender bound for rank less than three.

Source: Aschbacher–Smith 13.8.27, printed p.963, using B.4.6(13)
and the original critical-pair choice in 13.8.8(2).
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry Atlas.G2

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

/-- The actual conjugate endpoint line survives the natural projection. -/
theorem source_line_projection_ne_bot
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (f : Source.Hstar H →* Model (ZMod 2)) (hf : Function.Injective f)
    (p : W →ₗ[ZMod 2] Natural.Space (ZMod 2)) (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hr : rank (Source.starImage H (c.Ugamma V₃)) < 3) :
    (s.image (c.Aone V₁)).map p ≠ ⊥ := by
  let A := Source.starImage H (c.Ugamma V₃)
  let D := s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))
  let σ := (Natural.action (ZMod 2)).comp f
  have hc := (s.critical_line_displacement_of_conjugate (c.Ugamma V₃)
    (c.gb : G) hreverse hcard).2
  intro hz
  have hfix : D ≤ (fixedSpace σ A).comap p := by
    intro v hv a
    change Natural.action (ZMod 2) (f a) (p v) = p v
    rw [← he, ← sub_eq_zero, ← map_sub]
    have hm : p (ρ a v - v) ∈ (s.image (c.Aone V₁)).map p :=
      ⟨_, hc a a.property v hv, rfl⟩
    simpa only [hz, Submodule.mem_bot] using hm
  let q := D.mapQ (fixedSpace σ A) p hfix
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w, rfl⟩ := (fixedSpace σ A).mkQ_surjective v
    obtain ⟨u, rfl⟩ := hp w
    exact ⟨D.mkQ u, rfl⟩
  have hle : fixedCodim σ A ≤ rank A := by
    have hdim := LinearMap.finrank_le_finrank_of_surjective hq
    change fixedCodim σ A ≤ Module.finrank (ZMod 2) (W ⧸ D) at hdim
    have heq := s.quotient_finrank
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))
      (s.line_le_DH (c.Ugamma V₃) (c.Aone V₁) hUg)
    exact hdim.trans (heq.symm ▸ hcompare)
  have hstrict := strict_codimension_of_natural_projection σ f hf
    (LinearMap.id) Function.surjective_id (fun _ _ => rfl) A hA hr
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
