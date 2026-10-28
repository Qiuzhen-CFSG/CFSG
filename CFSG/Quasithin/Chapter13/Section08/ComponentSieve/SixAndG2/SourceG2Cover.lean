module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Filtration
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# The actual G₂(2)′ Weyl cover in the source sieve

Recognition of the literal component section, together with U_H=[U_H,K],
constructs a perfect central projection from U_H/V₁ to the natural six-space.
The universal binary cover is the trace-zero octonion seven-space. Its
surjection onto the original module retains the derived G₂ action and commutes
with the original natural projection. Rank-nullity leaves precisely the
natural module and the Weyl module, and the original order-two line then gives
m(U_H)≤8, the upper bound in the final filtration contradiction.

The acting group here is the actual derived group G₂(2)′. No extension to
full G₂(2) is presumed. Recognition of the component section and the parabolic
and displacement estimates remain inputs to the 13.8.27 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.27, printed p.963, using I.1.6(5) and I.2.3(1), pp.408,413.
The octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Cover
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open Atlas.G2.Natural

variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}

section Covers
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The original quotient is a quotient of the genuine Weyl module, compatibly
with its natural projection and the specified intrinsic component marking. -/
theorem weyl_quotient_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (OrthogonalCover.binaryNatural (ZMod 2)) eK) :
    ∃ p : Representation.IntertwiningMap (ρ.comp (modelActor hKH hK eK))
        (OrthogonalCover.binaryNatural (ZMod 2)), IsCover p ∧
      ∃ f : (OrthogonalCover.binaryAction (ZMod 2)).IntertwiningMap
          (ρ.comp (modelActor hKH hK eK)), Function.Surjective f ∧
        ∀ w, p (f w) = mk (ZMod 2) w := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨p, hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen _ eK hs
  obtain ⟨f, hf, he⟩ := OrthogonalCover.exists_quotient (ZMod 2) p hp
  exact ⟨p, hp, f, hf, he⟩

/-- The six-dimensional natural and seven-dimensional Weyl alternatives on the
whole source quotient, with the covering projection retained in both cases. -/
theorem natural_or_weyl_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (OrthogonalCover.binaryNatural (ZMod 2)) eK) :
    ∃ p : Representation.IntertwiningMap (ρ.comp (modelActor hKH hK eK))
        (OrthogonalCover.binaryNatural (ZMod 2)), IsCover p ∧
      ((∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] Space (ZMod 2),
        (∀ a v, E (ρ (modelActor hKH hK eK a) v) =
          OrthogonalCover.binaryNatural (ZMod 2) a (E v)) ∧ ∀ v, E v = p v) ∨
       (∃ E : TraceZero (ZMod 2) ≃ₗ[ZMod 2] Additive (Source.Utilde H V₃ V₁),
        (∀ a w, E (OrthogonalCover.binaryAction (ZMod 2) a w) =
          ρ (modelActor hKH hK eK a) (E w)) ∧ ∀ w, p (E w) = mk (ZMod 2) w)) := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨p, hp, f, hf, he⟩ := weyl_quotient_of_section hKH hK ρ hρ hgen eK hs
  refine ⟨p, hp, ?_⟩
  by_cases hk : p.toLinearMap.ker = ⊥
  · let E := LinearEquiv.ofBijective p.toLinearMap ⟨LinearMap.ker_eq_bot.mp hk, hp.1⟩
    exact Or.inl ⟨E, fun a v => LinearMap.congr_fun (p.isIntertwining' a) v, fun _ => rfl⟩
  · have hd := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1, finrank_top, finrank_space] at hd
    have hpos : 0 < Module.finrank (ZMod 2) p.toLinearMap.ker := by
      have hn : Module.finrank (ZMod 2) p.toLinearMap.ker ≠ 0 :=
        fun hz => hk (Submodule.finrank_eq_zero.mp hz)
      omega
    have hle := LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf
    rw [OrthogonalCover.finrank_traceZero] at hle
    have hdim : Module.finrank (ZMod 2) (TraceZero (ZMod 2)) =
        Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := by
      rw [OrthogonalCover.finrank_traceZero]
      omega
    let E := LinearEquiv.ofBijective f.toLinearMap
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf, hf⟩
    exact Or.inr ⟨E, fun a w => LinearMap.congr_fun (f.isIntertwining' a) w, he⟩

end Covers

/-- The original elementary subgroup U_H has rank at most eight. This supplies
the upper bound to the literal subgroup filtration of 13.8.27. -/
theorem rank_le_eight_of_section
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (OrthogonalCover.binaryNatural (ZMod 2)) eK)
    (hline : V₁ ≤ Source.UH H V₃) (hcard : Nat.card V₁ = 2) :
    Representation.BinaryOffender.rank (Source.UH H V₃) ≤ 8 := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨_, _, f, hf, _⟩ := weyl_quotient_of_section hKH hK ρ hρ hgen eK hs
  apply rank_le_eight_of_quotient (Source.UH H V₃) V₁ hline hcard
  exact (LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf).trans_eq
    (OrthogonalCover.finrank_traceZero (ZMod 2))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Cover
end
