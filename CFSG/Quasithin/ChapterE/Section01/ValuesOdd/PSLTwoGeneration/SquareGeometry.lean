module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport

/-!
# Reduction of the prime-square local escape problem

The prescribed normal PSL₂(p²) core is mapped faithfully to the canonical
inner layer of PΓL₂. Its linear kernel has index one or two. The first case
is an actual PSL₂ or PGL₂ model; the second retains the full field image and
allows arbitrary mixed extensions. Isomorphism transport then returns the
literal E-member and its noncontainment to the original group.

The two local calculations remain explicit premises. This module does not
yet prove the prime-square branch of E.1.14(6). In particular neither the
index calculation nor the rank bound supplies an escaping E-member.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2), E.1.2 and E.1.14(6), printed pp.33, 209--210 and 214;
the last cites Aschbacher (1982), Lemma 4.10.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry

open Subgroup GorensteinWalter

/-- Assembly for the two genuine local calculations. The normal socle and
its trivial centralizer suffice for the reduction. The source SQTK, simple
socle and Sylow-supplement hypotheses can therefore be retained by the caller
without any additional structural premise for this assembly. -/
theorem largeFamilyEscape_of_model_calculations
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hL : ClassicalGroup.IsPSL L 2 (p ^ 2))
    (hC : centralizer (L : Set G) = ⊥)
    (hlinear : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ 2 →
      ∀ (S : Subgroup (PGammaL2 F)) [Finite S],
        (Nonempty (S ≃* PSL2 F) ∨ Nonempty (S ≃* PGL2 F)) →
        ∀ T : Sylow 2 S, LargeFamilyEscapeAt T)
    (hfield : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ 2 →
      ∀ (S : Subgroup (PGammaL2 F)) [Finite S], pGammaL2PSLRange F ≤ S →
        (pGammaL2LinearKernel F S).index = 2 →
        Function.Surjective (pGammaL2FieldProjection F S) →
        ∀ T : Sylow 2 S, LargeFamilyEscapeAt T) :
    ∀ T : Sylow 2 G, LargeFamilyEscapeAt T := by
  obtain ⟨F, _, _, hF, f, hf, _hcore, hPSL⟩ :=
    exists_semilinear_model L hp hodd hL hC
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  let : Finite f.range := Finite.of_injective e.symm e.symm.injective
  apply largeFamilyEscape_of_equiv e.symm
  rcases linearKernel_index_eq_one_or_two hp hF f.range with hindex | hindex
  · exact hlinear F hF f.range
      (linear_model_of_kernel_index_one hp hodd hF f.range hPSL hindex)
  · exact hfield F hF f.range hPSL hindex
      (fieldProjection_surjective_of_index_two hp hF f.range hindex)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry
