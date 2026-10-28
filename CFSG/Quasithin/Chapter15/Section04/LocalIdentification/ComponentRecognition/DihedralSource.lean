module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition.Intrinsic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DihedralPSL2
public import Theory.GroupTheory.DihedralGeneratedFactor

/-!
# The central four-group and the adequate dihedral source branch

The original central four-group injects into the O₃′ quotient by F.6.11 and
its trivial intersection with O₂. Its image lies in the center of the original
Sylow image. A dihedral group of order eight has center of order two, excluding
the added PSL₂ branch without either local S₄ assertion. Thus the adequate
universal source input supplies the original full alternatives on this actual
15.4.22 configuration.

Source: Aschbacher–Smith, F.6.11/18 and 15.4.22, printed pp.306,309–310,1165.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open FFBranch.ClassificationComparison
namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {I : Type u} [Group I] [Finite I]
/-- The source central four-group excludes the added dihedral PSL₂ row
in the literal three-prime quotient, before any component recognition. -/
theorem no_dihedralPSL2Row_of_central_four {A B : Subgroup I} (triple : ChapterF.IsGoldschmidtTriple A B)
    (S : Sylow 2 I) (hS : A ⊓ B = (S : Subgroup I)) (Z : Subgroup I)
    (hZS : Z ≤ (S : Subgroup I)) (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I))
    (hZcard : Nat.card Z = 4) (hZQ : Z ⊓ pCore 2 I = ⊥)
    (r : FSource.DihedralPSL2Row
      (S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 I)))) : False := by
  let π := QuotientGroup.mk' (pPrimeCore 3 I)
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 I))
  have hinj := star_injective_on_four triple S hS Z hZS hZQ
  let j : Z →* Subgroup.center T :=
    { toFun := fun z => ⟨⟨π z, ⟨z, hZS z.property, rfl⟩⟩, by
        apply Subgroup.mem_center_iff.mpr
        intro t
        obtain ⟨x, hx, he⟩ := t.property
        apply Subtype.ext
        change (t : I ⧸ pPrimeCore 3 I) * π (z : I) = π (z : I) * t
        rw [← he, ← π.map_mul, ← π.map_mul]
        exact congrArg π (((hSZ hx) z z.property).symm)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact π.map_one
      map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; exact π.map_mul a b }
  have hj : Function.Injective j := by
    intro a b he
    apply hinj
    exact congrArg (fun x : Subgroup.center T => ((x : T) : I ⧸ pPrimeCore 3 I)) he
  have hc : Nat.card (Subgroup.center T) = 2 := by
    obtain ⟨es⟩ := r.sylow
    exact DihedralGroup.center_card_of_equiv (n := 2) (by decide) es
  have hn := Nat.card_le_card_of_injective j hj
  rw [hZcard, hc] at hn
  omega

/-- On the genuine central-four configuration, the adequate classifier
already gives the original alternatives on the literal quotient generators. -/
theorem full_alternatives_of_adequate_central_four {κ : GroupClass.{u}}
    (source : FSource.AdequateClassificationInput κ) (hI : IsSQTK κ I)
    {A B : Subgroup I} (triple : ChapterF.IsGoldschmidtTriple A B)
    (S : Sylow 2 I) (hS : A ⊓ B = (S : Subgroup I)) (Z : Subgroup I)
    (hZS : Z ≤ (S : Subgroup I)) (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I))
    (hZcard : Nat.card Z = 4) (hZQ : Z ⊓ pCore 2 I = ⊥) :
    let T := S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 I))
    FSource.Alternative (threePrimeImage A) (threePrimeImage B) T ∨
      FSource.Alternative (threePrimeImage B) (threePrimeImage A) T := by
  let π := QuotientGroup.mk' (pPrimeCore 3 I)
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 I))
  have hinj := star_injective_on_four triple S hS Z hZS hZQ
  have preserved : F611Preserved A B := by
    rcases (f611Conclusion_of_goldschmidt triple).alternatives with hp | hc
    · exact hp
    · obtain ⟨e⟩ := hc.symmetric_three
      have hd := Subgroup.card_dvd_of_injective
        (e.toMonoidHom.comp (π.comp Z.subtype)) (e.injective.comp hinj)
      rw [hZcard, Nat.card_eq_fintype_card, Fintype.card_perm] at hd
      norm_num at hd
  let q : ThreePrimeSQTKQuotient κ (threePrimeQuotient I) :=
    { Cover := I, sqtk := hI, equiv := MulEquiv.refl _ }
  obtain ⟨U, hU, hm⟩ := source (threePrimeQuotient I) _ _ preserved.triple q
  have he : U = T := by
    apply Sylow.ext
    rw [← hU, preserved.intersection, hS]
    rfl
  subst U
  have hn := no_dihedralPSL2Row_of_central_four triple S hS Z hZS hSZ hZcard hZQ
  rcases hm with hm | hm <;> rcases hm with hm | hr
  · exact Or.inl hm
  · obtain ⟨r⟩ := hr
    exact (hn r).elim
  · exact Or.inr hm
  · obtain ⟨r⟩ := hr
    exact (hn r).elim

end CFSG.Quasithin.Chapter15.Section04.SourceRecognition
