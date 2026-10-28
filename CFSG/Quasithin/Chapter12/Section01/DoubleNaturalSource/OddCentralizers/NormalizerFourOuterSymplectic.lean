module
public import Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuter

/-!
# Excluding the binary symplectic outer section

The actual GL₄(2) section of the original component's outer automorphism group
has order divisible by five. After descent through its entire center, Sylow
restriction preserves this nonsolvable simple section. The characteristic
Frattini-centralizer calculation for Sp₆(2) excludes that prime divisor from
the Sylow automorphism group, giving a contradiction.

The resulting four-family inspection retains the original quotient models:
odd-prime G₂, PSU₅(4), J₃ and McL. Its chosen-orbit consumer is in
`DoubleNaturalExcludedFourOddNormalizers`; the constrained SL₅(2) star remains
separate. Source: Aschbacher--Smith 4.4.10--11 and 12.1.9, pp.621 and 793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels
open ClassificationModels Theory.SpecificGroups

/-- The characteristic Frattini-centralizer image prevents a factor-five
Sylow automorphism, excluding the binary symplectic outer section. -/
theorem symplectic_six_binary
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSp Q 3 2)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 8)) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))) U f hf
  apply SymplecticSix.BinarySylowAutomorphisms.not_five_dvd_sylow_aut_of_equiv hF e P
  apply dvd_trans ?_ hd
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The binary symplectic exclusion descends through the component's full center. -/
theorem symplectic_six_binary_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f) : ¬ ClassicalGroup.IsPSp (K ⧸ center K) 3 2 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro hm
  exact symplectic_six_binary hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open ChapterA.Section02 ClassificationModels BinaryLinear.OuterCyclic

/-- The four remaining actual outer-section families after the binary symplectic exclusion. -/
inductive FourNonsymplecticOuterModel (Q : Type*) [Group Q] : Prop
  | g2 (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At Q p)
  | unitary_five_four (iso : ClassicalGroup.IsPSU Q 5 4)
  | janko_three (iso : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (iso : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

/-- Inspect the literal residual alternatives against the original outer section,
retaining the whole center of the same component. -/
theorem four_nonsymplectic_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : FourReducedOuterModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 4,
      Function.Surjective f) : FourNonsymplecticOuterModel (K ⧸ center K) := by
  have ha : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f := by
    obtain ⟨U,f,hf⟩ := ho
    let e := Chapter12.Section02.ChosenModule.doubledFour_linearEquiv
    exact ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩
  cases hm with
  | g2 p hp hpodd e => exact .g2 p hp hpodd e
  | symplectic_binary e => exact (FourOuterModels.symplectic_six_binary_cover_exclusion ha e).elim
  | unitary_five_four e => exact .unitary_five_four e
  | janko_three e => exact .janko_three e
  | mcl e => exact .mcl e

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
