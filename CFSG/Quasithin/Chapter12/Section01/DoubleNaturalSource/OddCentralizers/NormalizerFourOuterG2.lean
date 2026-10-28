module
public import Theory.SpecificGroups.G2.OddFrattiniEight
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuterSporadic

/-!
# Excluding the odd-prime G₂ outer sections in degree four

The actual odd-prime G₂ Sylow two-subgroups have Frattini quotients of order
at most eight. Sylow restriction preserves a nonsolvable simple outer section,
and the solvable Burnside basis kernel preserves it on this quotient. Its
automorphism order is too small for GL₄(2). Perfect central descent applies
the obstruction through the entire center of the original component.

The original odd-normalizer consumer therefore retains only its constrained
SL₅(2) star or the actual PSU₅(4) outer section. No global Schreier premise
or replacement component is used. Source: Aschbacher--Smith 4.4.10--11 and
12.1.9, printed pp.621,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels
open ClassificationModels

/-- The diagonal orthogonal calculation excludes every odd-prime G₂ outer section. -/
theorem g2_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : IsG2At Q p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 8)) :
    ¬ Function.Surjective f := by
  intro hf
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  have hP : Nat.card (P ⧸ frattini P) ≤ 8 := by
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Atlas.G2.OddFrattiniEight.frattini_card_le_eight ho hF (P.mapSurjective e.surjective)
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hd := MulAut.simple_outer_section_card_dvd_frattini_aut P
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))) U f hf
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn3 : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [←hn] using hP
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn,
    nat_card_alternatingGroup] at hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ,Nat.factorial] at hd

/-- The G₂ obstruction retains the full center of the original perfect component. -/
theorem g2_odd_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f) :
    ∀ p : ℕ, p.Prime → Odd p → ¬ IsG2At (K ⧸ center K) p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hpodd hm
  exact g2_odd hp hpodd hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open BinaryLinear.OuterCyclic

/-- Only the actual PSU₅(4) model remains in the original outer-section branch. -/
theorem four_outer_model_unitary_five
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : FourLieOuterModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 4,
      Function.Surjective f) : ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  cases hm with
  | unitary_five_four e => exact e
  | g2 p hp hpodd e =>
    obtain ⟨U,f,hf⟩ := ho
    let a := Chapter12.Section02.ChosenModule.doubledFour_linearEquiv
    exact (FourOuterModels.g2_odd_cover_exclusion
      ⟨U,a.toMonoidHom.comp f,a.surjective.comp hf⟩ p hp hpodd e).elim
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
