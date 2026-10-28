module
public import Theory.SpecificGroups.Janko3.Model.FrattiniEight
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.FrattiniEight
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuterSymplectic

/-!
# Excluding the remaining sporadic outer sections in degree four

The actual J₃ and McL Sylow two-subgroups have Frattini quotients of order at most
eight. Sylow restriction and the Burnside basis kernel preserve a nonsolvable
simple outer section, while GL₃(2) is too small to contain GL₄(2). Descent
through the entire center transfers both exclusions to the original component.
The final inspection retains the literal model identifications and is applied
to the chosen odd actor in `DoubleNaturalExcludedFourOddNormalizers`.

Source: Aschbacher–Smith 4.4.10–11 and 12.1.9, printed pp.621 and 793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels

private theorem no_small_frattini_section
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (P : Sylow 2 Q) (hP : Nat.card (P ⧸ frattini P) ≤ 8)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 8)) :
    ¬ Function.Surjective f := by
  intro hf
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

/-- The three-generator Sylow bound excludes the actual J₃ outer section. -/
theorem janko_three
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.Janko3.Model)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 8)) :
    ¬ Function.Surjective f :=
  no_small_frattini_section (default : Sylow 2 Q)
    (Sporadic.Janko3.TwoLocal.FrattiniEight.sylow_frattini_card_le_eight e _) U f

/-- The certified McL word subgroup supplies the same outer-section obstruction. -/
theorem mcl
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.LeechRelated.McL.Carrier)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 8)) :
    ¬ Function.Surjective f :=
  no_small_frattini_section (default : Sylow 2 Q)
    (Sporadic.LeechRelated.McL.FrattiniEight.sylow_frattini_card_le_eight_of_equiv e _) U f

/-- Central descent preserves the full original component center. -/
theorem janko_three_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f) : ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  rintro ⟨e⟩
  exact janko_three e _ (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

/-- Central descent preserves the full original component center. -/
theorem mcl_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f) : ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.McL.Carrier) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  rintro ⟨e⟩
  exact mcl e _ (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open ChapterA.Section02 ClassificationModels BinaryLinear.OuterCyclic

/-- The two remaining actual outer-section families, both of Lie type. -/
inductive FourLieOuterModel (Q : Type*) [Group Q] : Prop
  | g2 (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At Q p)
  | unitary_five_four (iso : ClassicalGroup.IsPSU Q 5 4)

/-- Inspect the literal original section, retaining the same component and full center. -/
theorem four_lie_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : FourNonsymplecticOuterModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 4,
      Function.Surjective f) : FourLieOuterModel (K ⧸ center K) := by
  have ha : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f := by
    obtain ⟨U,f,hf⟩ := ho
    let e := Chapter12.Section02.ChosenModule.doubledFour_linearEquiv
    exact ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩
  cases hm with
  | g2 p hp hpodd e => exact .g2 p hp hpodd e
  | unitary_five_four e => exact .unitary_five_four e
  | janko_three e => exact (FourOuterModels.janko_three_cover_exclusion ha e).elim
  | mcl e => exact (FourOuterModels.mcl_cover_exclusion ha e).elim

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
