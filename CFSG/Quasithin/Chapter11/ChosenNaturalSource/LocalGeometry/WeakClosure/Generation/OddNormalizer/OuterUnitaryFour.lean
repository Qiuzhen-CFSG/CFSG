module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedOuter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.UnitaryFour
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport
public import Theory.GroupTheory.SylowOuterFrattiniSections
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms

/-!
# Excluding both actions on binary unitary-four component covers

For fixed fields larger than two the actual Sylow automorphism group is
solvable. At the binary endpoint its Frattini quotient has order eight,
so a nonsolvable simple outer section has order at most 168. The original
natural simple quotient has order at least 20160. Central descent retains
the full component cover, and the existing inner-placement exclusion
handles the other action. Thus the entire binary PSU₄ row is impossible.

Source applies this result to the literal elementary Hall kernel. The
remaining B-only and sporadic exclusions stay with this owner.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Theory.SpecificGroups.ClassicalUnitary

private theorem unitary_four_no_large_outer_section
    {Q R : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ¬ Group.IsSolvable R) (hsize : 168 < Nat.card R)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n))
    (U : Subgroup (MulAut.Outer Q)) (f : U →* R) (hf : Function.Surjective f) : False := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Q e.toEquiv
  let P : Sylow 2 Q := Classical.choice inferInstance
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* P' := P.equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  by_cases hn1 : n = 1
  · have hP : Nat.card (P ⧸ frattini P) = 2 ^ 3 := by
      rw [SylowFrattiniBounds.card_congr a,
        UnitaryFourSylow.FrattiniExact.projective_frattini_card
          F J (by omega) hcard hconj P', hn1]
    let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
    let : IsElementaryAbelian 2 (P ⧸ frattini P) :=
      isElementaryAbelian_quotient_frattini (p := 2)
    have hd := MulAut.simple_outer_section_card_dvd_frattini_aut P hR U f hf
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 3 hP] at hd
    norm_num [Fin.prod_univ_succ] at hd
    have hle := Nat.le_of_dvd (by decide : 0 < 168) hd
    omega
  · let : Group.IsSolvable (MulAut P') :=
      FourSylowStructure.projective_sylow_mulAut_isSolvable
        F J (by omega) hcard hconj P'
    let : Group.IsSolvable (MulAut P) := Group.isSolvable_of_surjective
      (f := (MulAut.congr a.symm).toMonoidHom) (MulAut.congr a.symm).surjective
    let : Group.IsSolvable (MulAut.Outer Q) := MulAut.outer_isSolvable_of_sylow_aut P
    exact hR (Group.isSolvable_of_surjective hf)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The original natural simple quotient cannot be a section of the outer
  automorphism group of any binary unitary-four component cover. -/
theorem moved_outer_not_binary_unitary_four {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) : False := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient L) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (L ⧸ pCore 2 L))) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hsize : 168 < Nat.card (coreCentralQuotient L) := by
    have hl := quotient_card_ge D S
    have hz := Nat.le_of_dvd (by decide : 0 < 3) (quotient_center_card_dvd_three D S)
    have hc := card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))
    change 168 < Nat.card ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L))
    nlinarith
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact unitary_four_no_large_outer_section
    (Group.IsPerfect.not_isSolvable (coreCentralQuotient L)) hsize hn hm
    (U.map j) (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

open Chapter4 Chapter4.Section04
/-- Both possible actual actions are excluded; the selected component cannot
  have binary unitary-four central quotient, with its full cover retained. -/
theorem moved_component_not_binary_unitary_four {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) : False := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨_,_,_,_,himage,_⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    exact himage.not_binary_unitary_four D S hn hm
  · exact moved_outer_not_binary_unitary_four D S K hK ho hn hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
