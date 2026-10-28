module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.LinearThreeClosureChoice
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.NormalClosureBranch

/-!
# The remaining cubic suitable-choice branch

From the full original setup at p=3, the source comparison chooses the
actual closure component. A normal residual gives the completed solvable
normalizer; an exchanged component gives the completed symmetric-five or
binary linear-three normalizer. Thus only the invariant PSL₄(2) and
PSL₅(2) automorphism quotients remain. The returned invariant alternative
concerns the literal Mc/O₂(Mc), not just the component's Sylow join.

The last theorem applies the normalizer result to the original first
support and constructs the suitable involution in every completed branch.
It leaves exactly the invariant parabolic normalizer for the cubic assembly;
the PSL₂(16) full-image argument remains necessary before deducing p=3
in the complete source family. Neither this reduction nor its suitable
consumer asserts the unfinished source theorem.

Source: Aschbacher--Smith 14.6.14--17, pp.1033--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))


include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.16 at p=3, reduced to the two invariant automorphism models.
All exchanged component and layer premises are discharged by their source producers. -/
theorem source_normalizer_or_invariant_cubic_closure
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    (S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G)) ∨
    (((residualClosure H Mc).subgroupOf Mc).IsCComponent ∧
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) := by
  by_cases he : residualClosure H Mc = residual H
  · exact Or.inl (source_normalizer_of_normal_residual
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d rfl hmax he)
  obtain ⟨P,L,hi,hL,hcl,hn,hcomm⟩ := source_strict_closure_component_orbit
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d he
  by_cases hTL : (T : Subgroup G) ≤ normalizer (L : Set G)
  · have ho : componentOrbit L (T : Subgroup G) = L := le_antisymm
      (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL)
      (le_componentOrbit L (T : Subgroup G))
    have hPL : P ≤ L := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq (hcl.trans ho)
    rw [ho] at hn hcomm
    have hr := source_invariant_cubic_closure_alternative
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax
      hi hL.mem hL.quasisimple hn hPL hcomm (hcl.trans ho)
    exact Or.inr ⟨hr.1,hr.2.1⟩
  · have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hunique.symm ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans hi.overgroup
    let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P Mc L :=
      { toLocalInput := hi
        sqtk := hG.twoLocal_sqtk hMc.1.1
        component := hL.mem
        quasisimple := hL.quasisimple
        orbit_normal := hn
        complement_le_orbit := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq hcl
        orbit_commutator := hcomm
        noncentral := hL.noncentral_component_core
        not_invariant := hTL
        sylow_two := ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩ }
    have hm := source_swapped_closure_model hG T hempty hM hunique hmany hcard e hab H hH hs hprim d.prime hmax
    rw [←hcl] at hm
    obtain ⟨_hr,_,hlayer⟩ := source_strict_exchanged_closure_layer
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d hmax he L hL.mem.1 hL.mem.2 hm
    exact Or.inl (source_normalizer_cubic_exchanged_component
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax
      L hL.mem.1 hL.mem.2 hL.quasisimple hm hlayer)

/-- The actual suitable involution exists unless the original closure is
one of the two remaining invariant component models. -/
theorem source_exists_suitable_or_invariant_cubic_closure
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    (∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G)) ∨
    (((residualClosure H Mc).subgroupOf Mc).IsCComponent ∧
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) := by
  rcases source_normalizer_or_invariant_cubic_closure
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax with hn | hi
  · left
    obtain ⟨hWU,hZW,hKW,hSW,hi,hsep,hff⟩ := source_exchanged_support_premises
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
    have hK := source_residual_le_fittingPreimage
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d
    exact source_exists_suitable_of_fixed_free_support
      hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
        ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hK hWU hZW hKW hSW inf_le_left hi hn.2 hsep hff
  · exact Or.inr hi

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
