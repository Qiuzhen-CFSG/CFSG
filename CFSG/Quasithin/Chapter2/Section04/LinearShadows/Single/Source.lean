module
public import CFSG.Quasithin.Chapter2.Section04.Statement
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralEvenSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralOddReduction
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedDeltaPairSource
/-!
# Exclusion of the original single linear-block branch

The original torus setup and involution-closure theorem select the marked
field involution. The centerless transfer argument and the two original
noncentral field branches exhaust the possibilities. Every geometric,
fusion, cardinality and field-action premise is supplied by its source
producer; no shadow classification is assumed.

Source: Aschbacher–Smith, Theorem 2.4.7, printed pp.529–539.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.single_linear_source_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (_hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (_hcounter : ¬IsTheorem241Model G) (hsingle : d.L0=d.block)
    {n:ℕ} (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) : False := by
  have hLin := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective).symm
  obtain ⟨c⟩ := source_cyclic_torus_setup d hG T hST hsingle hLin hM hTM hu
  have hclosed := c.involution_fusion_closed d hG T hST hsingle hLin hM hTM hu
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle hL).1
  obtain ⟨s,hs2,hs,hsR⟩ := c.exists_field_involution_of_fusion hG hST.le hindex hclosed
  by_cases hZ : center (d.block.map d.H.subtype)=⊥
  · exact source_centerless_false d hG T hST hsingle hLin hM hTM hu c hZ s hs hs2 hsR
  · by_cases hn : 2<n
    · exact source_noncentral_large_false_of_setup d hG T hST hsingle hLin hM hTM hu c hZ hn
    · have hn2 : n=2 := by have hh:=hL.1;omega
      apply source_noncentral_odd_false_of_noncommuting_delta_pair d hG T hST hsingle hLin hM hTM hu c s hs hs2 hsR hZ
        (by rw [hn2];decide)
      intro x hxT hxS hxB u huDelta
      exact source_field_fixed_noncommuting_delta_pair d hG T hST hsingle hLin hM hTM hu c s hs
        ((orderOf_coe s).trans hs2) hsR hZ x hxT hxS hxB u huDelta
end CFSG.Quasithin.Chapter2
