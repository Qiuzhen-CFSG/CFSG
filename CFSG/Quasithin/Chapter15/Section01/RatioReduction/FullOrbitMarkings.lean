module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitEndpoints
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralMarking
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TransitivePair
/-!
# Uniform dihedral markings in the original full orbit

The actual endpoint producer gives two cyclic-three or cyclic-five factors.
Ambient conjugation identifies their literal carriers and supports, so the
prime and module dimension agree throughout the orbit. This retains the
original kernels and generating involutions, together with their inversion
and the dihedral equivalences.

Source: Aschbacher--Smith 15.1.2(3), printed p.1086.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_transitive_uniform_dihedral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      Nat.card d.Index = 2 ∧ ∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
        ∀ i, ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
          CyclicSource.DihedralMarking l p m := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd π hp hs ht hmore
  obtain ⟨hc,he⟩ := source_localAction_transitive_factor_endpoints hG T hempty hM hmany hJ
    U c d hd π hp ht hmore
  have hmark (i : d.Index) : ∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
      ∃ l : CyclicSource.LocalGeneration (d.factor i).action, CyclicSource.DihedralMarking l p m := by
    obtain ⟨l,hl⟩ := he i
    obtain ⟨p,m,hpm,hm⟩ := l.marking_of_endpoints hl
    exact ⟨p,m,hpm,l,hm⟩
  let i : d.Index := Classical.arbitrary d.Index
  obtain ⟨p,m,hpm,l,hl⟩ := hmark i
  refine ⟨hc,p,m,hpm,fun j => ?_⟩
  obtain ⟨q,n,hqn,k,hk⟩ := hmark j
  obtain ⟨g,hg⟩ := ht i j
  have hj := hp g i
  rw [hg] at hj
  let e := c.factorCarrierEquivOfConjugate d g hj
  obtain ⟨ei⟩ := hl.dihedral
  obtain ⟨ej⟩ := hk.dihedral
  have hcard : 2 * p = 2 * q := by
    calc
      2*p = Nat.card (d.factor i).Carrier :=
        (Nat.card_congr ei.toEquiv).trans DihedralGroup.nat_card |>.symm
      _ = Nat.card (d.factor j).Carrier := Nat.card_congr e.toEquiv
      _ = 2*q := (Nat.card_congr ej.toEquiv).trans DihedralGroup.nat_card
  have hpq : q = p := by omega
  have hdim := c.transitive_factor_dimensions d π hs ht i j
  rw [hl.dimension,hk.dimension] at hdim
  have hnm : n = m := by omega
  subst q
  subst n
  exact ⟨k,hk⟩
end CFSG.Quasithin.Chapter15.Section01
