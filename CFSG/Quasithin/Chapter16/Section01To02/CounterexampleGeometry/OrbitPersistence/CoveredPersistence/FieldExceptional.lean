module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.ModelAlternatives
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Divisibility by three for the exceptional field-derived endpoints

The opposite-vector stabilizer in the actual split-octonion G₂ model contains
SL₂(F). The central root Levi in the genuine graph-field triality carrier is
PSL₂ over its base field: the proved pinned Geck maps supply this identification,
including the elementary fixed-point restriction and faithful central descent.
In characteristic two SL₂ and PSL₂ are canonically isomorphic.

The opposite binary transvections in each rank-one subgroup have a commutator
of order three. An injective homomorphism induces an injection on derived
subgroups, so this gives divisibility by three in the requested actual derived
groups. The argument includes G₂(2)′ and ³D₄(2)′ without a perfectness assumption.
Finally, transport through the given model isomorphisms supplies both contracts.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.7(3a) and the covered case of 16.2.6(1), printed pp.1172–1174.
The triality rank-one construction follows GLS3 §§2.4 and 2.6, as documented
in the imported intrinsic modules.
-/

public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
open Subgroup
open Theory.SpecificGroups.Classical.EvenDerivedThree

private theorem commutator_card_dvd_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) :
    Nat.card (commutator A) ∣ Nat.card (commutator B) := by
  have hle : (commutator A).map f ≤ commutator B := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let f' : commutator A →* commutator B :=
    (f.comp (commutator A).subtype).codRestrict (commutator B)
      (fun x => hle ⟨x, x.property, rfl⟩)
  apply card_dvd_of_injective f'
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- The actual G₂(2ⁿ)′ endpoint has order divisible by three, including n = 1. -/
theorem FieldDerivedThreeInput.g2 : FieldDerivedThreeInput .g2 := by
  intro M hM hfin n _ hmodel
  obtain ⟨F, hF, hfinF, hq, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hq)
  let H := Atlas.G2.PairStabilizer.fixingPair (F := F)
  let eH : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* H :=
    (Theory.PSL2.sl2QuotientEquiv F).symm.trans
      Atlas.G2.PairStabilizer.fixingPairEquivSL2.symm
  let f := e.symm.toMonoidHom.comp (H.subtype.comp eH.toMonoidHom)
  have hf : Function.Injective f :=
    e.symm.injective.comp (Subtype.val_injective.comp eH.injective)
  exact (three_dvd_card_psl_commutator (F := F) (show (0 : Fin 2) ≠ 1 by decide)).trans
    (commutator_card_dvd_of_injective f hf)

/-- The actual derived subgroup of the graph-field carrier ³D₄(2ⁿ) has order
divisible by three, including the field of order two. -/
theorem FieldDerivedThreeInput.triality : FieldDerivedThreeInput .triality := by
  intro M hM hfin n _ hmodel
  obtain ⟨P, hq, ⟨e⟩⟩ := hmodel
  have hp : P.prime = 2 := by
    apply Nat.prime_eq_prime_of_dvd_pow P.prime_prime Nat.prime_two
    rw [← hq]
    exact dvd_pow_self _ (Nat.ne_of_gt P.exponent_pos)
  let F := GaloisField P.prime P.exponent
  let : CharP F 2 := hp ▸ inferInstanceAs (CharP F P.prime)
  let H := Triality.Standard.Parabolics.levi P .central
  let eH : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    Triality.Standard.Parabolics.leviCentralEquivPSL2OfPinnedMaps P hp
      (Triality.Standard.Parabolics.pinnedRankOneMaps P hp)
  let f := e.symm.toMonoidHom.comp (H.subtype.comp eH.symm.toMonoidHom)
  have hf : Function.Injective f :=
    e.symm.injective.comp (Subtype.val_injective.comp eH.symm.injective)
  exact (three_dvd_card_psl_commutator (F := F) (show (0 : Fin 2) ≠ 1 by decide)).trans
    (commutator_card_dvd_of_injective f hf)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence

end
