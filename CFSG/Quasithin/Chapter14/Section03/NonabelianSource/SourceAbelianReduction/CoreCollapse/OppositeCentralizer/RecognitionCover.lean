module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionSmallModels
public import Theory.SpecificGroups.PSL3Four.CentralCover.SylowCenter

/-!
# Excluding the central PSL₃(4) cover on the original Sylow subgroup

The component center has order two. Its Sylow subgroup therefore has order
128 and elementary center of order eight. Subnormal Sylow intersection embeds
it onto the original Sylow subgroup of the opposite centralizer. Its center
would embed in that subgroup's marked omega plane of order four, a contradiction.
The quotient map is the original component quotient followed by field transport.

Source: Aschbacher--Smith 14.3.22, printed p.999; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s


/-- The nontrivial central L₃(4) cover has too large an elementary Sylow center
for the original marked omega plane. -/
theorem source_triple_not_linearThreeFour_cover
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hneZ : center D ≠ ⊥) (hz : center D = pCore 2 D) :
    ¬ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 3 4 := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hEfield
  let := hEfinite
  let C := ResidualFusion.C (tripleProduct d a)
  have hZc : Nat.card (center D) = 2 := by
    have hd := (source_triple_component_center
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD).2.2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · exact (hneZ (card_eq_one.mp hh)).elim
    · exact hh
  let : Fintype E := Fintype.ofFinite E
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let aE : E ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Matrix.PSL3Four.card_F] using hE)
  let eM := eD.trans (Atlas.fieldEquivPSL 3 aE)
  let q := eM.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := eM.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center D := by
    ext x
    change eM (QuotientGroup.mk' (pCore 2 D) x) = 1 ↔ x ∈ center D
    rw [←eM.map_one,eM.injective.eq_iff]
    change (x : D ⧸ pCore 2 D) = 1 ↔ x ∈ center D
    rw [QuotientGroup.eq_one_iff,hz]
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,M₁,hS,hSc,hM₁,h115,_,_⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  obtain ⟨hPc,hPe,hPZ⟩ := Matrix.PSL3Four.double_cover_sylow_center q hq
    (hk ▸ le_refl _) (hk ▸ hZc) P
  let P₀ := (P : Subgroup D).map D.subtype
  have hPS : P₀ ≤ (S : Subgroup C) := by
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ (S : Subgroup C).subgroupOf D
    rwa [←hP]
  have heq : P₀ = (S : Subgroup C) := eq_of_le_of_card_ge hPS (by
    rw [hSc,show Nat.card P₀ = Nat.card P from card_map_of_injective D.subtype_injective,hPc])
  let ePS : P ≃* S := ((P : Subgroup D).equivMapOfInjective D.subtype D.subtype_injective).trans
    (MulEquiv.subgroupCongr heq)
  let eZ := centerCongr ePS
  have hSZ : Nat.card (center S) = 8 := (Nat.card_congr eZ.toEquiv).symm.trans hPZ
  let := hPe
  let : IsElementaryAbelian 2 (center S) :=
    IsElementaryAbelian.of_surjective eZ.toMonoidHom eZ.surjective
  let j : center S →* omegaCenterIn (S : Subgroup C) :=
    ((S : Subgroup C).subtype.comp (center S).subtype).codRestrict _ (by
      intro x
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨x.val.property,?_,?_⟩
      · intro y hy
        exact congrArg (S : Subgroup C).subtype (mem_center_iff.mp x.property ⟨y,hy⟩)
      · exact congrArg (S : Subgroup C).subtype
          (elemPow_eq_one_of_isElementaryAbelian (x : S) x.property))
  have hj : Function.Injective j := fun x y hh =>
    Subtype.ext (Subtype.ext (show ((x : S) : C) = ((y : S) : C) from congrArg (fun t : omegaCenterIn (S : Subgroup C) => (t : C)) hh))
  have hOc : Nat.card (omegaCenterIn (S : Subgroup C)) = 4 := by
    rw [←card_map_of_injective C.subtype_injective,
      NilesRankOneKernel.omegaCenterIn_map_injective _ C.subtype_injective,hS,hlocal.omega_center]
    let := isKleinFour_closure_pair_of_orderOf z (tripleProduct d a)
      h115.involution hlocal.involution
      (fun hh => hlocal.nonfusion (hh ▸ IsConj.refl z))
      (mem_centralizer_singleton_iff.mp
        (hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))))
    exact IsKleinFour.card_four
  have hh := Nat.card_le_card_of_injective j hj
  rw [hSZ,hOc] at hh
  omega


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
