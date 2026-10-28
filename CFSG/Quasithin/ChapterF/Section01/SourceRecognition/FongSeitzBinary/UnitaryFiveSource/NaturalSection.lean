module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryCover

/-!
# Natural coordinates on the actual unitary Frattini section

For q at least four, the original profile gives the actual section order
q^6 and its nontrivial irreducible SU3 action. Minimal-degree recognition
constructs a binary linear intertwiner with the natural three-space over
the given quadratic field. We retain its actor automorphism explicitly:
the projective panel square is transported through that same automorphism,
rather than silently changing the prescribed local marking.

This is a section realization, not a lift to the nonabelian radical or a
synchronization with the SL2 actor. The q=2 realization and the compatible
root labels remain separate obligations of this U5 source family.

Source: Fong--Seitz I (4D), (6A)(c); II (8.13)--(8.15), pp.203--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G X E : Type*} [Group G] [Group X] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split j)
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
  (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))

include e h hn hE hfixed hJ hconj hm hij hVi s ν hπ hπν hindexi hindexj hQi hderived hfrattini

/-- The natural-module conclusion is constructed on the literal source action. -/
theorem marked_natural_pullback :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    IsNatural J ((elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)).comp π) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hi := (QuadrangleStructure.marked_unitary_profile_of_cover Q split e h J hn hE hconj hJ
    hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini).2
  let : IsIrreducible ρ := hi
  let σ := ρ.comp π
  let : IsIrreducible σ := (irreducible_comp_surjective_iff π hπ ρ).mpr hi
  obtain ⟨_,hc,hnt⟩ := QuadrangleStructure.marked_unitary_section Q split e h J
    (by omega) hE hfixed hJ hm i j hij hVi hVj s ν hindexi hindexj hQi hderived hfrattini
  have hnσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨r,hr⟩ := hnt
    obtain ⟨g,rfl⟩ := hπ r
    refine ⟨g,fun he => hr ?_⟩
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) he)
  have hd : Module.finrank (ZMod 2) (Additive V) ≤ 6*n := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hcard
    have he : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2^(6*n) := by
      rw [←hcard]
      change Nat.card V = _
      rw [hc,←pow_mul,Nat.mul_comm n 6]
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) he).le
  exact MinimalDegree.isNatural_of_finrank_le J σ hn hE hconj hnσ hd

/-- Actual natural coordinates, with the full actor and the prescribed panel
marking both retained. The automorphism records the as-yet-unpinned labels. -/
theorem marked_natural_coordinates :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (a : J.specialSubgroup ≃* J.specialSubgroup)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ g, κ (π g) = a g) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) =
        J.specialToProjective (a.symm (κ r))) ∧
      ∀ r v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) r v) =
          Matrix.mulVec (κ r).val.val (c v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  have hnat := marked_natural_pullback Q split e h J hn hE hfixed hJ hconj hm i j hij
    hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hinj : Function.Injective π := by
    intro a b hab
    apply hnat.injective J
    exact congrArg (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)) hab
  obtain ⟨a,c,hc⟩ := hnat
  let k := MulEquiv.ofBijective π ⟨hinj,hπ⟩
  refine ⟨a,k.symm.trans a,c,?_,?_,?_⟩
  · intro g
    change a (k.symm (k g)) = a g
    rw [k.symm_apply_apply]
  · intro r
    have he := hπν (k.symm r)
    change ν (RootLocalCover.projection Q split j (k (k.symm r))) = _ at he
    simpa only [k.apply_symm_apply,MulEquiv.trans_apply,a.symm_apply_apply] using he
  · intro r v
    have he := hc (k.symm r) v
    change c (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj) (k (k.symm r)) v) = _ at he
    simpa only [k.apply_symm_apply,MulEquiv.trans_apply] using he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G E : Type*} [Group G] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split j)
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
  (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))

include h hn hE hfixed hJ hconj hm hij hVi s ν hπ hπν hindexi hindexj hQi hderived hfrattini

/-- Natural coordinates on the original quotient, with literal Q.q
representatives and the original projective panel marking. -/
theorem original_natural_coordinates :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (a : J.specialSubgroup ≃* J.specialSubgroup)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ g, κ (π g) = a g) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) =
        J.specialToProjective (a.symm (κ r))) ∧
      ∀ (g : generated L S) (hg : Q.q g ∈ rankOne Q split j) v,
        c (elementaryRepresentation (p := 2)
          (remainderFrattiniAction Q split j hVj) ⟨Q.q g,hg⟩ v) =
            Matrix.mulVec (κ ⟨Q.q g,hg⟩).val.val (c v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨a,κ,c,hcover,hpanel,hc⟩ := marked_natural_coordinates Q split (originalMarkedIso Q) h J
    hn hE hfixed hJ hconj hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  exact ⟨a,κ,c,hcover,hpanel,fun g hg v => hc ⟨Q.q g,hg⟩ v⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
