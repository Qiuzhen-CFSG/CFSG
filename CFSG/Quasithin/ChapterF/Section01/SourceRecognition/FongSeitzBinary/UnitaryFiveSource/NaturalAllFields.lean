module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.SmallNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryAllFields

/-!
# Actual unitary natural-section coordinates in every binary field

The original full actor and Frattini irreducibility give a nontrivial binary
representation of dimension 6n. For n at least two the existing minimum-degree
recognition applies; for n = 1 the small catalogue supplies the missing
natural coordinates. Transport through the actual generic cover keeps the
original projective panel square and literal Q.q representatives.

Thus the actual section is realized, including the nonperfect SU₃(2) case,
without a natural-module or injective-cover input. The intertwiner preserves the original SU₃ marking exactly. Synchronization
with the linear actor and lifting the section coordinates to the full root
equations remain later source obligations.
Source: Fong--Seitz I (4D), (6A)(c); II (8.13)--(8.15), pp.203--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MonoidAlgebra
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
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
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
theorem marked_natural_equiv_all :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    Nonempty (Representation.Equiv ((elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)).comp π)
        (restrictScalars (k := ZMod 2) (MinimalDegree.natural J (RingHom.id E)))) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hi := (QuadrangleStructure.marked_unitary_profile_irreducible_all_of_cover Q split e h J hn hE hconj hJ
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
  exact SmallNatural.natural_equiv_of_finrank_le J hJ σ hn hE hconj hnσ hd

/-- Actual natural coordinates, with the full actor and the prescribed panel
marking both retained exactly, including at q = 2. -/
theorem marked_natural_coordinates_all :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ g, κ (π g) = g) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) =
        J.specialToProjective (κ r)) ∧
      ∀ r v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) r v) =
          Matrix.mulVec (κ r).val.val (c v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨ec⟩ := marked_natural_equiv_all Q split e h J hn hE hfixed hJ hconj hm i j hij
    hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hc (g : J.specialSubgroup) (v) :
      ec (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (π g) v) =
          Matrix.mulVec g.val.val (ec v) := LinearMap.congr_fun (ec.isIntertwining' g) v
  have hnat : IsNatural J ((elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)).comp π) :=
    ⟨MulEquiv.refl _,ec.toLinearEquiv,hc⟩
  have hinj : Function.Injective π := by
    intro a b hab
    apply hnat.injective J
    exact congrArg (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)) hab
  let k := MulEquiv.ofBijective π ⟨hinj,hπ⟩
  refine ⟨k.symm,ec.toLinearEquiv,?_,?_,?_⟩
  · intro g
    exact k.symm_apply_apply g
  · intro r
    have he := hπν (k.symm r)
    change ν (RootLocalCover.projection Q split j (k (k.symm r))) = _ at he
    simpa only [k.apply_symm_apply,Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap] using he
  · intro r v
    have he := hc (k.symm r) v
    change ec (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj) (k (k.symm r)) v) = _ at he
    simpa only [k.apply_symm_apply,Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap] using he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G E : Type*} [Group G] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
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
theorem original_natural_coordinates_all :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ g, κ (π g) = g) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) =
        J.specialToProjective (κ r)) ∧
      ∀ (g : generated L S) (hg : Q.q g ∈ rankOne Q split j) v,
        c (elementaryRepresentation (p := 2)
          (remainderFrattiniAction Q split j hVj) ⟨Q.q g,hg⟩ v) =
            Matrix.mulVec (κ ⟨Q.q g,hg⟩).val.val (c v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨κ,c,hcover,hpanel,hc⟩ := marked_natural_coordinates_all Q split (originalMarkedIso Q) h J
    hn hE hfixed hJ hconj hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  exact ⟨κ,c,hcover,hpanel,fun g hg v => hc ⟨Q.q g,hg⟩ v⟩

include hVj in
/-- Natural coordinates evaluated on literal original actor and core
representatives. Conjugation uses a*v*a⁻¹, matching the left column action;
the original cover and projective panel maps are retained. -/
theorem original_natural_representatives_all :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ g, κ (π g) = g) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      ∀ (a v : generated L S) (ha : Q.q a ∈ rankOne Q split j)
        (hv : Q.q v ∈ simpleRemainder Q split j),
        ∃ w : simpleRemainder Q split j,
          (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
          c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w)) =
            Matrix.mulVec (κ ⟨Q.q a,ha⟩).val.val
              (c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j))
                ⟨Q.q v,hv⟩))) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨κ,c,hcover,hpanel,hc⟩ := original_natural_coordinates_all Q split h J
    hn hE hfixed hJ hconj hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨κ,c,hcover,hpanel,?_⟩
  intro a v ha hv
  let w := remainderRankOneAction Q split j hVj ⟨Q.q a,ha⟩ ⟨Q.q v,hv⟩
  refine ⟨w,?_,?_⟩
  · rw [remainderRankOneAction_apply,map_mul,map_mul,map_inv]
  · have he := hc a ha (Additive.ofMul (QuotientGroup.mk'
      (frattini (simpleRemainder Q split j)) ⟨Q.q v,hv⟩))
    change c (Additive.ofMul (remainderFrattiniAction Q split j hVj ⟨Q.q a,ha⟩
      (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) ⟨Q.q v,hv⟩))) = _ at he
    rw [remainderFrattiniAction_mk] at he
    exact he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
