module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalAllFields
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.NaturalRootKernel

/-!
# Original U₅ natural root coordinates and the full B–D equation

Construct the full SU₃ actor and natural section from the original profile
and generic cover. A common inner change of actor and basis pins its entire
Hermitian root to the actual source root. The original covering map and
projective panel square record that change element by element.

The crossed linear root receives faithful coordinates in this same field.
The whole crossed unitary root has a surjective noncentral coordinate whose
kernel is exactly its intrinsic center. The source commutator containment
lifts the natural polynomial to an exact B–D product equation. The original
consumer retains literal Q.q representatives and either orientation, with
all positive binary degrees, including q = 2 and q = 4.

These coordinates still need synchronization with the SL₂-derived labels
and both complete Hermitian parameter groups before the remaining mixed,
Cartan and Weyl equations give FiveData.
Source: Fong--Seitz II (8.14)--(8.16), printed pp.203--204.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MonoidAlgebra
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
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

/-- Pin the entire root inside the constructed SU₃ actor, changing the natural
basis by exactly the same inner conjugator and keeping the original cover. -/
theorem marked_natural_root_pinning :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) =
        J.specialToProjective (g*a*g⁻¹)) ∧
      ((rankOne Q split j).subtype.comp
        (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j ∧
      ∀ a v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) =
          Matrix.mulVec a.val.val (c v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨κ,c,hcover,hpanel,hc⟩ := marked_natural_coordinates_all Q split e h J hn hE
    hfixed hJ hconj hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  obtain ⟨g,θ,hroot,hθ⟩ := exists_unitary_root_pinning J hn hE hfixed hJ Q split j hVj ν κ
  obtain ⟨d,hd,_⟩ := natural_coordinates_conjugate J hJ Q split j κ
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)) c hc g θ hθ
  refine ⟨g,θ,d,?_,?_,hroot,hd⟩
  · intro a
    apply κ.injective
    rw [hθ,hcover]
  · intro a
    rw [hpanel,hθ]

/-- The B–D crossing is an exact equality on the actual quotient. All root
pinning, natural coordinates and the faithful crossed-linear chart are
constructed from the original profile and generic cover. -/
theorem marked_natural_crossing :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E))
      (χ : rootAt Q split i (Q.simple j) ≃* Multiplicative E),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) =
        J.specialToProjective (g*a*g⁻¹)) ∧
      ((rankOne Q split j).subtype.comp
        (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j ∧
      (∀ a v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v)) ∧
      (∀ x, χ x = naturalCrossCoordinate Q split i j hij c x) ∧
      Function.Surjective (naturalUnitaryCoordinate Q split hm i j hij c) ∧
      (naturalUnitaryCoordinate Q split hm i j hij c).ker = center (rootAt Q split j (Q.simple i)) ∧
      ∀ (p : hermitianUnipotentCoord J) (v : simpleRemainder Q split j),
        (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) →
        (θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D) * v =
          v * (χ.symm (.ofAdd (p.val.1 * (naturalSectionMap Q split j c v).toAdd 1)) : X ⧸ Q.D) *
            (θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨g,θ,c,hcover,hpanel,hroot,hc⟩ := marked_natural_root_pinning Q split e h J hn hE
    hfixed hJ hconj hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hcenter := (QuadrangleStructure.marked_unitary_special_radical Q e h split hm i j hij
    hVi hVj hQi hderived hfrattini).2.1
  have hphi := hcenter.le.trans (map_subtype_le _)
  have horders := QuadrangleStructure.marked_unitary_root_orders Q e h split hm i j hij (2^n)
    (pow_pos (by decide) n) hindexi hindexj
  have hcard : Nat.card (simpleRoot Q split i) = Nat.card E :=
    horders.1.trans hE.symm
  let χ := naturalCrossEquiv Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hphi hcard
  have hD : Nat.card (rootAt Q split j (Q.simple i)) = (2^n)^3 := by
    simpa only [rootAt,card_rightConjugate] using horders.2.1
  have hZ := unitary_cross_center_card Q split J hn hE hfixed hJ j (Q.simple i) hVj ν
  exact ⟨g,θ,c,χ,hcover,hpanel,hroot,hc,fun _ => rfl,
    naturalUnitaryCoordinate_surjective Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hcard hcenter hD hZ,
    naturalUnitaryCoordinate_ker Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hcard hcenter,
    natural_unitary_crossing Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hphi hcard⟩

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

/-- The lifted B–D equation uses literal original representatives under Q.q.
The same full SU₃ cover and projective endpoint marking are retained. -/
theorem original_natural_crossing :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E))
      (χ : rootAt Q split i (Q.simple j) ≃* Multiplicative E),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) =
        J.specialToProjective (g*a*g⁻¹)) ∧
      ((rankOne Q split j).subtype.comp
        (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j ∧
      (∀ a v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v)) ∧
      (∀ x, χ x = naturalCrossCoordinate Q split i j hij c x) ∧
      Function.Surjective (naturalUnitaryCoordinate Q split hm i j hij c) ∧
      (naturalUnitaryCoordinate Q split hm i j hij c).ker = center (rootAt Q split j (Q.simple i)) ∧
      ∀ (p : hermitianUnipotentCoord J) (b d : generated L S)
        (_hb : Q.q b = (θ (hermitianUnipotentSU J hJ p) : (generated L S) ⧸ Q.D))
        (hd : Q.q d ∈ simpleRemainder Q split j)
        (_hD : Q.q d ∈ rootAt Q split j (Q.simple i)),
        Q.q (b*d) = Q.q d *
          (χ.symm (.ofAdd (p.val.1 * (naturalSectionMap Q split j c ⟨Q.q d,hd⟩).toAdd 1)) :
            (generated L S) ⧸ Q.D) * Q.q b := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨g,θ,c,χ,hcover,hpanel,hroot,hc,hχ,hδ,hker,hcross⟩ := marked_natural_crossing Q split
    (originalMarkedIso Q) h J hn hE hfixed hJ hconj hm i j hij hVi hVj s ν π hπ hπν
      hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,c,χ,hcover,hpanel,hroot,hc,hχ,hδ,hker,?_⟩
  intro p b d hb hd hD
  rw [map_mul,hb]
  exact hcross p ⟨Q.q d,hd⟩ hD

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
