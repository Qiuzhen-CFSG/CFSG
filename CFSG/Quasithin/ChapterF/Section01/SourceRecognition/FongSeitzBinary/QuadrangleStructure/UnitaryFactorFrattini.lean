module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.SmallUnitaryIrreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactor
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.SmallUnitaryIrreducibility

/-!
# The unitary quadrangle core is special from the original factor orders

The original SU3-or-PSU3 quotient gives its actual root of order q^3 and
surjective SU3 cover, with the literal projective square. The opposite
panel index q^2+1 gives radical order q^7. Its crossed-root center forces
the Frattini and derived subgroups to have order q. The resulting
six-n-dimensional action is irreducible, including q = 2. Its center
therefore lies in the Frattini subgroup; the converse is the quadrangle
root-commutation calculation. This derives both original specialness
equations through the same marked original core isomorphism.

The last theorem feeds these derived equations to the complete all-fields
(6A)(c) structural consumer. It retains both mixed commutators, the full
SU3 actor, the scalar kernel, the actual linear representative equations
and all irreducible section actions. The Chapter 12 application uses the
original linear quotient to compute the opposite panel index directly.

The `import all` is an intentional internal proof extension of the same
SmallUnitaryIrreducibility family. It reuses its private six-dimensional
binary argument without changing that module or exporting its private
names. The other imports and all public statements retain normal module
boundaries.

Earlier source producers still supply F.1.1, the full marked split
quotient, rotation four, the panel parameters and both kernel containments.
No exhaustive row selection or U5 coordinate-equation assertion is made.
Those equations remain with the independent U5 source owner.
Source: Fong--Seitz I (4D), (6A)(c), pp.21--23,37--38;
DGS (11.8)(a,c,d,f), pp.175--176; AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem faithful_frattini_representation
    (j : Fin 2) (s : RootReflection Q split j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j})) :
    Function.Injective (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)) := by
  intro a b hab
  apply remainderFrattiniAction_injective Q split j s hVj hc
  ext v
  exact Additive.ofMul.injective
    (congrArg (fun f : Module.End (ZMod 2)
      (Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))) =>
        f (Additive.ofMul v)) hab)

/-- The full special actor and irreducible section are forced by the cover
and the radical order, including fixed-field order two. -/
theorem unitary_profile_of_radical_order
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hcard : Nat.card (simpleRemainder Q split j) = (2^n)^7) :
    Function.Injective π ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible ∧
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  obtain ⟨hphi,hd⟩ := unitary_frattini_eq_cross_center_of_cover Q split J hn hE hconj hJ
    hm i j hij hVj s hc ν π hπ hπν hcard
  by_cases hn2 : 2 ≤ n
  · exact ⟨unitary_cover_injective Q split J hn2 hE hconj hJ
      hm i j hij hVj s ν π hπ hphi hcard,
      unitary_frattini_irreducible_of_cover Q split J hn2 hE hconj hJ
        hm i j hij hVj s ν π hπ hphi hcard,hphi,hd⟩
  · have hn1 : n = 1 := by omega
    subst n
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 hn hE hconj
    have hW := (unitary_frattini_section_card Q split J hn hE hfixed hJ i j hVj ν hphi hcard).2
    let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
    let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
    have hρ := faithful_frattini_representation Q split j s hVj hc
    have hk : (ρ.comp π).ker ≤ J.specialToProjective.ker := by
      intro a ha
      have he : π a = 1 := hρ (ha.trans ρ.map_one.symm)
      rw [MonoidHom.mem_ker,←hπν,he,map_one,map_one]
    have hdim : Module.finrank (ZMod 2) (Additive V) = 6 := by
      have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
      rw [Nat.card_zmod] at he
      apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      change 2 ^ Module.finrank (ZMod 2) (Additive V) = 2^6
      rw [←he]
      exact hW
    have hσ := small_unitary_faithful_of_scalar_kernel J (by simpa using hE)
      (by simpa using hconj) hJ (ρ.comp π) hk (by change Module.finrank (ZMod 2) (Additive V) < 8; omega)
    have hπi : Function.Injective π := fun _ _ he => hσ (congrArg ρ he)
    let κ := MulEquiv.ofBijective π ⟨hπi,hπ⟩
    have hpc : pCore 2 J.specialSubgroup = ⊥ := by
      apply map_injective (f := κ.toMonoidHom) κ.injective
      rw [pCore_map_iso,Subgroup.map_bot,rankOne_twoCore_eq_bot Q split j s hVj]
    have hpc' : pCore 2 (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
      rw [←J.specialToProjective.map_pCore_of_central_kernel
        J.specialToProjective_surjective J.specialToProjective_ker_le_center,hpc,Subgroup.map_bot]
    exact ⟨hπi,(irreducible_comp_surjective_iff π hπ ρ).mp
      (small_unitary_faithful_six_irreducible J (by simpa using hE)
        (by simpa using hconj) hJ hpc' (ρ.comp π) hσ hdim),hphi,hd⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h in
/-- The actual factor cover and source panel orders force specialness of the
original unitary core, and give the full SU3 actor and irreducible section. -/
theorem marked_unitary_core_special_of_factor
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    _root_.commutator ((parabolic L S j).pCoreIn 2) = center ((parabolic L S j).pCoreIn 2) ∧
      frattini ((parabolic L S j).pCoreIn 2) = center ((parabolic L S j).pCoreIn 2) ∧
      ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        Nonempty (UnitaryActorProfile Q split j J hVj ν) ∧
        (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  have hrj : Nat.card (simpleRoot Q split j) = (2^n)^3 := by
    rcases hfactor with hs | hp
    · obtain ⟨a⟩ := hs
      exact MarkedLocal.specialUnitary_simpleRoot_card Q mark h split j T hT J hn hE hconj a
    · obtain ⟨a⟩ := hp
      exact MarkedLocal.projectiveUnitary_simpleRoot_card Q mark h split j T hT J hn hE hconj a
  have hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1 := by
    have he := marked_commonBorel_root_index Q mark h split j
    omega
  have hcard := (marked_unitary_root_orders Q mark h split hm i j hij (2^n)
    (pow_pos (by decide) n) hindexi hindexj).2.2.2.1
  obtain ⟨ν,π,hπ,hπν⟩ := MarkedLocal.regular_unitary_cover_of_factor Q mark h split
    J hn hE hconj j hVj hfactor
  let s := Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.actorReflection Q split j
  obtain ⟨hinj,hirr,hphi,hderived⟩ := unitary_profile_of_radical_order Q split J hn hE hconj hJ
    hm i j hij hVj s (MarkedLocal.parabolic_core_selfCentralizing Q mark h j) ν π hπ hπν hcard
  let V := simpleRemainder Q split j
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  have hne : _root_.commutator V ≠ ⊥ := by
    intro he
    have hz := hderived.symm.trans (by rw [←map_subtype_commutator,he,Subgroup.map_bot])
    have hc := congrArg (fun A : Subgroup (X ⧸ Q.D) => Nat.card A) hz
    rw [card_map_of_injective (rootAt Q split j (Q.simple i)).subtype_injective,
      unitary_cross_center_card Q split J hn hE hfixed hJ j (Q.simple i) hVj ν,card_bot] at hc
    have hq := Nat.one_lt_two_pow hn.ne'
    omega
  have hZΦ := remainder_center_le_frattini_of_irreducible Q split j hVj hirr hne
  have hΦZ : frattini V ≤ center V := by
    apply (map_le_map_iff_of_injective V.subtype_injective).mp
    exact hphi.le.trans (cross_center_le_remainder_center Q split hm i j hij hVi hVj)
  have hΦeq : frattini V = center V := le_antisymm hΦZ hZΦ
  have hDeq : _root_.commutator V = center V := by
    apply map_injective (f := V.subtype) V.subtype_injective
    rw [map_subtype_commutator,hderived,←hΦeq]
    exact hphi.symm
  let a := markedCoreEquiv Q mark h split j hVj
  have hDoriginal : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2) := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective,
      ←_root_.commutator_def,center_map_equiv]
    exact hDeq
  have hΦoriginal : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2) := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [frattini_map_equiv,center_map_equiv]
    exact hΦeq
  let κ := MulEquiv.ofBijective π ⟨hinj,hπ⟩
  refine ⟨hDoriginal,hΦoriginal,ν,⟨⟨κ.symm.toMonoidHom,κ.symm.surjective,κ.symm.injective,?_⟩⟩,hirr⟩
  intro r
  have he := hπν (κ.symm r)
  change ν (RootLocalCover.projection Q split j (κ (κ.symm r))) = _ at he
  rw [κ.apply_symm_apply] at he
  simpa only [rankOneLocalEquiv_eq_projection,MulEquiv.coe_toMonoidHom] using he
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
include e h

/-- The complete all-fields (6A)(c) output now follows without either
original core specialness equation. The full actor, both mixed commutators,
all section actions and the literal projective square are retained. -/
theorem marked_unitary_sixA_all_of_factor_orders
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (t : RootReflection Q split j)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S)) :
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
    (∃ κ : rankOne Q split j ≃* J.specialSubgroup,
      (∀ r : rankOne Q split j,
        ν (rankOneLocalEquiv Q split j hVj (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup ∧
      center (rankOne Q split j) =
        (center J.specialSubgroup).comap κ.toMonoidHom) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ =
        rootAt Q split i (Q.simple j) ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (rootAt Q split j (Q.simple i))).map
          (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (frattini (simpleRemainder Q split j)).map
          (simpleRemainder Q split j).subtype) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q split i) =
        _root_.commutator (simpleRemainder Q split i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
            Subgroup (X ⧸ Q.D)),
        letI := he
        Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
          Subgroup (X ⧸ Q.D)) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2)
          (remainderDerivedAction Q split i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q split i) ⧸
        frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split i hVi)).IsIrreducible ∧
      Representation.IsIrreducible
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation
          Q split i hVi)) ∧
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  obtain ⟨hderived,hfrattini,_⟩ := marked_unitary_core_special_of_factor Q e h split J hn hE hconj hJ
    hm i j hij hVi hVj hindexi hfactor
  exact marked_unitary_sixA_all_of_factor Q split e h J hn hK hE hfixed hJ hconj
    hm i j hij hVi hVj s t f hf hk hfactor hindexi hindexj hQi hderived hfrattini

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
