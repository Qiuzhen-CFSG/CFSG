module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SpecialRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedRadicals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.Frattini.OmegaProducts

/-!
# The original unitary-five special radical

Restrict the existing original S equivalence to each full parabolic
core. This is an isomorphism onto the literal complementary section;
its formula retains the original full-overlap map. Consequently the
specialness equations of DGS (11.8)(f), Phi(Q_beta)=Q_beta'=Z(Q_beta),
transport to that same radical. The quadrangle calculation identifies
all three embedded subgroups with the intrinsic center of U_beta^s_alpha.
The linear opposite root cannot commute with its crossed copy, and the
commutator lies in this center. The full root orders q^2 and q^3 give
radical orders q^8 and q^7 and full S order q^10.

The source specialization retains both endpoint orientations, q=2, and
an independent geometric marking. It does not assume an ambient descent
from the geometric completion. The earlier specialness and elementary
linear Sylow-quotient clauses remain explicit Chapter 11 inputs.
The center-commutator equality, the other full-root commutator, both
root-generated actor identifications and the irreducible actions remain
unproved parts of (6A)(c); no full U5 recognition is asserted here.

Source: DGS (11.5), (11.8), pp.172--176;
Fong--Seitz I (3G), (6A)(c), pp.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- Restrict the actual original S marking to the full original endpoint core. -/
def markedCoreEquiv (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    (parabolic L S i).pCoreIn 2 ≃* simpleRemainder Q split i := by
  let A := ((parabolic L S i).pCoreIn 2).subgroupOf S
  have hi : Function.Injective (MarkedLocal.sylowMap Q e h) := by
    intro a b he
    apply (markedSylowEquiv Q e h split).injective
    apply Subtype.ext
    simpa only [markedSylowEquiv_apply] using he
  exact (subgroupOfEquivOfLe (h.parabolic_core_le_S i)).symm.trans
    ((A.equivMapOfInjective (MarkedLocal.sylowMap Q e h) hi).trans
      (MulEquiv.subgroupCongr ((marked_sylow_core_map Q e h i).trans
        (marked_remainder_eq_core Q e h split i hV).symm)))

@[simp] theorem markedCoreEquiv_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (c : (parabolic L S i).pCoreIn 2) :
    (markedCoreEquiv Q e h split i hV c : X ⧸ Q.D) =
      MarkedLocal.sylowMap Q e h ⟨c,h.parabolic_core_le_S i c.property⟩ := by rfl

include e h in
/-- DGS (11.8)(f) locates the literal beta-core center and Frattini layer,
and forces a nonzero center-side commutator in the same quotient. -/
theorem marked_unitary_special_radical
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≠ ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≤
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  let a := markedCoreEquiv Q e h split j hVj
  have hd : _root_.commutator (simpleRemainder Q split j) =
      center (simpleRemainder Q split j) := by
    have he := congrArg (Subgroup.map a.toMonoidHom) hderived
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective,←_root_.commutator_def,
      center_map_equiv] at he
    exact he
  have hf : frattini (simpleRemainder Q split j) = center (simpleRemainder Q split j) := by
    have he := congrArg (Subgroup.map a.toMonoidHom) hfrattini
    rw [frattini_map_equiv,center_map_equiv] at he
    exact he
  have hd' : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
    rw [←hd,map_subtype_commutator]
  let := marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi
  have hab : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr inferInstance
  have hcenter := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_center_eq_cross_center
    Q split hm i j hij hVi hVj hab hd'.ge
  exact ⟨hd'.trans hcenter,(congrArg (Subgroup.map (simpleRemainder Q split j).subtype) hf).trans hcenter,
    hcenter,
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.cross_root_commutator_ne_bot_of_special_radical
      Q split hm i j hij hVi hVj hab hd'.ge,
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.cross_root_commutator_le_center
      Q split hm i j hij hVi hVj⟩

include e h in
/-- The two honest panel indices give q² and q³ roots, q⁸ and q⁷ radicals,
and order q¹⁰ for the full original S. -/
theorem marked_unitary_root_orders
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (q : ℕ) (hq : 0 < q)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = q^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = q^3 + 1) :
    Nat.card (simpleRoot Q split i) = q^2 ∧ Nat.card (simpleRoot Q split j) = q^3 ∧
      Nat.card (simpleRemainder Q split i) = q^8 ∧
      Nat.card (simpleRemainder Q split j) = q^7 ∧ Nat.card S = q^10 := by
  have hri : Nat.card (simpleRoot Q split i) = q^2 := by
    have hh := marked_commonBorel_root_index Q e h split i; omega
  have hrj : Nat.card (simpleRoot Q split j) = q^3 := by
    have hh := marked_commonBorel_root_index Q e h split j; omega
  have hprod : Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1) = q^5 := by
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rw [hri,hrj]; ring
    · rw [hrj,hri]; ring
    · exact (hij rfl).elim
  have hU : Nat.card split.U = q^10 := by
    rw [unipotent_card_even Q split 2 hm,hprod]; ring
  have hRi : Nat.card (simpleRemainder Q split i) = q^8 := by
    have hc := unipotent_card_simple Q split i
    rw [hU,hri] at hc
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 2)
    exact hc.symm.trans (by ring)
  have hRj : Nat.card (simpleRemainder Q split j) = q^7 := by
    have hc := unipotent_card_simple Q split j
    rw [hU,hrj] at hc
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 3)
    exact hc.symm.trans (by ring)
  exact ⟨hri,hrj,hRi,hRj,(Nat.card_congr (markedSylowEquiv Q e h split).toEquiv).trans hU⟩

include h in
omit Q e split in
/-- The special-radical conclusions on the original SourceQuotient; the
universal-to-ambient descent is never assumed. -/
theorem original_unitary_special_radical
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    (frattini (simpleRemainder Q₀ split₀ j)).map (simpleRemainder Q₀ split₀ j).subtype =
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map (rootAt Q₀ split₀ j (Q₀.simple i)).subtype ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ ≠ ⊥ ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ ≤
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map (rootAt Q₀ split₀ j (Q₀.simple i)).subtype := by
  obtain ⟨_,hphi,_,hne,hbound⟩ := marked_unitary_special_radical Q₀ (originalMarkedIso Q₀) h split₀
    hm i j hij hVi hVj hQi hderived hfrattini
  exact ⟨hphi,hne,hbound⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
