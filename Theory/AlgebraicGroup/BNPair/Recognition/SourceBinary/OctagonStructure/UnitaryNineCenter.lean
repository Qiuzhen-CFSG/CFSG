module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineSubgroup
public import Theory.GroupTheory.Commutator.CoprimeAbelianFixed
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed

/-!
# The middle-root center obstruction for the unitary subgroup X

The source subgroup X of order 2^(9b) contains the whole cubic fixed
radical Y and is normalized by the Cartan three-core T. Thus C_X(T)=Y.
If X' lies in the middle Frattini root M, T fixes X'. The already abelian
Y is then central in X by coprime decomposition and the three-subgroups
lemma. Its outer Frattini root is nontrivial and disjoint from M, so the
actual embedded center of X strictly contains M. In particular X cannot
have both its derived subgroup and its center equal to M.

The import-all edge reuses the definition of the actual Cartan three-core
without changing that earlier module's public boundary. The matching CFSG
module supplies all fixed-root, abelianness and nontriviality inputs from
the original factors, including degree one and both scalar conventions.

Source: Fong--Seitz I (6F), printed p.47, the contradiction after
Z(X)=Phi(X)=Phi(U_2^(s_1 s_2 s_1)). The invariant-subgroup reduction to
that equality and the sharp projective degree bound remain required.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- X has exactly the same cubic fixed subgroup as the full unitary radical. -/
theorem unitaryNineSubgroup_threeCore_fixed (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hY : simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      unitaryNineSubgroup Q split i j) :
    unitaryNineSubgroup Q split i j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
      simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by
  exact le_antisymm (inf_le_inf_right _ ((unitaryNineSubgroup_le_middleFive Q split i j).trans
    (middleFive_le_remainder Q split hm j i hij.symm))) (le_inf hY inf_le_right)

/-- If the cubic actor fixes X's derived subgroup, its entire fixed subgroup is central in X. -/
theorem unitaryNineSubgroup_fixed_central (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hY : simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      unitaryNineSubgroup Q split i j)
    (ha : IsMulCommutative ↥(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))))
    (hd : ⁅unitaryNineSubgroup Q split i j,unitaryNineSubgroup Q split i j⁆ ≤
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) :
    simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      centralizer (unitaryNineSubgroup Q split i j : Set (X ⧸ Q.D)) := by
  let K := unitaryNineSubgroup Q split i j
  let T := cartanThreeCore Q
  have hK : IsPGroup 2 K := split.isTwo.to_le
    (((unitaryNineSubgroup_le_middleFive Q split i j).trans
      (middleFive_le_remainder Q split hm j i hij.symm)).trans inf_le_left)
  have hT : IsPGroup 3 T := pCore_isPGroup.map _
  have hc : Nat.Coprime (Nat.card T) (Nat.card K) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) T K hT hK
  have he := unitaryNineSubgroup_threeCore_fixed Q split hm i j hij hY
  rw [←he] at ha ⊢
  exact fixed_le_centralizer_of_derived_fixed_of_abelian K T ((cartanThreeCore_le Q).trans
    (unitaryNineSubgroup_cartan_normalizes Q split i j))
      (@IsNilpotent.to_isSolvable K _ hK.isNilpotent) hc hd ha

private theorem outer_middle_disjoint (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (rootAt Q split j (Q.simple i))
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)) := by
  apply rootAt_disjoint
  have hs (k : Fin 2) : (Q.simple k)⁻¹=Q.simple k := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hsquare (k : Fin 2) : Q.simple k*Q.simple k=1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  simp only [mul_inv_rev,hs,mul_assoc,hsquare,inv_one,one_mul]
  simp only [←mul_assoc (Q.simple j) (Q.simple j),hsquare,one_mul]
  have hlen (b : Bool) : Q.tits.wordLength (alternatingWord Q b 2)=
      Q.tits.wordLength (alternatingWord Q b 1)+1 := by
    rw [wordLength_alternatingWord Q b (by omega),wordLength_alternatingWord Q b (by omega)]
  rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;>
    rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,mul_one,Bool.not_false] using hlen false
  · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,mul_one,Bool.not_true] using hlen true
  · exact (hij rfl).elim

private theorem frattini_card_independent (j : Fin 2) (v w : Weyl Q) :
    Nat.card (rootFrattiniAt Q split j v)=Nat.card (rootFrattiniAt Q split j w) := by
  have he := (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j)
    (representative v : X ⧸ Q.D)).trans
      (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j)
        (representative w : X ⧸ Q.D)).symm
  change rootAt Q split j v ≃* rootAt Q split j w at he
  simp only [rootFrattiniAt,card_map_of_injective (rootAt Q split j v).subtype_injective,
    card_map_of_injective (rootAt Q split j w).subtype_injective]
  rw [←frattini_map_equiv he,card_map_of_injective he.injective]

private theorem embedded_center (K : Subgroup (X ⧸ Q.D)) :
    (center K).map K.subtype=K ⊓ centralizer (K : Set (X ⧸ Q.D)) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,fun y hy => congrArg Subtype.val ((mem_center_iff.mp hx) ⟨y,hy⟩)⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)),rfl⟩

/-- If the derived subgroup is contained in the middle Frattini root,
the actual center strictly contains that root. -/
theorem unitaryNineSubgroup_center_gt_middle_of_derived_le (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hY : simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      unitaryNineSubgroup Q split i j)
    (ha : IsMulCommutative ↥(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))))
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))=rootFrattiniAt Q split j w)
    (hc : 1 < Nat.card (rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)))
    (hd : ⁅unitaryNineSubgroup Q split i j,unitaryNineSubgroup Q split i j⁆ ≤
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)) :
    rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) <
      (center (unitaryNineSubgroup Q split i j)).map (unitaryNineSubgroup Q split i j).subtype := by
  rw [embedded_center]
  let K := unitaryNineSubgroup Q split i j
  let Y := simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
  let A := rootFrattiniAt Q split j (Q.simple i)
  let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  have hfixed (w) : rootFrattiniAt Q split j w ≤
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by rw [←hfix]; exact inf_le_right
  have hYC : Y ≤ centralizer (K : Set (X ⧸ Q.D)) :=
    unitaryNineSubgroup_fixed_central Q split hm i j hij hY ha (hd.trans (hfixed _))
  have hAK : A ≤ K := le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hMK : M ≤ K := (map_subtype_le _).trans
    (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have he := unitaryNineSubgroup_threeCore_fixed Q split hm i j hij hY
  have hAY : A ≤ Y := (le_inf hAK (hfixed _)).trans he.le
  have hMY : M ≤ Y := (le_inf hMK (hfixed _)).trans he.le
  apply lt_of_le_not_ge (le_inf hMK (hMY.trans hYC))
  intro hle
  have hAM : A ≤ M := (le_inf hAK (hAY.trans hYC)).trans hle
  have hdis : Disjoint A M := (outer_middle_disjoint Q split hm i j hij).mono
    (map_subtype_le _) (map_subtype_le _)
  have hbot : A=⊥ := disjoint_self.mp (hdis.mono_right hAM)
  have hcardA : Nat.card A=Nat.card M := frattini_card_independent Q split j _ _
  have hcontra : 1 < Nat.card A := hcardA ▸ hc
  rw [hbot,Nat.card_unique] at hcontra
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
