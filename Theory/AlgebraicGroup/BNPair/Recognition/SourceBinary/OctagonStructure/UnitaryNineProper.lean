module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineIndex
public import Theory.ElementaryAbelian.LargeSection
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed

/-!
# Proper invariant subgroups of the unitary nine-b subgroup

The five literal generating factors force every proper full-Cartan-invariant
subgroup of X to have index at least 2^b. Indeed, a missing linear factor
has trivial intersection, and a missing unitary factor has intersection
1 or its Frattini subgroup. The previously proved trichotomy also controls
the two end Frattini factors. No normality of the candidate in X is needed.

Thus a proper candidate has order at most 2^(8b). If it contains an
elementary section of order at least 2^(8b), that section exhausts the
candidate, which must itself be elementary. The actual middle-root bound
2^(7b) then excludes it. The conclusions include b=1 and both orientations.

Source: Fong--Seitz I (6F), printed p.47, the proper invariant-subgroup
paragraph. The sharp projective degree bound has a separate producer; the
whole-X case and lower-central persistence remain subsequent steps.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

private theorem small_index_contains_of_trichotomy {Y : Type*} [Group Y] [Finite Y]
    (K V C M : Subgroup Y) {b : ℕ} (hCK : C ≤ K)
    (hC : Nat.card C=2^(3*b)) (hM : Nat.card M=2^b)
    (ht : C ⊓ V=⊥ ∨ C ⊓ V=M ∨ C ⊓ V=C)
    (hsmall : V.relIndex K < 2^b) : C ≤ V := by
  have hi : V.relIndex C < 2^b :=
    (relIndex_le_of_le_right hCK (Nat.ne_of_gt Nat.card_pos)).trans_lt hsmall
  have hc := relIndex_mul_relIndex (⊥ : Subgroup Y) (C ⊓ V) C bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_comm C V,inf_relIndex_right,hC,inf_comm V C] at hc
  rcases ht with he | he | he
  · rw [he,Nat.card_unique,one_mul] at hc
    have hle : 2^b ≤ 2^(3*b) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rw [he,hM] at hc
    have hp : 2^(3*b)=2^b*2^(2*b) := by rw [←pow_add]; congr 1; omega
    rw [hp] at hc
    have heq : V.relIndex C=2^(2*b) := Nat.eq_of_mul_eq_mul_left (by positivity) hc
    rw [heq] at hi
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : b ≤ 2*b)) hi).elim
  · exact he ▸ (show C ⊓ V ≤ V from inf_le_right)

private theorem small_index_contains_of_dichotomy {Y : Type*} [Group Y] [Finite Y]
    (K V A : Subgroup Y) {b : ℕ} (hAK : A ≤ K)
    (hA : 2^b ≤ Nat.card A) (ht : A ⊓ V=⊥ ∨ A ≤ V)
    (hsmall : V.relIndex K < 2^b) : A ≤ V := by
  rcases ht with he | he
  · have hi := (relIndex_le_of_le_right (H:=V) hAK (Nat.ne_of_gt Nat.card_pos)).trans_lt hsmall
    rw [←inf_relIndex_right,inf_comm V A,he,relIndex_bot_left] at hi
    exact (not_lt_of_ge hA hi).elim
  · exact he

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Every proper Cartan-invariant subgroup misses at least 2^b cosets. -/
theorem unitaryNineSubgroup_proper_index
    {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 0 < b)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    (i j : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split i ≃* PSL(2,E))
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nat.card (simpleRoot Q split i)=2^(2*b))
    (hj : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ rootFrattiniAt Q split j w)
    (V : Subgroup (X ⧸ Q.D)) (hV : V < unitaryNineSubgroup Q split i j)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (V : Set (X ⧸ Q.D))) :
    2^b ≤ V.relIndex (unitaryNineSubgroup Q split i j) := by
  by_contra hn
  have hsmall := Nat.lt_of_not_ge hn
  let K := unitaryNineSubgroup Q split i j
  have htri (w : Weyl Q) (W : Subgroup (X ⧸ Q.D))
      (hW : W ≤ rootAt Q split j w)
      (hHW : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :=
    unitary_rootAt_cartan_subgroup_trichotomy Q split J hb hcard hconj j hKj μ hj w
      (hfix w) W hW hHW
  have hphi (w : Weyl Q) (hAK : rootFrattiniAt Q split j w ≤ K) :
      rootFrattiniAt Q split j w ≤ V := by
    let A := rootFrattiniAt Q split j w
    have hHA : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D)) :=
      (rootAt_torus_normalizes Q split j w).trans
        (normalizer_le_normalizer_characteristic_image _ (frattini _))
    apply small_index_contains_of_dichotomy K V A hAK
      (unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ w).ge ?_ hsmall
    rcases htri w (A ⊓ V) (inf_le_left.trans (map_subtype_le _))
      ((le_inf hHA hH).trans inf_normalizer_le_normalizer_inf) with he | he | he
    · exact Or.inl he
    · exact Or.inr (he.ge.trans inf_le_right)
    · exact Or.inr ((map_subtype_le _).trans (he ▸ (show A ⊓ V ≤ V from inf_le_right)))
  have hlin (w : Weyl Q) (hAK : rootAt Q split i w ≤ K) : rootAt Q split i w ≤ V := by
    let A := rootAt Q split i w
    have hA : Nat.card A=2^(2*b) := by dsimp only [A]; rw [rootAt,card_rightConjugate,hi]
    apply small_index_contains_of_dichotomy K V A hAK
      ((Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : b ≤ 2*b)).trans_eq hA.symm) ?_ hsmall
    by_cases he : A ⊓ V=⊥
    · exact Or.inl he
    · have heq := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i ν hKi w
        (A ⊓ V) inf_le_left he
        ((le_inf (rootAt_torus_normalizes Q split i w) hH).trans inf_normalizer_le_normalizer_inf)
      exact Or.inr (heq.ge.trans inf_le_right)
  have hmid : rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤ V := by
    let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    apply small_index_contains_of_trichotomy K V C
      (rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i))
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right)) ?_
      (unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ _)
      (htri _ (C ⊓ V) inf_le_left
        ((le_inf (rootAt_torus_normalizes Q split j _) hH).trans inf_normalizer_le_normalizer_inf)) hsmall
    dsimp only [C]
    rw [rootAt,card_rightConjugate,hj,←pow_mul,Nat.mul_comm b 3]
  exact hV.not_ge (sup_le (sup_le (sup_le (sup_le
    (hphi _ (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))))
    (hlin _ (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))) hmid)
    (hlin _ (le_sup_of_le_left le_sup_right))) (hphi _ le_sup_right))

/-- The index gap gives the precise upper bound used for a proper source candidate. -/
theorem unitaryNineSubgroup_proper_card_le (i j : Fin 2) {b : ℕ}
    (hK : Nat.card (unitaryNineSubgroup Q split i j)=2^(9*b))
    (V : Subgroup (X ⧸ Q.D)) (hV : V ≤ unitaryNineSubgroup Q split i j)
    (hindex : 2^b ≤ V.relIndex (unitaryNineSubgroup Q split i j)) :
    Nat.card V ≤ 2^(8*b) := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) V
    (unitaryNineSubgroup Q split i j) bot_le hV
  rw [relIndex_bot_left,relIndex_bot_left,hK] at hc
  apply Nat.le_of_mul_le_mul_right (c:=2^b) ?_ (by positivity)
  calc
    Nat.card V*2^b ≤ Nat.card V*V.relIndex (unitaryNineSubgroup Q split i j) :=
      Nat.mul_le_mul_left _ hindex
    _ = 2^(9*b) := hc
    _ = 2^(8*b)*2^b := by rw [←pow_add]; congr 1; omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
