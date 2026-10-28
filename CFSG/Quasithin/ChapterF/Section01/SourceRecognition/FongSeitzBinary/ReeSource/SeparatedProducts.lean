module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SeparatedProducts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Opposition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.MixedBounds

/-!
# Coordinate separation on the actual Ree radical quotient

The natural panel markings make every root Frattini quotient an irreducible
binary module for the full Cartan. In positive parameter, each root-action
kernel has order q-1>1; the proved independent-root kernel intersections
therefore distinguish the constituents. The ordered-product separation
lemma now applies with all representation premises discharged.

Source: Fong--Seitz I (1973), (6H), pp.51--53. The odd linear degree and
faithful Borel remain earlier source inputs. PositiveNearEquality consumes
the product theorem in the actual four-root commutator interval.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include ν hC μ hB hn in
/-- Every marked source root quotient is an irreducible binary Cartan module,
including the one-dimensional quotients at q=2. -/
theorem source_root_frattini_irreducible (k : Fin 2) (w : Weyl Q) :
    (rootAtCartanFrattiniRepresentation Q split k w).IsIrreducible := by
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl
  · apply root_frattini_irreducible_of_card Q split 0 w n hn.pos
      (linear_rootAction_cyclic Q split 0 n ν T hC hn.pos (UnitarySource.actorReflection Q split 0) w)
    · rw [Nat.card_congr (rootActionImageEquiv Q split 0 w).toEquiv]
      exact linear_cartanImage_card Q split 0 n hn.pos ν T hC (UnitarySource.actorReflection Q split 0)
    · let := linear_rootAt_elementary Q split 0 n ν T hC w
      rw [frattini_eq_bot_of_isElementaryAbelian (p := 2),Nat.card_congr QuotientGroup.quotientBot.toEquiv]
      exact linear_rootAt_card Q split 0 n ν T hC hn.pos w
  · apply root_frattini_irreducible_of_card Q split 1 w (2*m+1) (by omega)
      ((rootActionImageEquiv Q split 1 w).isCyclic.mpr
        (suzuki_cartanImage_cyclic Q split 1 m μ hB (UnitarySource.actorReflection Q split 1)))
    · rw [Nat.card_congr (rootActionImageEquiv Q split 1 w).toEquiv]
      exact suzuki_cartanImage_card Q split 1 m μ hB (UnitarySource.actorReflection Q split 1)
    · rw [Nat.card_congr (rootAtFrattiniEquiv Q split 1 w).toEquiv,
        Nat.card_congr (suzukiFrattiniQuotientEquiv Q split 1 m μ hB).toEquiv,
        Nat.card_congr Multiplicative.ofAdd.symm]
      exact GaloisField.card 2 (2*m+1) (by omega)

include ν hC μ hB hn in
private theorem root_kernel_ne_bot (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hmpos : 0 < m) (k : Fin 2) (w : Weyl Q) : (rootAction Q split k w).ker ≠ ⊥ := by
  let s := UnitarySource.actorReflection Q split
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB s hcore
  have hH := ree_cartan_card Q split hm n hn m ν T hC μ hB s hcore
  have hr : Nat.card (rootAction Q split k w).range = 2^(2*m+1)-1 := by
    rw [Nat.card_congr (rootActionImageEquiv Q split k w).toEquiv]
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · rw [linear_cartanImage_card Q split 0 n hn.pos ν T hC (s 0),he]
    · exact suzuki_cartanImage_card Q split 1 m μ hB (s 1)
  intro hz
  have hc := (rootAction Q split k w).ker.card_mul_index
  rw [index_ker,hz,Nat.card_unique,one_mul,hr,hH] at hc
  have hq : 1 < 2^(2*m+1)-1 := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ 2*m+1 by omega)
    norm_num at hh
    omega
  nlinarith

include ν hC μ hB hn in
/-- Distinct root reflections distinguish the actual Cartan constituents
for positive Suzuki parameters. -/
theorem source_independent_root_kernels_distinct
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (k l : Fin 2) (w v : Weyl Q)
    (hne : w⁻¹*Q.simple k*w ≠ v⁻¹*Q.simple l*v) :
    (rootAction Q split k w).ker ≠ (rootAction Q split l v).ker := by
  have hfix (t : Fin 2) : reflectionFixed Q split t = (cartanPanelMap Q t).ker := by
    have ht : t = 0 ∨ t = 1 := by omega
    rcases ht with rfl | rfl
    · exact linear_reflectionFixed_eq_kernel Q split 0 n ν T hC (UnitarySource.actorReflection Q split 0)
    · exact suzuki_reflectionFixed_eq_kernel Q split 1 m μ hB (UnitarySource.actorReflection Q split 1)
  have hd := independent_rootAction_kernels Q split hm hfix
    (ree_longestCartanAction_inversion Q split hm n hn m ν T hC μ hB
      (UnitarySource.actorReflection Q split) hcore) k l w v hne
  intro he
  rw [he,inf_idem] at hd
  exact root_kernel_ne_bot Q split n hn m ν T hC μ hB hm hcore hmpos l v hd

include ν hC μ hB hn in
/-- Membership of an ordered product in the actual radical Frattini subgroup
forces membership of each coordinate. All root actions and separation
premises are discharged from the marked octagonal source. -/
theorem source_ordered_frattini_product_support
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (i : Fin 2) {r : ℕ} (k : Fin r → Fin 2) (w : Fin r → Weyl Q)
    (hA : ∀ t, rootAt Q split (k t) (w t) ≤ simpleRemainder Q split i)
    (hind : Pairwise fun t u => (w t)⁻¹*Q.simple (k t)*(w t) ≠
      (w u)⁻¹*Q.simple (k u)*(w u))
    (a : ∀ t, rootAt Q split (k t) (w t))
    (hz : (List.ofFn (fun t => (a t : X ⧸ Q.D))).prod ∈
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype) :
    ∀ t, (a t : X ⧸ Q.D) ∈
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
  have hKi : simpleRemainder Q split i ≤ localKernel Q i := by
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact marked_linear_remainder_le_kernel Q split 0 ν T hC
    · exact marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  exact separated_root_frattini_product_support Q split i hKi k w hA
    (fun t => source_root_frattini_irreducible Q split n hn m ν T hC μ hB (k t) (w t))
    (fun t u htu => source_independent_root_kernels_distinct Q split n hn m ν T hC μ hB
      hm hcore hmpos (k t) (k u) (w t) (w u) (hind htu)) a hz

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
