module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.DerivedRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorRealization

/-!
# Fixed-point obstruction on the linear U₅ Frattini section

The linear radical has central Frattini subgroup. Its whole crossed unitary
root therefore maps to the Frattini section with kernel contained in that
root's intrinsic center. The linear simple root centralizes this image.
A Hermitian SL₂(q²) module has just q fixed vectors under that simple root,
forcing the crossed root to have order at most q times its center order.
The actual orders q³ and q contradict this, also when q = 2.

The CFSG LinearNatural consumer uses this obstruction to select the natural
module and construct coordinates for the actual reflection-pinned actor.
Source: Fong--Seitz I (6A)(c); II (8C), pp.203,208, (8.14), (8.32)--(8.33).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus.FiniteModel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

private theorem classTwo_join {Y : Type*} [Group Y] (B D : Subgroup Y)
    (hB : ⁅B,B⁆ ≤ centralizer (B : Set Y))
    (hD : ⁅D,D⁆ ≤ centralizer (D : Set Y))
    (hBD : ⁅B,D⁆ ≤ centralizer ((B ⊔ D : Subgroup Y) : Set Y))
    (hder : ⁅B ⊔ D,B ⊔ D⁆ = ⁅B,B⁆ ⊔ ⁅B,D⁆ ⊔ ⁅D,D⁆) :
    ⁅B ⊔ D,B ⊔ D⁆ ≤ centralizer ((B ⊔ D : Subgroup Y) : Set Y) := by
  have hBDB : ⁅⁅B,D⁆,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hBD.trans (centralizer_le (show B ≤ B ⊔ D from le_sup_left)))
  have hBDD : ⁅⁅B,D⁆,D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hBD.trans (centralizer_le (show D ≤ B ⊔ D from le_sup_right)))
  have hBBD : ⁅⁅B,B⁆,D⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hBDB (by rwa [commutator_comm D B])
  have hDDB : ⁅⁅D,D⁆,B⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by rwa [commutator_comm D B]) hBDD
  rw [hder]
  refine sup_le (sup_le ?_ hBD) ?_
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hB)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBBD))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDDB))
      (le_centralizer_iff.mp hD)

private theorem special_central {Y : Type*} [Group Y] (B : Subgroup Y)
    (hB : _root_.commutator B = center B) : ⁅B,B⁆ ≤ centralizer (B : Set Y) := by
  rw [←map_subtype_commutator,hB]
  rintro x ⟨b,hb,rfl⟩
  exact mem_centralizer_iff.mpr (fun y hy => congrArg Subtype.val (mem_center_iff.mp hb ⟨y,hy⟩))

variable {X K E : Type*} [Group X] [Field K] [Finite K] [CharP K 2]
  [Field E] [Finite E] [CharP E 2] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2) (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include hn hE hfixed hJ hm hij hVi hVj s ν in
/-- The entire linear radical's Frattini subgroup is central. -/
theorem linear_frattini_central
    (hAi : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hcard : Nat.card (simpleRoot Q split i) = (2^n)^2)
    (hcomm : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j)) :
    (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype ≤
      centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
  obtain ⟨hphi,hder,_,_⟩ := unitary_linear_layers Q split J hn hE hfixed hJ hm i j hij hVi hVj ν hAi hcard hcomm
  have hz := (unitary_simpleRoot_special Q split J hn hE hfixed hJ j hVj ν).2
  have hV := unitary_remainder_eq_two_roots Q split hm i j hij hcomm
  rw [hphi,map_subtype_commutator]
  have hd : ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ ≤
      centralizer (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) := by
    rw [crossed_derived_center_eq Q split i j s hz]
    rintro x ⟨d,hd,rfl⟩
    exact mem_centralizer_iff.mpr (fun y hy => congrArg Subtype.val (mem_center_iff.mp hd ⟨y,hy⟩))
  rw [hV] at hder ⊢
  apply classTwo_join _ _ (special_central _ hz) hd
  · rw [hcomm]
    apply le_centralizer_iff.mpr
    exact sup_le
      (commutator_eq_bot_iff_le_centralizer.mp (adjacent_roots_commute Q split hm j i hij.symm hVj hVi))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (middle_roots_commute Q split hm i j hij hVi hVj)))
  · rwa [hcomm]

/-- The actual linear Frattini representation, with its full specified actor. -/
def linearFrattiniRepresentation (μ : rankOne Q split i ≃* SL(2,K)) :
    Representation (ZMod 2) SL(2,K)
      (Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))) :=
  (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)).comp μ.symm.toMonoidHom



section FixedBound
variable [NeZero n]
local instance : Module (ZMod 2) (Space n) := SL2.BinarySmall.spaceBinaryModule n
variable (μ : rankOne Q split i ≃* SL(2,K))
  (hroot : ((rankOne Q split i).subtype.comp
    (μ.symm.toMonoidHom.comp (Matrix.SpecialLinearGroup.upperUnipotentHom K))).range = simpleRoot Q split i)
  (hcentral : (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype ≤
    centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))

include hm hij hVj hroot hcentral
omit [Finite K] [CharP K 2] in
/-- A Hermitian model would bound the crossed root by its center times q.
The actual source root has order q³ and center q, so this excludes that model. -/
theorem hermitian_frattini_root_bound
    (hh : SL2.BinarySmall.IsHermitian (linearFrattiniRepresentation Q split i hVi μ) n) :
    Nat.card (rootAt Q split j (Q.simple i)) ≤
      Nat.card (center (rootAt Q split j (Q.simple i))) * 2^n := by
  obtain ⟨ξ,⟨c⟩⟩ := hh
  let V := simpleRemainder Q split i
  let D := rootAt Q split j (Q.simple i)
  have hDV : D ≤ V := (opposite_roots_le_remainder Q split j i hij.symm).2
  let q := (QuotientGroup.mk' (frattini V)).comp (inclusion hDV)
  let φ : D →* Multiplicative (Space n) := {
    toFun d := .ofAdd (c (.ofMul (q d)))
    map_one' := by rw [map_one]; exact congrArg Multiplicative.ofAdd c.map_zero
    map_mul' x y := by simp only [map_mul,ofMul_mul,map_add,ofAdd_add] }
  have hfix (d : D) : (φ d).toAdd ∈
      BinaryOffender.fixedSpace (SL2.BinarySmall.hermitian n)
        (Matrix.SpecialLinearGroup.upperUnipotent (Field n)) := by
    intro a
    obtain ⟨u,hu⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mp a.property
    let a' := Matrix.SpecialLinearGroup.upperUnipotentHom K (.ofAdd (ξ.symm u))
    have he : Matrix.SpecialLinearGroup.map ξ.toRingHom a' = a.val := by
      rw [←hu]
      ext k l
      fin_cases k <;> fin_cases l <;>
        simp [a',Matrix.SpecialLinearGroup.upperUnipotentHom,Matrix.SpecialLinearGroup.transvection_coe]
    have ha : (μ.symm a' : X ⧸ Q.D) ∈ simpleRoot Q split i := hroot ▸ ⟨.ofAdd (ξ.symm u),rfl⟩
    have hc : Commute (μ.symm a' : X ⧸ Q.D) (d : X ⧸ Q.D) :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (adjacent_roots_commute Q split hm i j hij hVi hVj) ha) d d.property).symm
    have hact : remainderRankOneAction Q split i hVi (μ.symm a') (inclusion hDV d) = inclusion hDV d := by
      apply Subtype.ext
      rw [remainderRankOneAction_apply]
      change (μ.symm a' : X ⧸ Q.D)*d*(μ.symm a' : X ⧸ Q.D)⁻¹ = d
      rw [hc.eq,mul_inv_cancel_right]
    have ht := LinearMap.congr_fun (c.isIntertwining' a') (.ofMul (q d))
    change c (.ofMul (remainderFrattiniAction Q split i hVi (μ.symm a') (q d))) =
      SL2.BinarySmall.hermitian n (Matrix.SpecialLinearGroup.map ξ.toRingHom a') (c (.ofMul (q d))) at ht
    rw [he] at ht
    dsimp only [q,MonoidHom.comp_apply] at ht
    rw [remainderFrattiniAction_mk,hact] at ht
    exact ht.symm
  have hker : φ.ker ≤ center D := by
    intro d hd
    have hz : q d = 1 := by
      apply Additive.ofMul.injective
      exact c.injective ((congrArg Multiplicative.toAdd hd).trans c.map_zero.symm)
    have hf : inclusion hDV d ∈ frattini V := (QuotientGroup.eq_one_iff _).mp hz
    have hdv := hcentral (mem_map_of_mem V.subtype hf)
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_iff.mp hdv x (hDV x.property)
  let t : φ.range → fixedField n := fun x =>
    OrthogonalFourMinus.RankOne.upperFixedEquiv n ⟨x.val.toAdd,by
      obtain ⟨d,hd⟩ := x.property
      rw [←hd]
      exact hfix d⟩
  have ht : Function.Injective t := by
    intro x y hxy
    have he := (OrthogonalFourMinus.RankOne.upperFixedEquiv n).injective hxy
    apply Subtype.ext
    exact Multiplicative.toAdd.injective (congrArg (fun z : BinaryOffender.fixedSpace (SL2.BinarySmall.hermitian n) (Matrix.SpecialLinearGroup.upperUnipotent (Field n)) => z.val) he)
  have hcard : Nat.card φ.range ≤ 2^n :=
    (Nat.card_le_card_of_injective t ht).trans_eq (card_fixedField n)
  have hc := φ.ker.card_mul_index
  rw [index_ker] at hc
  calc
    Nat.card D = Nat.card φ.ker * Nat.card φ.range := hc.symm
    _ ≤ Nat.card (center D) * 2^n := Nat.mul_le_mul (Nat.card_le_card_of_injective (inclusion hker) (inclusion_injective hker)) hcard
end FixedBound

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
