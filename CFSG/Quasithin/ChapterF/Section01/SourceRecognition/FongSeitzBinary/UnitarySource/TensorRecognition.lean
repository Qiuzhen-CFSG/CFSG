module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorTorus
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition

/-!
# Recognition of the actual U₄ complementary module

Apply the proved small binary SL₂ classifier to the actual conjugation
representation, aligned to the specified root-actor reflection. The
source commutator and order give irreducibility and binary degree 4n.
The field has order 2^(2n), so the exceptional SL₂(8) branch is impossible.
The smaller simple root has order 2^n and is normalized by the aligned
torus. The free-orbit bound excludes the natural branch, also for n=1.
The remaining branch supplies an actual Hermitian intertwiner on this
same remainder and an actual identification of its acting field.

This proves the module selection used in Fong--Seitz II (8B), p.201.
Its input commutator, section order and elementary structure are supplied
by QuadraticLinearActors.marked_quadratic_linear_sixA. The application
module discharges them from that literal original-source producer.
Compatible labels for the other endpoint and the scalar-field alignment
remain later source-coordinate obligations; no full recognition is claimed.

Source: Fong--Seitz I (4C), (6A)(b), pp.20--21,37--38; II (8B), p.201.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hij : i ≠ j) (hm : rotationOrder Q = 4)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  [IsElementaryAbelian 2 (simpleRemainder Q split i)]
  (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)

include hij hm in
/-- The actual remainder is the Hermitian module, with no module-comparison premise. -/
theorem aligned_remainder_hermitian (n : ℕ) (hn : 0 < n)
    (hF : Nat.card F = 2 ^ (2*n))
    (hR : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2)
    (hsmall : Nat.card (simpleRoot Q split j) = 2^n)
    (hcomm : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split j (Q.simple i)) :
    let : NeZero n := ⟨hn.ne'⟩
    Representation.SL2.BinarySmall.IsHermitian
      (alignedRemainderRepresentation Q split i hV μ s) n := by
  let : NeZero n := ⟨hn.ne'⟩
  let ρ := elementaryRepresentation (p := 2) (remainderRankOneAction Q split i hV)
  let σ := alignedRemainderRepresentation Q split i hV μ s
  let a := alignedPinning Q split i hV μ s
  let : ρ.IsIrreducible := quadratic_remainder_irreducible Q split hm i j hij hV
    a.symm (by omega) hF hR hcomm
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff a.toMonoidHom a.surjective ρ).mpr inferInstance
  have hd : Module.finrank (ZMod 2) (Additive (simpleRemainder Q split i)) = 4*n := by
    have hc : Nat.card (simpleRemainder Q split i) =
        2 ^ Module.finrank (ZMod 2) (Additive (simpleRemainder Q split i)) := by
      change Nat.card (Additive (simpleRemainder Q split i)) = _
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (simpleRemainder Q split i)))
    rw [hc,hF,←pow_mul] at hR
    have hh := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hR
    omega
  have hnt : ∃ g, σ g ≠ 1 := by
    obtain ⟨r,hr⟩ := remainderRankOneAction_nontrivial Q split hm i j hij hV hcomm
    refine ⟨a.symm r,fun he => hr ?_⟩
    apply DFunLike.ext
    intro v
    have hv := LinearMap.congr_fun he (Additive.ofMul v)
    change Additive.ofMul (remainderRankOneAction Q split i hV (a (a.symm r)) v) =
      Additive.ofMul v at hv
    change remainderRankOneAction Q split i hV r v = v
    simpa only [MulEquiv.apply_symm_apply] using Additive.ofMul.injective hv
  rcases ChapterG.Section09.DefiningCharacteristic.binary_small_module_alternatives
    σ hnt (2*n) (by omega) hF (by omega) with hnat | hherm | htriple
  · have hb := natural_remainder_torus_bound Q split i hV μ s j hij hnat.2.2
    rw [hF,hsmall, mul_comm 2 n,pow_mul] at hb
    have hq : 2 ≤ 2^n := Nat.one_lt_pow hn.ne' (by decide)
    have hsq0 : 1 ≤ (2^n)^2 := le_trans (by decide : 1 ≤ 2^2) (Nat.pow_le_pow_left hq 2)
    have hsq : 2^n < (2^n)^2-1 := by nlinarith [Nat.sub_add_cancel hsq0]
    omega
  · obtain ⟨he,_,hs,hh⟩ := hherm
    have heq : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] σ.asModule) = n := by omega
    simpa only [heq] using hh
  · omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
