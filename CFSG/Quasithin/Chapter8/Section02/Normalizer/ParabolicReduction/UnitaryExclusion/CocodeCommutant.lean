module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.GroupDeductions
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CoreAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The corrected cocode commutant in the unitary branch

The cocode in Proposition 8.2.8(5) is the literal binary quotient
`P/U`, with binary dimension 12.  The marked equivalence supplied by the
recognition part of the argument identifies it with a two by three array over
`𝔽₄`.  Scalar multiplication on that array gives an injective copy of
`𝔽₄ˣ` in the binary linear automorphisms, and the marked centralizer
calculation identifies the entire commutant with this copy.  Hence the
commutant has order three and has no element of order five.

The final theorem applies this calculation to the canonical conjugation action
on the literal quotient `P/U`.  Its hypotheses are exactly the marked scalar
recognition and the commuting action supplied by the preceding 8.2.8
calculation.  The kernel description from `TensorRecognition.CoreAction` then
turns triviality of the quotient action into `[P,X] ≤ U`.

Source: Aschbacher--Smith, Proposition 8.2.8(5) and Lemma 8.2.9,
printed pp. 718--720 (PDF pp. 735--737).
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion

/-- The corrected two-by-three cocode model over a field. -/
abbrev CocodeScalarSpace (F : Type*) := Fin 2 → Fin 3 → F

variable {F V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
variable [AddCommGroup V] [Module (ZMod 2) V]

/-- Scalar multiplication on a binary vector space after a marked `𝔽₄`-model. -/
noncomputable def cocodeScalarAction
    (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F) (c : Fˣ) : V ≃ₗ[ZMod 2] V where
  toFun v := e.symm (c.val • e v)
  invFun v := e.symm (c⁻¹.val • e v)
  left_inv v := by simp [smul_smul]
  right_inv v := by simp [smul_smul]
  map_add' v w := by simp [map_add]
  map_smul' a v := by
    change e.symm (c.val • e (a • v)) = a • e.symm (c.val • e v)
    rw [e.map_smul, smul_comm, ← e.symm.map_smul]

/-- The multiplicative map from field units to the binary scalar action. -/
noncomputable def cocodeScalarMap
    (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F) : Fˣ →* (V ≃ₗ[ZMod 2] V) where
  toFun c := cocodeScalarAction e c
  map_one' := by
    ext v
    simp [cocodeScalarAction]
  map_mul' c d := by
    ext v
    simp [cocodeScalarAction, mul_smul]

omit [Finite F] in
lemma cocodeScalarMap_injective (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F) :
    Function.Injective (cocodeScalarMap e) := by
  intro c d h
  have hh := congrArg
    (fun f : V ≃ₗ[ZMod 2] V => e (f (e.symm (fun _ _ => (1 : F))))) h
  have hh' := congrArg (fun z : CocodeScalarSpace F => z 0 0) hh
  apply Units.ext
  simpa [cocodeScalarMap, cocodeScalarAction] using hh'

omit [Finite F] [Algebra (ZMod 2) F] in
lemma cocode_card_units_four (hF : Nat.card F = 4) : Nat.card Fˣ = 3 := by
  rw [Nat.card_units, hF]

omit [Finite F] in
lemma cocodeScalarMap_range_card (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F)
    (hF : Nat.card F = 4) : Nat.card (cocodeScalarMap e).range = 3 := by
  rw [MonoidHom.range_eq_map]
  calc
    Nat.card ((⊤ : Subgroup Fˣ).map (cocodeScalarMap e)) = Nat.card (⊤ : Subgroup Fˣ) :=
      Nat.card_congr ((Subgroup.equivMapOfInjective (⊤ : Subgroup Fˣ)
        (cocodeScalarMap e) (cocodeScalarMap_injective e)).toEquiv).symm
    _ = Nat.card Fˣ := Subgroup.card_top
    _ = 3 := cocode_card_units_four hF

omit [Finite F] in
lemma cocode_order_five_scalar_eq_one
    (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F) (hF : Nat.card F = 4)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ (cocodeScalarMap e).range)
    (ha5 : a ^ 5 = 1) : a = 1 := by
  let C := (cocodeScalarMap e).range
  let z : C := ⟨a, ha⟩
  have h3 := (pow_card_eq_one' (x := z))
  rw [cocodeScalarMap_range_card e hF] at h3
  have h5 : z ^ 5 = 1 := by simpa [z] using ha5
  have ho : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 3 5) (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one h5)
  have hz : z = 1 := orderOf_eq_one_iff.mp ho
  exact congrArg Subtype.val hz

/- The marked cocode commutant is exactly the scalar copy of `𝔽₄ˣ`. -/
omit [Finite F] in
lemma cocode_centralizer_card_eq_three
    (S : Set (V ≃ₗ[ZMod 2] V))
    (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F) (hF : Nat.card F = 4)
    (hscalar : ∀ a : V ≃ₗ[ZMod 2] V,
      a ∈ centralizer S ↔ a ∈ (cocodeScalarMap e).range) :
    Nat.card (centralizer S) = 3 := by
  have heq : centralizer S = (cocodeScalarMap e).range := by
    ext a
    exact hscalar a
  rw [heq]
  exact cocodeScalarMap_range_card e hF

/- The corrected cocode commutant has no element of order five. -/
omit [Finite F] in
lemma cocode_centralizer_no_order_five
    (S : Set (V ≃ₗ[ZMod 2] V))
    (e : V ≃ₗ[ZMod 2] CocodeScalarSpace F) (hF : Nat.card F = 4)
    (hscalar : ∀ a : V ≃ₗ[ZMod 2] V,
      a ∈ centralizer S ↔ a ∈ (cocodeScalarMap e).range)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ centralizer S)
    (ha5 : a ^ 5 = 1) : a = 1 := by
  exact cocode_order_five_scalar_eq_one e hF ((hscalar a).mp ha) ha5

/-- Binary linearization of the automorphism group of an elementary abelian group. -/
noncomputable def cocodeMulAutLinear (Q : Type*) [Group Q]
    [IsElementaryAbelian 2 Q] :
    MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) where
  toFun a := { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

lemma cocodeMulAutLinear_injective (Q : Type*) [Group Q]
    [IsElementaryAbelian 2 Q] :
    Function.Injective (cocodeMulAutLinear Q) := by
  intro a b h
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f : Additive Q ≃ₗ[ZMod 2] Additive Q =>
    f (Additive.ofMul x)) h

private theorem cocode_space_finrank :
    Module.finrank (ZMod 2) (CocodeScalarSpace (GaloisField 2 2)) = 12 := by
  change Module.finrank (ZMod 2) (Fin 2 → Fin 3 → GaloisField 2 2) = 12
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [GaloisField.finrank (p := 2) (n := 2) (by decide)]

private theorem cocode_first_finrank :
    Module.finrank (ZMod 2) (Fin 2 → GaloisField 2 2) = 4 := by
  rw [Module.finrank_pi_fintype]
  simp [GaloisField.finrank (p := 2) (n := 2) (by decide)]

private theorem cocode_second_finrank :
    Module.finrank (ZMod 2) (Fin 3 → GaloisField 2 2) = 6 := by
  rw [Module.finrank_pi_fintype]
  simp [GaloisField.finrank (p := 2) (n := 2) (by decide)]

/-- The literal cocode and its two corrected `𝔽₄` factors have dimensions 12, 4 and 6. -/
theorem corrected_cocode_finranks :
    Module.finrank (ZMod 2) (CocodeScalarSpace (GaloisField 2 2)) = 12 ∧
      Module.finrank (ZMod 2) (Fin 2 → GaloisField 2 2) = 4 ∧
      Module.finrank (ZMod 2) (Fin 3 → GaloisField 2 2) = 6 := by
  exact ⟨cocode_space_finrank, cocode_first_finrank, cocode_second_finrank⟩

/--
The corrected cocode commutant supplies the uniform `hlayer` premise in
`exists_five_centralizing_pair`.  The marked equivalence and its centralizer
recognition are explicit hypotheses because they are the outputs of the
preceding source calculations.
-/
theorem cocode_hlayer_of_marked_centralizer
    {H : Type*} [Group H]
    (I U X : Subgroup H) [I.Normal] [U.Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    (hX : Nat.card X = 5)
    (_hXI : X ≤ normalizer (I : Set H))
    (S : Set (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))))
    (e : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
      CocodeScalarSpace (GaloisField 2 2))
    (hscalar : ∀ a : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
      a ∈ centralizer S ↔ a ∈ (cocodeScalarMap e).range)
    (hcomm : ∀ x ∈ X,
      cocodeMulAutLinear (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))
        (TensorRecognition.coreQuotientAction I U x) ∈ centralizer S) :
    ⁅I.pCoreIn 2, X⁆ ≤ U := by
  let P := I.pCoreIn 2
  let Q := P ⧸ U.subgroupOf P
  let q := TensorRecognition.coreQuotientAction I U
  have hF : Nat.card (GaloisField 2 2) = 4 := GaloisField.card 2 2 (by decide)
  apply commutator_le.mpr
  intro p hp x hx
  have hx5 : x ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : X))
    simpa [hX] using congrArg Subtype.val h
  have hq5 : q x ^ 5 = 1 := by
    rw [← map_pow, hx5, map_one]
  have hl5 : (cocodeMulAutLinear Q (q x)) ^ 5 = 1 := by
    rw [← map_pow, hq5, map_one]
  have hlC : cocodeMulAutLinear Q (q x) ∈ centralizer S := hcomm x hx
  have hlR : cocodeMulAutLinear Q (q x) ∈ (cocodeScalarMap e).range :=
    (hscalar _).mp hlC
  have hl1 := cocode_order_five_scalar_eq_one e hF hlR hl5
  have hq1 : q x = 1 := cocodeMulAutLinear_injective Q hl1
  have hxker : x ∈ q.ker := MonoidHom.mem_ker.mpr hq1
  rw [TensorRecognition.coreQuotientAction_kernel I U] at hxker
  exact (mem_centralizerModulo_iff.mp hxker).2 p hp


/--
A uniform wrapper in the exact shape required by
`exists_five_centralizing_pair`.  The preceding 8.2.8 action calculation is
used only through `hcomm`; it proves that every eligible order-five subgroup
has quotient action in the marked commutant.
-/
theorem cocode_uniform_hlayer
    {H : Type*} [Group H]
    (M I U : Subgroup H) [I.Normal] [U.Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    (S : Set (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))))
    (e : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
      CocodeScalarSpace (GaloisField 2 2))
    (hscalar : ∀ a : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
      a ∈ centralizer S ↔ a ∈ (cocodeScalarMap e).range)
    (hcomm : ∀ (X : Subgroup H), X ≤ M → Nat.card X = 5 →
      X ≤ normalizer (I : Set H) →
      X.map (QuotientGroup.mk' (pCore 2 H)) ≤
        centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) →
      ∀ x ∈ X,
        cocodeMulAutLinear (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))
          (TensorRecognition.coreQuotientAction I U x) ∈ centralizer S) :
    ∀ X : Subgroup H, X ≤ M → Nat.card X = 5 →
      X ≤ normalizer (I : Set H) →
      X.map (QuotientGroup.mk' (pCore 2 H)) ≤
        centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) →
      ⁅I.pCoreIn 2, X⁆ ≤ U := by
  intro X hXM hX hXI hXC
  exact cocode_hlayer_of_marked_centralizer I U X hX hXI S e hscalar
    (hcomm X hXM hX hXI hXC)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion
