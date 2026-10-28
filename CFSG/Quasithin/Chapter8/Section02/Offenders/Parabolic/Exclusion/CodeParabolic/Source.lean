module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic.Marked
public import CFSG.Quasithin.ChapterD.Defs
public import Theory.Representation.ElementaryAbelianAction

/-!
# The original conjugation action in the exceptional code branch

The faithful image is the literal `internalActionImage` already used in
Hypothesis 3.1.5. The kernel calculation identifies its projection kernel
with the relative centralizer. A genuine code marking then gives the actor
rank bound and cubic displacement on the original module and its dual.
The final application retains M_V = M ∩ N_G(V) and the actual cubic
subgroups of C_M(Z); it does not assume that M normalizes V.

Source: Aschbacher–Smith, Proposition 8.2.2(1), printed p.715 (PDF p.732),
and the reductions after Hypothesis 7.0.2, printed p.695. The source module
marking, the two-group centralizer and C_M(Z) ≤ N_G(V) remain explicit earlier
inputs. These lemmas do not count chief factors or reconstruct H/O₂(H).
-/

public section
open scoped IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
open Subgroup Representation.BinaryOffender MathieuCode
open Sporadic.Mathieu (M22)
variable {G : Type*} [Group G] [Finite G]
    (K V : Subgroup G) [IsElementaryAbelian 2 V]
    (hMV : K ≤ normalizer (V : Set G))

/-- The original conjugation homomorphism, with its actual action image. -/
@[expose] def sourceConjugation : K →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion hMV)

/-- The source action of K on the additive copy of V. -/
@[expose] def sourceRepresentation : Representation (ZMod 2) K (Additive V) :=
  Representation.ofElementaryAbelianAction.comp (sourceConjugation K V hMV)

/-- The faithful source action, literally the range of conjugation. -/
@[expose] def faithfulSourceRepresentation :
    Representation (ZMod 2) (ChapterD.internalActionImage K V hMV) (Additive V) :=
  Representation.ofElementaryAbelianAction.comp
    (ChapterD.internalActionImage K V hMV).subtype

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- The kernel is precisely the relative centralizer C_K(V). -/
theorem sourceConjugation_ker :
    (sourceConjugation K V hMV).ker = (centralizer (V : Set G)).subgroupOf K := by
  ext m
  rw [MonoidHom.mem_ker]
  constructor
  · intro hm
    change m.val ∈ centralizer (V : Set G)
    rw [mem_centralizer_iff]
    intro v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩).val) hm
    change m.val * v * m.val⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hm
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change m.val * v.val * m.val⁻¹ = v.val
    have hc := mem_centralizer_iff.mp hm v.val v.property
    change v.val * m.val = m.val * v.val at hc
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

/-- The actual Aut_M(V) actors satisfy the minimum-rank requirement of 3.1.9(6). -/
theorem source_actor_rank
    (e : ChapterD.internalActionImage K V hMV ≃* MulAut M22)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ a v, E (faithfulSourceRepresentation K V hMV a v) =
      m22AutCodeRepresentation (e a) (E v))
    (A : Subgroup (ChapterD.internalActionImage K V hMV))
    (hA : IsElementaryTwo A)
    (hr : actionRatio (faithfulSourceRepresentation K V hMV) A ≤ 2) :
    2 ≤ rank A :=
  marked_code_actor_rank (faithfulSourceRepresentation K V hMV) e E hE A hA hr

/-- Apply the displacement calculation to the subgroup D of the acting subgroup K.
In 3.1.9(6) take K = M ∩ N_G(V) and D lying in C_M(Z). The two-group
centralizer premise is an earlier local-structure obligation, kept explicit. -/
theorem source_cubic_displacement
    (e : ChapterD.internalActionImage K V hMV ≃* MulAut M22)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ a v, E (faithfulSourceRepresentation K V hMV a v) =
      m22AutCodeRepresentation (e a) (E v))
    (hC : IsPGroup 2 ((centralizer (V : Set G)).subgroupOf K))
    (D : Subgroup K) (hD : Nat.card D = 3) :
    fixedCodim (sourceRepresentation K V hMV) D = 6 ∧
      fixedCodim (sourceRepresentation K V hMV).dual D = 6 := by
  let f : K →* MulAut M22 :=
    e.toMonoidHom.comp (sourceConjugation K V hMV).rangeRestrict
  have hk : f.ker = (sourceConjugation K V hMV).ker := by
    ext m
    change e ((sourceConjugation K V hMV).rangeRestrict m) = 1 ↔
      sourceConjugation K V hMV m = 1
    constructor
    · intro he
      have hh := e.injective (he.trans e.map_one.symm)
      exact congrArg Subtype.val hh
    · intro he
      have hh : (sourceConjugation K V hMV).rangeRestrict m = 1 := Subtype.ext he
      exact (congrArg e hh).trans e.map_one
  have hker : IsPGroup 2 f.ker := by rwa [hk, sourceConjugation_ker]
  have he : ∀ m v, E (sourceRepresentation K V hMV m v) =
      m22AutCodeRepresentation (f m) (E v) := by
    intro m v
    exact hE ((sourceConjugation K V hMV).rangeRestrict m) v
  exact ⟨marked_code_cubic_displacement _ f hker E he D hD,
    marked_code_dual_cubic_displacement _ f hker E he D hD⟩

/-- The literal C_M(Z) application, without assuming that all of M normalizes V.
The acting subgroup is M_V = M ∩ N_G(V), as in the source. -/
theorem centralizer_cubic_displacement
    (M V Z D : Subgroup G) [IsElementaryAbelian 2 V]
    (hZ : M ⊓ centralizer (Z : Set G) ≤ normalizer (V : Set G))
    (hDle : D ≤ M ⊓ centralizer (Z : Set G)) (hD : Nat.card D = 3)
    (e : ChapterD.internalActionImage (M ⊓ normalizer (V : Set G)) V inf_le_right ≃*
      MulAut M22)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ a v, E (faithfulSourceRepresentation
      (M ⊓ normalizer (V : Set G)) V inf_le_right a v) =
        m22AutCodeRepresentation (e a) (E v))
    (hC : IsPGroup 2 ((centralizer (V : Set G)).subgroupOf
      (M ⊓ normalizer (V : Set G)))) :
    fixedCodim (sourceRepresentation (M ⊓ normalizer (V : Set G)) V inf_le_right)
      (D.subgroupOf (M ⊓ normalizer (V : Set G))) = 6 ∧
    fixedCodim (sourceRepresentation (M ⊓ normalizer (V : Set G)) V inf_le_right).dual
      (D.subgroupOf (M ⊓ normalizer (V : Set G))) = 6 := by
  have hDM : D ≤ M ⊓ normalizer (V : Set G) :=
    le_inf (hDle.trans inf_le_left) (hDle.trans hZ)
  have hc : Nat.card (D.subgroupOf (M ⊓ normalizer (V : Set G))) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans hD
  exact source_cubic_displacement _ V inf_le_right e E hE hC _ hc

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
