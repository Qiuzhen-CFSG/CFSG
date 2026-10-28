module
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Representation.ElementaryAbelianAction
public import Theory.PGroupCore
public import Theory.GroupAction.HomomorphismFixedKernel

/-!
# Faithfulness on an elementary quotient by a central subgroup

Let A normalize a finite elementary abelian subgroup V and centralize Z.
Suppose the kernel of conjugation on V lies in O₂(A). Any element acting
trivially on V/Z belongs to a normal subgroup K fixing both Z∩V and V/Z.
The kernel-and-quotient automorphism theorem makes K a two-group, hence
K lies in O₂(A). Consequently any descended conjugation representation of
A/O₂(A) on the literal quotient V/(Z∩V) is faithful.

This is independent of irreducibility or a lower degree theorem. In
particular it applies to solvable actors such as Sz(2). The source
application is the Suzuki center layer in DGS85 (12.6), printed p.183.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- Centrality of Z and control of the whole-span kernel force faithfulness
on the actual quotient by Z∩V, retaining conjugation on representatives. -/
theorem central_quotient_conjugation_faithful (A V Z : Subgroup G) [Finite V]
    [IsElementaryAbelian 2 V] [(Z.subgroupOf V).Normal]
    (hAV : A ≤ normalizer (V : Set G))
    (hAZ : A ≤ centralizer (Z : Set G))
    (hC : (centralizer (V : Set G)).subgroupOf A ≤ pCore 2 A)
    (ρ : Representation (ZMod 2) (A ⧸ pCore 2 A)
      (Additive (V ⧸ Z.subgroupOf V)))
    (hρ : ∀ a : A, ∀ v : V,
      (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk v))).toMul =
        QuotientGroup.mk ⟨(a : G) * (v : G) * (a : G)⁻¹,
          (mem_normalizer_iff.mp (hAV a.property) v).mp v.property⟩) :
    Function.Injective ρ := by
  let π := QuotientGroup.mk' (pCore 2 A)
  let K := (ρ.comp π).ker
  let : MulDistribMulAction A V := conjMulDistribMulActionOfLeNormalizer A V hAV
  let f : K →* MulAut V := (MulDistribMulAction.toMulAut A V).comp K.subtype
  let d := QuotientGroup.mk' (Z.subgroupOf V)
  have hd : IsPGroup 2 d.ker := by
    rw [QuotientGroup.ker_mk']
    exact (IsElementaryAbelian.isPGroup 2 V).to_subgroup _
  have hf : IsPGroup 2 f.ker := by
    have hle : f.ker ≤ (pCore 2 A).comap K.subtype := by
      intro a ha
      apply hC
      intro v hv
      have he := DFunLike.congr_fun (show f a = 1 from ha) (⟨v,hv⟩ : V)
      have he' : ((a : A) : G) * v * ((a : A) : G)⁻¹ = v := congrArg Subtype.val he
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    exact (pCore_isPGroup.comap_of_injective K.subtype K.subtype_injective).to_le hle
  have hp : IsPGroup 2 K := d.isPGroup_of_fixes_kernel_and_quotient hd f hf
    (by
      intro a v
      have ha : ρ (π a.val) = 1 := a.property
      have he := hρ a.val v
      rw [show (QuotientGroup.mk a.val : A ⧸ pCore 2 A) = π a.val from rfl, ha] at he
      exact he.symm)
    (by
      intro a v
      apply Subtype.ext
      have hz : ((v : V) : G) ∈ Z := by
        have hv := v.property
        change (QuotientGroup.mk' (Z.subgroupOf V)) (v : V) = 1 at hv
        exact (QuotientGroup.eq_one_iff (v : V)).mp hv
      have he := hAZ a.val.property _ hz
      change ((a : A) : G) * ((v : V) : G) * ((a : A) : G)⁻¹ = _
      rw [←he, mul_inv_cancel_right])
  have hK : K ≤ pCore 2 A := le_sSup ⟨inferInstance,hp⟩
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro z hz
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) z
  exact (QuotientGroup.eq_one_iff a).mpr (hK hz)
end Subgroup
