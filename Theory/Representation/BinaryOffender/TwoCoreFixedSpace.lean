module

public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.GroupAction.CommutingFixedKernel
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Theory.PGroupCore

/-!
# Two-core fixed-space kernels

For a faithful binary representation, a subgroup commuting with a two-group
and fixing its fixed space is itself a two-group, by the P × Q lemma.
If a normal subgroup L has two-group quotient and the two-core Q centralizes L,
apply this to C_G(C_V(Q)) ∩ L. The kernel's image in G/L is also a two-group,
so the entire normal kernel is a two-group and equals Q.

This is the fixed-space argument of Aschbacher–Smith, *The Classification of
Quasithin Groups*, B.1.10–11, printed pp. 72–73, in the form needed for G = LA.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The P × Q lemma for a faithful binary linear action. -/
theorem isPGroup_of_commuting_fixes_fixedSpace (hfaith : Function.Injective ρ)
    (Q B : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQB : ⁅Q, B⁆ = ⊥) (hfix : B ≤ subspaceKernel ρ (fixedSpace ρ Q) ⊤) :
    IsPGroup 2 B := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  let f : G →* MulAut (Multiplicative V) := {
    toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by ext v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one v.toAdd)
    map_mul' g h := by ext v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g h) v.toAdd) }
  have hf : Function.Injective f := by
    intro x y heq
    apply hfaith
    ext v
    exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun heq (Multiplicative.ofAdd v))
  have hcomm : ⁅Q.map f, B.map f⁆ = ⊥ := by rw [← map_commutator, hQB, Subgroup.map_bot]
  have hfix' : B.map f ≤ fixingSubgroup (MulAut (Multiplicative V))
      (FixedPoints.subgroup (Q.map f) (Multiplicative V) : Set (Multiplicative V)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply Multiplicative.toAdd.injective
    apply (hfix hb).2
    intro q
    exact congrArg Multiplicative.toAdd (hv ⟨f q, mem_map_of_mem f q.property⟩)
  have hB := isPGroup_of_commuting_fixes_fixed (Q.map f) (B.map f)
    (hQ.map f) hcomm hfix'
  exact hB.of_injective (f.subgroupMap B) (fun x y h => Subtype.ext
    (hf (congrArg Subtype.val h)))

/-- The fixed-space kernel equals the two-core under a centralized two-group quotient. -/
theorem fixedSpace_kernel_eq_twoCore_of_centralizes [Finite G]
    (hfaith : Function.Injective ρ) (L : Subgroup G) [L.Normal]
    (hquot : IsPGroup 2 (G ⧸ L))
    (hcent : pCore 2 G ≤ centralizer (L : Set G)) :
    subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G := by
  let Q := pCore 2 G
  let R := subspaceKernel ρ (fixedSpace ρ Q) ⊤
  let f := invariantActionHom ρ (fixedSpace ρ Q) (fixedSpace_stable_of_normal ρ Q)
  have hRf : R = f.ker := (invariantActionHom_ker ρ _ _).symm
  let : R.Normal := hRf ▸ inferInstance
  have hB : IsPGroup 2 (R ⊓ L : Subgroup G) := by
    apply isPGroup_of_commuting_fixes_fixedSpace ρ hfaith Q (R ⊓ L) pCore_isPGroup
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact hcent.trans (centralizer_le (show (R ⊓ L : Subgroup G) ≤ L from inf_le_right))
    · exact inf_le_left
  let q : R →* G ⧸ L := (QuotientGroup.mk' L).comp R.subtype
  have hker : IsPGroup 2 q.ker := by
    apply hB.of_injective
      ({ toFun := fun x => ⟨x.val.val, x.val.property,
           (QuotientGroup.eq_one_iff _).mp x.property⟩
         map_one' := rfl
         map_mul' _ _ := rfl } : q.ker →* (R ⊓ L : Subgroup G))
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (R ⊓ L : Subgroup G) => (z : G)) h))
  have hRtop := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hker
  have hR : IsPGroup 2 R := by
    rw [comap_top] at hRtop
    exact hRtop.of_equiv Subgroup.topEquiv
  change R = Q
  apply le_antisymm (show R ≤ pCore 2 G from le_sSup ⟨inferInstance, hR⟩)
  intro g hg
  exact ⟨mem_top _, fun v hv => hv ⟨g, hg⟩⟩
end Representation.BinaryOffender
