module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Mathlib.GroupTheory.Sylow

/-!
# Cubic witnesses for binary fixed spaces

An element of order three normalizing a two-subgroup fixes its fixed space
through an extension whenever it does so on the submodule and quotient.
Indeed its displacement on a fixed vector lies in the fixed part of the
submodule; a unipotent cubic operator in characteristic two is the identity.
Thus this argument applies to nonsplit extensions as well as direct sums.

A witness on any two-subgroup yields witnesses on every Sylow two-subgroup:
enlarge the subgroup to a Sylow subgroup and conjugate. The cubic element
cannot belong to a two-group.

These are the extension and Sylow transport arguments used in the small
alternating-module comparison in Aschbacher–Smith, Lemma 15.4.18, p.1163,
with the module alternatives of B.5.1, p.99.
-/

public section
namespace Representation.BinaryOffender
open Subgroup

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem cubic_fixed_of_fixed_displacement
    (ρ : Representation (ZMod 2) G V) (d : G) (h3 : d ^ 3 = 1) (v : V)
    (h : ρ d (ρ d v - v) = ρ d v - v) : ρ d v = v := by
  have h2 : ρ d (ρ d v) = v := by
    rw [map_sub] at h
    have hsum (x : V) : x + x = 0 := by
      simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul]
        using (add_smul (1 : ZMod 2) 1 x).symm
    have hn (x : V) : -x = x := neg_eq_iff_add_eq_zero.mpr (hsum x)
    simp only [sub_eq_add_neg, hn] at h
    exact add_right_cancel (h.trans (add_comm _ _))
  have hh := congrArg (ρ d) h2
  have hpow : ρ d (ρ d (ρ d v)) = v := by
    change (ρ d * ρ d * ρ d) v = v
    rw [← map_mul, ← map_mul]
    rw [show d * d * d = d ^ 3 by simp [pow_succ], h3, map_one,
      Module.End.one_apply]
  exact hh.symm.trans hpow

/-- A normalizer preserves the fixed space. -/
theorem fixedSpace_apply_mem_of_normalizes (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (d : G) (hd : d ∈ normalizer (A : Set G))
    {v : V} (hv : v ∈ fixedSpace ρ A) : ρ d v ∈ fixedSpace ρ A := by
  intro a
  have ha : d⁻¹ * (a : G) * d ∈ A := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hd) a).mp a.property
  have h := congrArg (ρ d) (hv ⟨_, ha⟩)
  change ρ d (ρ (d⁻¹ * (a : G) * d) v) = ρ d v at h
  change ρ (a : G) (ρ d v) = ρ d v
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left,
    mul_assoc, inv_mul_cancel, mul_one] using h

/-- Lifting through an equivariant map with pointwise fixed kernel. Neither
surjectivity nor a splitting of the map is required. -/
theorem cubic_fixedSpace_of_map (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (A : Subgroup G) (d : G)
    (h3 : d ^ 3 = 1)
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = σ g (q v))
    (hker : ∀ v ∈ q.ker, ρ d v = v)
    (hfix : ∀ w ∈ fixedSpace σ A, σ d w = w) :
    ∀ v ∈ fixedSpace ρ A, ρ d v = v := by
  intro v hv
  apply cubic_fixed_of_fixed_displacement ρ d h3 v
  apply hker
  change q (ρ d v - v) = 0
  rw [map_sub, hq, hfix]
  · exact sub_self _
  · intro a
    change σ (a : G) (q v) = q v
    rw [← hq]
    exact congrArg q (hv a)

/-- The central submodule–natural section–trivial quotient configuration.
The submodule and the whole module may both be nonsplit extensions. -/
theorem cubic_fixedSpace_of_central_section
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (A : Subgroup G) (d : G) (h3 : d ^ 3 = 1)
    (hn : d ∈ normalizer (A : Set G))
    (U : Subrepresentation ρ) (q : U.toSubmodule →ₗ[ZMod 2] W)
    (hq : ∀ g u, q (U.toRepresentation g u) = σ g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ g v - v ∈ U)
    (hfix : ∀ w ∈ fixedSpace σ A, σ d w = w) :
    ∀ v ∈ fixedSpace ρ A, ρ d v = v := by
  have hU := cubic_fixedSpace_of_map U.toRepresentation σ A d h3 q hq
    (fun u hu => hker d u hu) hfix
  intro v hv
  apply cubic_fixed_of_fixed_displacement ρ d h3 v
  let u : U.toSubmodule := ⟨ρ d v - v, hquot d v⟩
  have hu : u ∈ fixedSpace U.toRepresentation A := by
    intro a
    apply Subtype.ext
    exact (fixedSpace ρ A).sub_mem
      (fixedSpace_apply_mem_of_normalizes ρ A d hn hv) hv a
  exact congrArg Subtype.val (hU u hu)

/-- A nonidentity cubic element never belongs to a two-subgroup. -/
theorem cubic_not_mem_twoSubgroup (A : Subgroup G) (hA : IsPGroup 2 A)
    (d : G) (h3 : d ^ 3 = 1) (hne : d ≠ 1) : d ∉ A := by
  intro hd
  have hc := hA.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨d, hd⟩ : A)
  have hdiv : orderOf (⟨d, hd⟩ : A) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext h3)
  have he := hc.eq_one_of_dvd hdiv
  exact hne (congrArg Subtype.val (orderOf_eq_one_iff.mp he))

/-- A cubic fixed-space witness for one two-subgroup yields a witness for
every Sylow two-subgroup, by containment and conjugacy. -/
theorem sylow_fixedSpace_enlargement_of_cubic [Finite G]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (hA : IsPGroup 2 A)
    (d : G) (h3 : d ^ 3 = 1) (hne : d ≠ 1)
    (hfix : ∀ v ∈ fixedSpace ρ A, ρ d v = v) (S : Sylow 2 G) :
    ∃ c : G, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup G), ρ c v = v := by
  obtain ⟨T, hAT⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hS : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hc3 : (MulAut.conj g d) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  refine ⟨MulAut.conj g d,
    cubic_not_mem_twoSubgroup (S : Subgroup G) S.isPGroup' _ hc3
      (fun h => hne ((MulAut.conj g).map_eq_one_iff.mp h)), hc3, ?_⟩
  intro v hv
  have hinv (x : V) : ρ g⁻¹ (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : V) : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hw : ρ g⁻¹ v ∈ fixedSpace ρ A := by
    intro a
    have ha : g * (a : G) * g⁻¹ ∈ (S : Subgroup G) := by
      rw [← hS]
      exact ⟨a, hAT a.property, rfl⟩
    have hh := congrArg (ρ g⁻¹) (hv ⟨_, ha⟩)
    change ρ g⁻¹ (ρ (g * (a : G) * g⁻¹) v) = ρ g⁻¹ v at hh
    change ρ (a : G) (ρ g⁻¹ v) = ρ g⁻¹ v
    simpa only [map_mul, Module.End.mul_apply, hinv] using hh
  change ρ (g * d * g⁻¹) v = v
  simp only [map_mul, Module.End.mul_apply, hfix _ hw, hginv]

/-- The witness may be constructed in an embedded subgroup. The ambient
Sylow subgroup need not have the same order as a Sylow subgroup of the model. -/
theorem sylow_fixedSpace_enlargement_of_embedded_cubic
    {D : Type*} [Group D] [Finite D]
    (ρ : Representation (ZMod 2) D V) (f : G →* D) (hf : Function.Injective f)
    (A : Subgroup G) (hA : IsPGroup 2 A) (d : G) (h3 : d ^ 3 = 1) (hne : d ≠ 1)
    (hfix : ∀ v ∈ fixedSpace (ρ.comp f) A, ρ (f d) v = v) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  apply sylow_fixedSpace_enlargement_of_cubic ρ (A.map f) (hA.map f) (f d)
    (by rw [← map_pow, h3, map_one])
    (fun h => hne (hf (h.trans f.map_one.symm))) _ S
  intro v hv
  apply hfix v
  intro a
  exact hv ⟨f a, ⟨a, a.property, rfl⟩⟩

/-- A cubic witness lifts through an equivariant map with a trivial kernel.
In particular this allows arbitrary trivial summands on the original module. -/
theorem sylow_fixedSpace_enlargement_of_cubic_quotient
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = σ g (q v))
    (hker : ∀ g, ∀ v ∈ q.ker, ρ g v = v) (S : Sylow 2 G)
    (hmodel : ∃ d : G, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace σ (S : Subgroup G), σ d w = w) :
    ∃ d : G, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup G), ρ d v = v := by
  obtain ⟨d, hd, h3, hfix⟩ := hmodel
  exact ⟨d, hd, h3, cubic_fixedSpace_of_map ρ σ (S : Subgroup G) d h3 q hq
    (hker d) hfix⟩

end Representation.BinaryOffender
