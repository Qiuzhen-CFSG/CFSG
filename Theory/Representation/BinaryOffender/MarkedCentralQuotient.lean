module

public import Theory.Representation.IrreducibleMovedPlaneSections
public import Theory.Representation.BinaryOffender.IrreducibleCentralSeed
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Mathlib.Order.OrderIsoNat

/-!
# Central quotients from an irreducible moved plane

If K=[K,v] and V=[V,K], an invariant subspace not centralized by K
contains the entire irreducible moved plane of v. The quotient by that
subspace is fixed by v and hence by K, so it is zero. Consequently C_V(K)
is the unique maximal invariant subspace. This argument keeps central
extensions and proves, rather than assumes, that the central quotient is chief.

For a faithful action and simple perfect normal K, the action on V/C_V(K)
is faithful: its kernel centralizes K and its displacement vanishes on [V,K].
Finite invariant chief flags are constructed, and the unique-noncentral-factor
conclusion is proved for every such flag when all proper subspaces are central.

Source application: Aschbacher–Smith, 13.5.21(3), printed p.924 (PDF p.941).
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The full K-fixed space, invariant under the ambient group by normality. -/
def fixedSubrepresentation (K : Subgroup G) [K.Normal] : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ K
  apply_mem_toSubmodule g x hx :=
    (fixedSpace_stable_of_normalizes ρ (show (⊤ : Subgroup G) ≤ normalizer (K : Set G)
      from le_normalizer_of_normal) (mem_top g) x).2 hx

/-- The literal quotient V/C_V(K), with its induced ambient action. -/
abbrev fixedQuotient (K : Subgroup G) [K.Normal] :=
  (fixedSubrepresentation ρ K).quotientRepresentation

/-- Kernel membership means that every displacement lies in the actual fixed space. -/
theorem quotient_kernel_iff (K : Subgroup G) [K.Normal] (g : G) :
    g ∈ (fixedQuotient ρ K).ker ↔ ∀ x, ρ g x - x ∈ fixedSpace ρ K := by
  constructor
  · intro hg x
    have he := LinearMap.congr_fun hg ((fixedSpace ρ K).mkQ x)
    exact (Submodule.Quotient.eq _).mp he
  · intro hg
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (fixedSpace ρ K).mkQ_surjective x
    exact (Submodule.Quotient.eq _).mpr (hg x)

/-- A proper invariant subspace is central: the moved plane forces every noncentral one to be all of V. -/
theorem MovedPlane.eq_top_or_central (K L : Subgroup G) (v : G)
    (p : MovedPlane ρ L v) (hgen : ⁅K, zpowers v⁆ = K)
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) (N : Subrepresentation ρ) :
    N = ⊤ ∨ N.toSubmodule ≤ fixedSpace ρ K := by
  classical
  by_cases hN : N.toSubmodule ≤ fixedSpace ρ K
  · exact Or.inr hN
  left
  have hn : ¬ K ≤ (sectionRepresentation ρ ⊥ N).ker := by
    intro hn
    apply hN
    intro x hx k
    have he := (sectionRepresentation_trivial_iff ρ ⊥ N k).mp
      (fun w => LinearMap.congr_fun (hn k.property) w) x hx
    exact sub_eq_zero.mp he
  have hm := generator_moves_of_noncentral _ K v hgen hn
  have hpN := p.le_upper ⊥ N hm
  have hv : v ∈ N.quotientRepresentation.ker := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := N.toSubmodule.mkQ_surjective q
    apply (Submodule.Quotient.eq _).mpr
    exact hpN (p.moved.symm ▸ (show ρ v x - x ∈ LinearMap.range (ρ v - 1) from ⟨x, rfl⟩))
  have hKN : K ≤ N.quotientRepresentation.ker := by
    rw [← hgen]
    exact (commutator_mono le_rfl (zpowers_le.mpr hv)).trans
      (commutator_le_right K N.quotientRepresentation.ker)
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hwhole]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, x, _, rfl⟩
  exact (Submodule.Quotient.eq _).mp
    (LinearMap.congr_fun (hKN hk) (N.toSubmodule.mkQ x))

/-- The central quotient is genuinely chief; chiefness is not a premise. -/
theorem MovedPlane.central_isCoatom (K L : Subgroup G) [K.Normal] (v : G)
    (p : MovedPlane ρ L v) (hgen : ⁅K, zpowers v⁆ = K)
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤)
    (hn : ¬ K ≤ ρ.ker) : IsCoatom (fixedSubrepresentation ρ K) := by
  refine ⟨?_, ?_⟩
  · intro he
    apply hn
    intro k hk
    apply LinearMap.ext
    intro x
    have hx : x ∈ fixedSubrepresentation ρ K := by rw [he]; trivial
    exact hx ⟨k, hk⟩
  · intro N hN
    rcases p.eq_top_or_central ρ K L v hgen hwhole N with ht | hc
    · exact ht
    · exact ((not_le_of_gt hN) hc).elim

end Representation.BinaryOffender

namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A perfect noncentral action remains noncentral on its fixed-space quotient. -/
theorem fixedQuotient_noncentral (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hn : ¬ K ≤ ρ.ker) : ¬ K ≤ (fixedQuotient ρ K).ker := by
  intro hc
  apply hn
  have hfix : (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K := by
    apply le_fixedSpace_of_commutator_le_fixedSpace ρ K ⊤
      (le_subspaceStabilizer ρ _ (fun _ _ _ _ => Submodule.mem_top))
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, x, _, rfl⟩
    exact (quotient_kernel_iff ρ K k).mp (hc hk) x
  intro k hk
  exact LinearMap.ext (fun x => hfix Submodule.mem_top ⟨k, hk⟩)

/-- Faithfulness on K lifts to the whole group using V=[V,K]. -/
theorem fixedQuotient_faithful (K : Subgroup G) [K.Normal]
    (hρ : Function.Injective ρ)
    (hK : Function.Injective ((fixedQuotient ρ K).comp K.subtype))
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) :
    Function.Injective (fixedQuotient ρ K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change g = 1
  apply hρ
  apply LinearMap.ext
  intro x
  have hcomm (k : K) : g * k.val = k.val * g := by
    have he : (⟨g * k.val * g⁻¹, (inferInstance : K.Normal).conj_mem k.val k.property g⟩ : K) = k := by
      apply hK
      change fixedQuotient ρ K (g * k.val * g⁻¹) = fixedQuotient ρ K k.val
      simp only [map_mul, show fixedQuotient ρ K g = 1 from hg, one_mul]
      have hi : fixedQuotient ρ K g⁻¹ = 1 := by
        have hh := congrArg (fixedQuotient ρ K) (inv_mul_cancel g)
        simpa only [map_mul, show fixedQuotient ρ K g = 1 from hg, mul_one, map_one] using hh
      rw [hi, mul_one]
    have he' := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul).mp he'
  have hx : x ∈ subspaceCommutator ρ ⊤ K := by rw [hwhole]; trivial
  simp only [map_one, Module.End.one_apply]
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, hk, y, _, rfl⟩ := hz
    have he : ρ g (ρ k y) = ρ k (ρ g y) := by
      exact LinearMap.congr_fun ((ρ.map_mul g k).symm.trans
        ((congrArg ρ (hcomm ⟨k, hk⟩)).trans (ρ.map_mul k g))) y
    have hf := ((quotient_kernel_iff ρ K g).mp hg y) ⟨k, hk⟩
    change ρ k (ρ g y - y) = ρ g y - y at hf
    rw [map_sub] at hf
    rw [map_sub, he]
    exact sub_eq_sub_iff_sub_eq_sub.mp hf
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul a z _ hz => rw [map_smul, hz]

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Simplicity discharges faithfulness of K on the central quotient. -/
theorem simple_fixedQuotient_faithful (K : Subgroup G) [K.Normal]
    [IsSimpleGroup K] [Group.IsPerfect K]
    (hρ : Function.Injective ρ) (hn : ¬ K ≤ ρ.ker)
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) :
    Function.Injective (fixedQuotient ρ K) := by
  apply fixedQuotient_faithful ρ K hρ _ hwhole
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases ((fixedQuotient ρ K).comp K.subtype).normal_ker.eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    apply fixedQuotient_noncentral ρ K hn
    intro k hk
    exact (show (⟨k, hk⟩ : K) ∈ ((fixedQuotient ρ K).comp K.subtype).ker from
      ht.symm ▸ mem_top _)

/-- An irreducible quotient by a central subspace and full commutator generation
make every proper invariant subspace central. -/
theorem eq_top_or_central_of_irreducible_central_quotient (K : Subgroup G)
    (C : Subrepresentation ρ) (hC : C.toSubmodule ≤ fixedSpace ρ K)
    [IsIrreducible C.quotientRepresentation]
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) (N : Subrepresentation ρ) :
    N = ⊤ ∨ N.toSubmodule ≤ fixedSpace ρ K := by
  rcases C.le_or_sup_eq_top_of_irreducible_quotient N with hc | ht
  · exact Or.inr (fun x hx => hC (hc hx))
  left
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hwhole]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, x, _, rfl⟩
  obtain ⟨c, hc, n, hn, he⟩ := Submodule.mem_sup.mp (ht.symm ▸ Submodule.mem_top (x := x))
  rw [← he, map_add, show ρ k c = c from hC hc ⟨k, hk⟩, add_sub_add_left_eq_sub]
  exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule k hn) hn

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Construct an exhaustive chief flag in the finite invariant-subspace lattice. -/
theorem exists_chief_flag [Finite V] :
    ∃ (c : ℕ → Subrepresentation ρ) (n : ℕ),
      Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧ ∀ i < n, c i ⋖ c (i + 1) := by
  classical
  obtain ⟨a, ha0, n, han, ha⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
      (show (⊥ : Subrepresentation ρ) ≤ ⊤ from bot_le)
  let c : ℕ → Subrepresentation ρ := fun i => a (min i n)
  have hc : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi),
        Nat.min_eq_left hi] using (ha i hi).le
    · simp only [c, Nat.min_eq_right (by omega : n ≤ i),
        Nat.min_eq_right (by omega : n ≤ i + 1), le_refl]
  refine ⟨c, n, hc, ?_, ?_, ?_⟩
  · simpa only [c, Nat.zero_min] using ha0
  · simpa only [c, Nat.min_self] using han
  · intro i hi
    simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi] using ha i hi

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every exhaustive chief flag has exactly one noncentral factor. -/
theorem unique_noncentral_in_flag (K : Subgroup G)
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) (hn : ¬ K ≤ ρ.ker)
    (hmax : ∀ N : Subrepresentation ρ, N = ⊤ ∨ N.toSubmodule ≤ fixedSpace ρ K)
    (c : ℕ → Subrepresentation ρ) (n : ℕ)
    (hzero : c 0 = ⊥) (hstop : c n = ⊤) (hchief : ∀ i < n, c i ⋖ c (i + 1)) :
    ∃! i, i < n ∧ ¬ K ≤ (sectionRepresentation ρ (c i) (c (i + 1))).ker := by
  have hn0 : 0 < n := by
    by_contra hh
    have he : (⊥ : Subrepresentation ρ) = ⊤ := hzero.symm.trans (by simpa [show n = 0 by omega] using hstop)
    apply hn
    intro k hk
    apply LinearMap.ext
    intro x
    have hx : x = 0 := (show x ∈ (⊥ : Subrepresentation ρ) from he.symm ▸ (by trivial))
    simp only [hx, map_zero]
  have hi : n - 1 < n := by omega
  have hil : n - 1 + 1 = n := by omega
  have hlast : ¬ K ≤ (sectionRepresentation ρ (c (n - 1)) (c (n - 1 + 1))).ker := by
    intro hk
    have hle : subspaceCommutator ρ ⊤ K ≤ (c (n - 1)).toSubmodule := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hkK, x, _, rfl⟩
      exact (sectionRepresentation_trivial_iff _ _ _ _).mp
        (fun w => LinearMap.congr_fun (hk hkK) w) x
        (by rw [hil, hstop]; trivial)
    have he : c (n - 1) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact top_unique (hwhole ▸ hle)
    exact (hchief (n - 1) hi).lt.ne (by rw [hil, hstop, he])
  refine ⟨n - 1, ⟨hi, hlast⟩, ?_⟩
  rintro j ⟨hj, hnon⟩
  rcases hmax (c (j + 1)) with ht | hfix
  · by_contra hne
    have hjn : j + 1 < n := by omega
    have := (hchief (j + 1) hjn).lt
    rw [ht] at this
    exact not_lt_of_ge le_top this
  · exfalso
    apply hnon
    intro k hk
    apply LinearMap.ext
    intro w
    apply (sectionRepresentation_trivial_iff _ _ _ _).mpr _ w
    intro x hx
    rw [show ρ k x = x from hfix hx ⟨k, hk⟩, sub_self]
    exact (c j).toSubmodule.zero_mem

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Transport irreducibility through a surjective actor map and equivariant linear coordinates. -/
theorem irreducible_of_surjective_equivariant
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
    (f : G →* H) (hf : Function.Surjective f) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v))
    (hi : IsIrreducible σ) : IsIrreducible ρ := by
  let := hi
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : Nontrivial V := e.symm.injective.nontrivial
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation σ := ⟨S.toSubmodule.map e.toLinearMap, by
    intro h x hx
    obtain ⟨g, rfl⟩ := hf h
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, he g v⟩⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have h : e v ∈ T := ⟨v, hv, rfl⟩
    rw [hb] at h
    exact e.map_eq_zero_iff.mp h
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    have h : e v ∈ T := by rw [ht]; trivial
    obtain ⟨w, hw, he⟩ := h
    exact (e.injective he) ▸ hw

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original irreducible moved plane embeds into every noncentral quotient. -/
theorem MovedPlane.quotientMap_injective (K L : Subgroup G) (v : G)
    (p : MovedPlane ρ L v) (hgen : ⁅K, zpowers v⁆ = K)
    (N : Subrepresentation ρ) (hn : ¬ K ≤ N.quotientRepresentation.ker) :
    Function.Injective (N.toSubmodule.mkQ.comp p.plane.toSubmodule.subtype) := by
  have hs : ¬ K ≤ (sectionRepresentation ρ N ⊤).ker := by
    intro hs
    apply hn
    intro k hk
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := N.toSubmodule.mkQ_surjective q
    apply (Submodule.Quotient.eq _).mpr
    exact (sectionRepresentation_trivial_iff _ _ _ _).mp
      (fun w => LinearMap.congr_fun (hs hk) w) x (by trivial)
  have hm := generator_moves_of_noncentral _ K v hgen hs
  have hi := p.sectionMap_injective N ⊤ hm
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply hi
  rw [map_zero]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (x : V) ∈ N.toSubmodule
  exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hx

end Representation.BinaryOffender
