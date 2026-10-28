module

public import Theory.Representation.BinaryPermutation
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Tactic
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Tensor decomposition for an inverted cubic action in characteristic two

Let K and S₃ act linearly and commute on a binary module V. If the normal
cubic subgroup of S₃ has zero fixed space, the fixed space I of a transposition
is a K-module and V is equivariantly isomorphic to I tensor the concrete
natural module `BinaryPermutation.core (Fin 3)`. Restriction to K is I × I.
The definitions `productTensorEquiv` and `productPairEquiv` provide the actual
linear equivalences for a representation of K × S₃.

For a cubic generator r and inverter t, the inverse to (a,b) ↦ a + r(b) has
coordinates (v + r(v + t(v)), v + t(v)). The identity 1 + r + r² = 0 follows
from the zero-fixed-space hypothesis. The same norm operator vanishes on
cubic commutators, so commutator generation implies that hypothesis. This
identity also passes through invariant subspaces and equivariant quotients,
which supplies the transport to chief sections. No semisimplicity assumption
on the ambient group or its binary module is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.20,
external-X alternative (a), printed p.954 (PDF p.971), combined manuscript
of 1 March 2004. This is the conditional representation-theoretic input;
the ambient subgroup and action hypotheses remain explicit.
-/

public section

namespace InvertedCubicTensor
abbrev F := ZMod 2
abbrev S₃ := Equiv.Perm (Fin 3)
/-- A fixed three-cycle, generating the normal cubic subgroup. -/
@[expose] def cubic : S₃ := Equiv.swap 0 1 * Equiv.swap 1 2
/-- A transposition inverting the chosen three-cycle. -/
@[expose] def inverter : S₃ := Equiv.swap 0 1
lemma cubic_cube : cubic * cubic * cubic = 1 := by decide +kernel
lemma inverter_square : inverter * inverter = 1 := by decide +kernel
lemma inverts_cubic : inverter * cubic = cubic * cubic * inverter := by decide +kernel
private lemma words (g : S₃) :
    g = 1 ∨ g = cubic ∨ g = cubic * cubic ∨ g = inverter ∨
      g = cubic * inverter ∨ g = cubic * cubic * inverter := by
  revert g
  decide +kernel
variable {V : Type*} [AddCommGroup V] [Module F V]
private lemma double (v : V) : v + v = 0 := by
  simpa only [show (1 : F) + 1 = 0 by decide, zero_smul, one_smul] using (add_smul (1 : F) 1 v).symm
private lemma neg (v : V) : -v = v := neg_eq_iff_add_eq_zero.mpr (double v)
variable (σ : Representation F S₃ V)
private lemma cubic_cube_apply (v : V) : σ cubic (σ cubic (σ cubic v)) = v := by
  change (σ cubic * σ cubic * σ cubic) v = v
  rw [← map_mul, ← map_mul, cubic_cube, map_one, Module.End.one_apply]
private lemma inverter_square_apply (v : V) : σ inverter (σ inverter v) = v := by
  change (σ inverter * σ inverter) v = v
  rw [← map_mul, inverter_square, map_one, Module.End.one_apply]
private lemma inverter_cubic_apply (v : V) :
    σ inverter (σ cubic v) = σ cubic (σ cubic (σ inverter v)) := by
  change (σ inverter * σ cubic) v = (σ cubic * σ cubic * σ inverter) v
  rw [← map_mul, ← map_mul, ← map_mul, inverts_cubic]
private lemma norm_zero (h : ∀ v, σ cubic v = v → v = 0) (v : V) :
    v + σ cubic v + σ cubic (σ cubic v) = 0 := by
  apply h
  simp only [map_add, cubic_cube_apply]
  abel
private lemma cubic_square_apply (h : ∀ v, σ cubic v = v → v = 0) (v : V) :
    σ cubic (σ cubic v) = v + σ cubic v := by
  have hh := norm_zero σ h v
  have := eq_neg_of_add_eq_zero_right hh
  simpa only [neg_add, neg] using this

/-- The fixed space of the chosen inverter; it carries the multiplicity module. -/
@[expose] def multiplicitySpace : Submodule F V := (σ inverter - LinearMap.id).ker
lemma mem_multiplicitySpace (v : V) : v ∈ multiplicitySpace σ ↔ σ inverter v = v := by
  change σ inverter v - v = 0 ↔ _
  exact sub_eq_zero
private lemma second_mem (v : V) : v + σ inverter v ∈ multiplicitySpace σ := by
  rw [mem_multiplicitySpace, map_add, inverter_square_apply]
  exact add_comm _ _
private lemma first_mem (h : ∀ v, σ cubic v = v → v = 0) (v : V) :
    v + σ cubic (v + σ inverter v) ∈ multiplicitySpace σ := by
  rw [mem_multiplicitySpace, map_add, inverter_cubic_apply,
    (mem_multiplicitySpace σ _).mp (second_mem σ v), cubic_square_apply σ h]
  abel_nf
  simp only [two_zsmul, double, zero_add]

private def pairMap : (multiplicitySpace σ × multiplicitySpace σ) →ₗ[F] V where
  toFun x := x.1.val + σ cubic x.2.val
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' c x := by simp

/-- The explicit decomposition V = I + rI, with its coordinate inverse. -/
def pairEquiv (h : ∀ v, σ cubic v = v → v = 0) :
    (multiplicitySpace σ × multiplicitySpace σ) ≃ₗ[F] V :=
  { pairMap σ with
    invFun := fun v => (⟨v + σ cubic (v + σ inverter v), first_mem σ h v⟩,
      ⟨v + σ inverter v, second_mem σ v⟩)
    left_inv := by
      rintro ⟨a, b⟩
      have ha := (mem_multiplicitySpace σ _).mp a.property
      have hb := (mem_multiplicitySpace σ _).mp b.property
      have hs : (a.val + σ cubic b.val) + σ inverter (a.val + σ cubic b.val) = b.val := by
        rw [map_add, ha, inverter_cubic_apply, hb, cubic_square_apply σ h]
        have hh := double a.val
        have hh' := double (σ cubic b.val)
        abel_nf at *
        simp_all
      apply Prod.ext <;> apply Subtype.ext
      · change (a.val + σ cubic b.val) +
          σ cubic ((a.val + σ cubic b.val) + σ inverter (a.val + σ cubic b.val)) = a.val
        rw [hs, add_assoc, double, add_zero]
      · exact hs
    right_inv := by
      intro v
      change (v + σ cubic (v + σ inverter v)) + σ cubic (v + σ inverter v) = v
      rw [add_assoc, double, add_zero] }

/-- The two coordinates reconstruct a vector as a + r(b). -/
lemma pairEquiv_apply (h : ∀ v, σ cubic v = v → v = 0)
    (x : multiplicitySpace σ × multiplicitySpace σ) :
    pairEquiv σ h x = x.1.val + σ cubic x.2.val := by rfl

/-- The two coordinates of the concrete natural module. -/
private def naturalCoordinates : BinaryPermutation.core (Fin 3) ≃ₗ[F] (F × F) where
  toFun n := (n.val 0, n.val 2)
  invFun x := ⟨![x.1, x.1 + x.2, x.2], by
    rw [BinaryPermutation.mem_core, Fin.sum_univ_three]
    change x.1 + (x.1 + x.2) + x.2 = 0
    calc
      _ = (x.1 + x.1) + (x.2 + x.2) := by abel
      _ = 0 := by rw [double, double, add_zero]⟩
  left_inv n := by
    apply Subtype.ext
    have hn := n.property
    rw [BinaryPermutation.mem_core] at hn
    rw [Fin.sum_univ_three] at hn
    funext i
    fin_cases i
    · rfl
    · change n.val 0 + n.val 2 = n.val 1
      rw [add_assoc] at hn
      have h := eq_neg_of_add_eq_zero_left hn
      simp only [neg] at h
      have : n.val 0 + n.val 2 = (n.val 1 + n.val 2) + n.val 2 := congrArg (· + n.val 2) h
      simpa only [add_assoc, double, add_zero] using this
    · rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

open scoped TensorProduct
private noncomputable def tensorCoordinates :
    multiplicitySpace σ ⊗[F] BinaryPermutation.core (Fin 3) ≃ₗ[F] (multiplicitySpace σ × multiplicitySpace σ) :=
  (TensorProduct.congr (LinearEquiv.refl F (multiplicitySpace σ)) naturalCoordinates).trans
    ((TensorProduct.prodRight F F (multiplicitySpace σ) F F).trans
      ((TensorProduct.rid F (multiplicitySpace σ)).prodCongr (TensorProduct.rid F (multiplicitySpace σ))))

private lemma tensorCoordinates_tmul (i : multiplicitySpace σ) (n : BinaryPermutation.core (Fin 3)) :
    tensorCoordinates σ (i ⊗ₜ[F] n) = (n.val 0 • i, n.val 2 • i) := by
  simp [tensorCoordinates, TensorProduct.rid_tmul]
  constructor <;> rfl

/-- The tensor equivalence for the symmetric-three action. -/
noncomputable def tensorEquiv (h : ∀ v, σ cubic v = v → v = 0) :
    multiplicitySpace σ ⊗[F] BinaryPermutation.core (Fin 3) ≃ₗ[F] V :=
  (tensorCoordinates σ).trans (pairEquiv σ h)

lemma tensorEquiv_tmul (h : ∀ v, σ cubic v = v → v = 0)
    (i : multiplicitySpace σ) (n : BinaryPermutation.core (Fin 3)) :
    tensorEquiv σ h (i ⊗ₜ[F] n) = n.val 0 • i.val + n.val 2 • σ cubic i.val := by
  change pairEquiv σ h (tensorCoordinates σ _) = _
  rw [tensorCoordinates_tmul]
  change _ + σ cubic (_ • _) = _
  rw [map_smul]
  rfl

private lemma natural_middle (n : BinaryPermutation.core (Fin 3)) : n.val 1 = n.val 0 + n.val 2 := by
  have hn := n.property
  rw [BinaryPermutation.mem_core, Fin.sum_univ_three, add_assoc] at hn
  have h := eq_neg_of_add_eq_zero_left hn
  rw [neg] at h
  have := congrArg (· + n.val 2) h
  simpa only [add_assoc, double, add_zero] using this.symm

private lemma tensorEquiv_cubic (h : ∀ v, σ cubic v = v → v = 0)
    (i : multiplicitySpace σ) (n : BinaryPermutation.core (Fin 3)) :
    tensorEquiv σ h (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) cubic n) =
      σ cubic (tensorEquiv σ h (i ⊗ₜ[F] n)) := by
  rw [tensorEquiv_tmul, tensorEquiv_tmul, map_add, map_smul, map_smul, cubic_square_apply σ h]
  change n.val 2 • i.val + n.val 1 • σ cubic i.val = _
  rw [natural_middle, add_smul, smul_add]
  abel

private lemma tensorEquiv_inverter (h : ∀ v, σ cubic v = v → v = 0)
    (i : multiplicitySpace σ) (n : BinaryPermutation.core (Fin 3)) :
    tensorEquiv σ h (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) inverter n) =
      σ inverter (tensorEquiv σ h (i ⊗ₜ[F] n)) := by
  rw [tensorEquiv_tmul, tensorEquiv_tmul, map_add, map_smul, map_smul,
    (mem_multiplicitySpace σ _).mp i.property, inverter_cubic_apply, (mem_multiplicitySpace σ _).mp i.property, cubic_square_apply σ h]
  change n.val 1 • i.val + n.val 2 • σ cubic i.val = _
  rw [natural_middle, add_smul, smul_add]
  abel

lemma tensorEquiv_symmetric (h : ∀ v, σ cubic v = v → v = 0)
    (g : S₃) (i : multiplicitySpace σ) (n : BinaryPermutation.core (Fin 3)) :
    tensorEquiv σ h (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) g n) =
      σ g (tensorEquiv σ h (i ⊗ₜ[F] n)) := by
  have hm (a b : S₃)
      (ha : ∀ n, tensorEquiv σ h (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) a n) =
        σ a (tensorEquiv σ h (i ⊗ₜ[F] n)))
      (hb : ∀ n, tensorEquiv σ h (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) b n) =
        σ b (tensorEquiv σ h (i ⊗ₜ[F] n))) (n) :
      tensorEquiv σ h (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) (a * b) n) =
        σ (a * b) (tensorEquiv σ h (i ⊗ₜ[F] n)) := by
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  rcases words g with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact tensorEquiv_cubic σ h i n
  · exact hm cubic cubic (tensorEquiv_cubic σ h i) (tensorEquiv_cubic σ h i) n
  · exact tensorEquiv_inverter σ h i n
  · exact hm cubic inverter (tensorEquiv_cubic σ h i) (tensorEquiv_inverter σ h i) n
  · exact hm (cubic * cubic) inverter (hm cubic cubic (tensorEquiv_cubic σ h i) (tensorEquiv_cubic σ h i))
      (tensorEquiv_inverter σ h i) n

variable {K : Type*} [Group K] (κ : Representation F K V)
  (hc : ∀ k g v, κ k (σ g v) = σ g (κ k v))

/-- The actual multiplicity representation, on the inverter-fixed subspace. -/
@[expose] def multiplicity : Representation F K (multiplicitySpace σ) where
  toFun k := (κ k).restrict (by
    intro v hv
    rw [mem_multiplicitySpace] at hv ⊢
    rw [← hc, hv])
  map_one' := by ext v; exact LinearMap.congr_fun κ.map_one v
  map_mul' k l := by ext v; exact LinearMap.congr_fun (κ.map_mul k l) v

lemma multiplicity_apply (k : K) (i : multiplicitySpace σ) :
    (multiplicity σ κ hc k i).val = κ k i.val := rfl

/-- The two isomorphic K-summands are exhibited by a linear equivalence. -/
lemma pairEquiv_equivariant (h : ∀ v, σ cubic v = v → v = 0)
    (k : K) (x : multiplicitySpace σ × multiplicitySpace σ) :
    pairEquiv σ h (multiplicity σ κ hc k x.1, multiplicity σ κ hc k x.2) =
      κ k (pairEquiv σ h x) := by
  change κ k x.1.val + σ cubic (κ k x.2.val) = κ k (x.1.val + σ cubic x.2.val)
  rw [map_add, hc]

lemma tensorEquiv_multiplicity (h : ∀ v, σ cubic v = v → v = 0)
    (k : K) (i : multiplicitySpace σ) (n : BinaryPermutation.core (Fin 3)) :
    tensorEquiv σ h (multiplicity σ κ hc k i ⊗ₜ[F] n) =
      κ k (tensorEquiv σ h (i ⊗ₜ[F] n)) := by
  simp only [tensorEquiv_tmul, multiplicity_apply, map_add, map_smul, hc]

/-- The external tensor product with the concrete binary natural S3-module. -/
@[expose] noncomputable def tensorRepresentation :
    Representation F (K × S₃) (multiplicitySpace σ ⊗[F] BinaryPermutation.core (Fin 3)) :=
  Representation.tprod ((multiplicity σ κ hc).comp (MonoidHom.fst K S₃))
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.snd K S₃))

/-- Tensor decomposition for commuting K and S3 actions. -/
lemma tensorEquiv_equivariant (h : ∀ v, σ cubic v = v → v = 0)
    (k : K) (g : S₃) (z : multiplicitySpace σ ⊗[F] BinaryPermutation.core (Fin 3)) :
    tensorEquiv σ h (tensorRepresentation σ κ hc (k,g) z) =
      κ k (σ g (tensorEquiv σ h z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul i n =>
    change tensorEquiv σ h (multiplicity σ κ hc k i ⊗ₜ[F]
      BinaryPermutation.coreRepresentation (Fin 3) g n) = _
    rw [tensorEquiv_multiplicity, tensorEquiv_symmetric]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma alternating_words (g : S₃) (hg : g ∈ alternatingGroup (Fin 3)) :
    g = 1 ∨ g = cubic ∨ g = cubic * cubic := by
  have h : ∀ g : S₃, Equiv.Perm.sign g = 1 → g = 1 ∨ g = cubic ∨ g = cubic * cubic := by
    decide +kernel
  exact h g (Equiv.Perm.mem_alternatingGroup.mp hg)

lemma fixedFree_iff_fixedSpace_eq_bot :
    (∀ v, σ cubic v = v → v = 0) ↔
      Representation.BinaryOffender.fixedSpace σ (alternatingGroup (Fin 3)) = ⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro v hv
    exact h v (hv ⟨cubic, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩)
  · intro h v hv
    have hmem : v ∈ Representation.BinaryOffender.fixedSpace σ (alternatingGroup (Fin 3)) := by
      intro g
      change σ (g : S₃) v = v
      rcases alternating_words g g.property with he | he | he
      · simp [he]
      · simpa only [he] using hv
      · simp only [he, map_mul, Module.End.mul_apply, hv]
    simpa only [h, Submodule.mem_bot] using hmem

/-- The cubic averaging operator, without division (three is one over F2). -/
private def normMap : V →ₗ[F] V := LinearMap.id + σ cubic + σ cubic * σ cubic
private lemma normMap_apply (v : V) : normMap σ v = v + σ cubic v + σ cubic (σ cubic v) := rfl
private lemma normMap_cubic (v : V) : normMap σ (σ cubic v) = normMap σ v := by
  simp only [normMap_apply, cubic_cube_apply]
  abel
private lemma normMap_commutator (g : S₃) (hg : g ∈ alternatingGroup (Fin 3)) (v : V) :
    normMap σ (σ g v - v) = 0 := by
  rw [map_sub]
  apply sub_eq_zero.mpr
  rcases alternating_words g hg with rfl | rfl | rfl
  · simp
  · exact normMap_cubic σ v
  · simp only [map_mul, Module.End.mul_apply, normMap_cubic]

private lemma fixedFree_of_normMap_zero (hn : ∀ v, normMap σ v = 0) :
    ∀ v, σ cubic v = v → v = 0 := by
  intro v hv
  have hh := hn v
  simpa only [normMap_apply, hv, double, zero_add] using hh

/-- Generation by cubic commutators removes the entire cubic fixed space. -/
lemma fixedFree_of_commutator_eq_top
    (hgen : Representation.BinaryOffender.subspaceCommutator σ ⊤
      (alternatingGroup (Fin 3)) = ⊤) :
    ∀ v, σ cubic v = v → v = 0 := by
  apply fixedFree_of_normMap_zero
  have hle : Representation.BinaryOffender.subspaceCommutator σ ⊤
      (alternatingGroup (Fin 3)) ≤ (normMap σ).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    exact normMap_commutator σ g hg v
  rw [hgen] at hle
  intro v
  exact hle (Submodule.mem_top)

variable {W : Type*} [AddCommGroup W] [Module F W]
/-- Zero cubic fixed space descends through an equivariant surjection. -/
lemma fixedFree_of_surjective (τ : Representation F S₃ W)
    (q : V →ₗ[F] W) (hq : Function.Surjective q)
    (he : ∀ v, q (σ cubic v) = τ cubic (q v))
    (h : ∀ v, σ cubic v = v → v = 0) : ∀ w, τ cubic w = w → w = 0 := by
  apply fixedFree_of_normMap_zero
  intro w
  obtain ⟨v, rfl⟩ := hq w
  have hn := congrArg q (norm_zero σ h v)
  simpa only [map_add, he, map_zero, normMap_apply] using hn

/-- Zero cubic fixed space passes to an equivariant submodule. -/
lemma fixedFree_of_injective (τ : Representation F S₃ W)
    (j : W →ₗ[F] V) (hj : Function.Injective j)
    (he : ∀ w, j (τ cubic w) = σ cubic (j w))
    (h : ∀ v, σ cubic v = v → v = 0) : ∀ w, τ cubic w = w → w = 0 := by
  intro w hw
  apply hj
  rw [map_zero]
  apply h
  rw [← he, hw]

/-- Every equivariant quotient of an invariant subspace retains zero cubic fixed space.
This is the form used for chief sections. -/
lemma fixedFree_on_subquotient (U : Subrepresentation σ) (τ : Representation F S₃ W)
    (q : U.toSubmodule →ₗ[F] W) (hq : Function.Surjective q)
    (he : ∀ u, q (U.toRepresentation cubic u) = τ cubic (q u))
    (h : ∀ v, σ cubic v = v → v = 0) : ∀ w, τ cubic w = w → w = 0 := by
  apply fixedFree_of_surjective U.toRepresentation τ q hq he
  exact fixedFree_of_injective σ U.toRepresentation U.toSubmodule.subtype
    U.toSubmodule.subtype_injective (fun _ => rfl) h

section Ambient
variable {G : Type*} [Group G] (ρ : Representation F G V)
  (f : K →* G) (s : S₃ →* G) (hs : ∀ k g, Commute (f k) (s g))

include hs in
/-- Commuting ambient subgroups give the commuting actions used above. -/
lemma ambient_commute (k : K) (g : S₃) (v : V) :
    (ρ.comp f) k ((ρ.comp s) g v) = (ρ.comp s) g ((ρ.comp f) k v) := by
  change (ρ (f k) * ρ (s g)) v = (ρ (s g) * ρ (f k)) v
  rw [← map_mul, ← map_mul, (hs k g).eq]

/-- Ambient cubic commutators give the required hypothesis after pullback. -/
lemma ambient_fixedFree_of_commutator
    (hgen : Representation.BinaryOffender.subspaceCommutator ρ ⊤
      ((alternatingGroup (Fin 3)).map s) = ⊤) :
    ∀ v, (ρ.comp s) cubic v = v → v = 0 := by
  apply fixedFree_of_normMap_zero
  have hle : Representation.BinaryOffender.subspaceCommutator ρ ⊤
      ((alternatingGroup (Fin 3)).map s) ≤ (normMap (ρ.comp s)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨g, hg, rfl⟩, v, _, rfl⟩
    exact normMap_commutator (ρ.comp s) g hg v
  rw [hgen] at hle
  intro v
  exact hle Submodule.mem_top

/-- The constructed tensor map intertwines the actual ambient commuting actions. -/
lemma ambient_tensorEquiv_equivariant
    (h : ∀ v, ρ (s cubic) v = v → v = 0)
    (k : K) (g : S₃) (z : multiplicitySpace (ρ.comp s) ⊗[F] BinaryPermutation.core (Fin 3)) :
    tensorEquiv (ρ.comp s) h
      (tensorRepresentation (ρ.comp s) (ρ.comp f) (ambient_commute ρ f s hs) (k,g) z) =
      ρ (f k * s g) (tensorEquiv (ρ.comp s) h z) := by
  rw [tensorEquiv_equivariant]
  simp only [MonoidHom.comp_apply, map_mul, Module.End.mul_apply]
end Ambient

/-- The concrete natural S3-module has dimension two. -/
lemma natural_finrank : Module.finrank F (BinaryPermutation.core (Fin 3)) = 2 := by
  simpa using BinaryPermutation.finrank_core (Fin 3)

section Product
variable (ρ : Representation F (K × S₃) V)

/-- The S3 restriction of a representation of the direct product. -/
@[expose] def rightAction : Representation F S₃ V := ρ.comp (MonoidHom.inr K S₃)
/-- The K restriction of a representation of the direct product. -/
@[expose] def leftAction : Representation F K V := ρ.comp (MonoidHom.inl K S₃)

lemma product_commute (k : K) (g : S₃) (v : V) :
    leftAction ρ k (rightAction ρ g v) = rightAction ρ g (leftAction ρ k v) := by
  change (ρ (k,1) * ρ (1,g)) v = (ρ (1,g) * ρ (k,1)) v
  simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

/-- The multiplicity module for a binary representation of K × S3. -/
@[expose] def productMultiplicity : Representation F K (multiplicitySpace (rightAction ρ)) :=
  multiplicity (rightAction ρ) (leftAction ρ) (product_commute ρ)

/-- The actual tensor equivalence, assuming the normal cubic subgroup has zero fixed space. -/
noncomputable def productTensorEquiv
    (h : Representation.BinaryOffender.fixedSpace (rightAction ρ)
      (alternatingGroup (Fin 3)) = ⊥) :
    multiplicitySpace (rightAction ρ) ⊗[F] BinaryPermutation.core (Fin 3) ≃ₗ[F] V :=
  tensorEquiv (rightAction ρ) ((fixedFree_iff_fixedSpace_eq_bot (rightAction ρ)).mpr h)

lemma productTensorEquiv_equivariant
    (h : Representation.BinaryOffender.fixedSpace (rightAction ρ)
      (alternatingGroup (Fin 3)) = ⊥)
    (g : K × S₃) (z : multiplicitySpace (rightAction ρ) ⊗[F] BinaryPermutation.core (Fin 3)) :
    productTensorEquiv ρ h
      (tensorRepresentation (rightAction ρ) (leftAction ρ) (product_commute ρ) g z) =
      ρ g (productTensorEquiv ρ h z) := by
  change tensorEquiv (rightAction ρ) _
    (tensorRepresentation (rightAction ρ) (leftAction ρ) (product_commute ρ) g z) = _
  rw [tensorEquiv_equivariant]
  change (ρ (g.1,1) * ρ (1,g.2)) _ = _
  simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, Prod.eta]
  rfl

/-- Restriction to K consists of two copies of the constructed multiplicity module. -/
noncomputable def productPairEquiv
    (h : Representation.BinaryOffender.fixedSpace (rightAction ρ)
      (alternatingGroup (Fin 3)) = ⊥) :
    (multiplicitySpace (rightAction ρ) × multiplicitySpace (rightAction ρ)) ≃ₗ[F] V :=
  pairEquiv (rightAction ρ) ((fixedFree_iff_fixedSpace_eq_bot (rightAction ρ)).mpr h)

lemma productPairEquiv_equivariant
    (h : Representation.BinaryOffender.fixedSpace (rightAction ρ)
      (alternatingGroup (Fin 3)) = ⊥) (k : K) (x : multiplicitySpace (rightAction ρ) × multiplicitySpace (rightAction ρ)) :
    productPairEquiv ρ h (productMultiplicity ρ k x.1, productMultiplicity ρ k x.2) =
      ρ (k,1) (productPairEquiv ρ h x) :=
  pairEquiv_equivariant (rightAction ρ) (leftAction ρ) (product_commute ρ) _ k x
end Product

end InvertedCubicTensor
