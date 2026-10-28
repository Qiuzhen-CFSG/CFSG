module

public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction
public import Theory.FieldTheory.QuadraticFrobeniusTrace
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Involutory coefficient cocycles in the actual G₂ group

Every cocycle for a nonidentity coefficient involution over a finite field of
characteristic two is a coboundary in the split-octonion automorphism group.

The map xU ↦ gσ(x)U is an involution on the odd set of cosets of the six-root
subgroup U. A fixed coset conjugates the cocycle into U. Its triangular root
coordinates are then removed from last to first: at each step the cocycle
equation makes the last remaining coordinate σ-fixed, and the quadratic trace
provides the next root conjugator. All conjugators belong to the actual group
of multiplication-preserving linear automorphisms of the split octonions.

This discharges the cocycle premise in the G₂ case of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.4(4), printed p.1171,
and the G₂(4) discussion on printed p.1191. The root-coordinate laws are from
the licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.EvenFieldFixedResidual.Cocycle
open LieAutomorphismExtensions LieParabolicSetup
variable {F : Type*} [Field F]

private theorem bound_mul (n : ℕ) (t u : Fin 6 → F)
    (ht : ∀ i : Fin 6, n ≤ i.val → t i = 0)
    (hu : ∀ i : Fin 6, n ≤ i.val → u i = 0) :
    ∀ i : Fin 6, n ≤ i.val → unipotentProductParameters t u i = 0 := by
  intro i hi
  have ht' : ∀ j : Fin 6, i.val ≤ j.val → t j = 0 :=
    fun j hij => ht j (hi.trans hij)
  have hu' : ∀ j : Fin 6, i.val ≤ j.val → u j = 0 :=
    fun j hij => hu j (hi.trans hij)
  fin_cases i <;> simp (disch := decide) [unipotentProductParameters, ht', hu']

private theorem bound_inv (n : ℕ) (t : Fin 6 → F)
    (ht : ∀ i : Fin 6, n ≤ i.val → t i = 0) :
    ∀ i : Fin 6, n ≤ i.val → unipotentInverseParameters t i = 0 := by
  intro i hi
  have ht' : ∀ j : Fin 6, i.val ≤ j.val → t j = 0 :=
    fun j hij => ht j (hi.trans hij)
  fin_cases i <;> simp (disch := decide) [unipotentInverseParameters, ht']

private theorem top_mul (n : Fin 6) (t u : Fin 6 → F)
    (ht : ∀ i : Fin 6, n.val < i.val → t i = 0) :
    unipotentProductParameters t u n = u n + t n := by
  fin_cases n <;> simp (disch := decide) [unipotentProductParameters, ht]

private theorem top_inv (n : Fin 6) (t : Fin 6 → F)
    (ht : ∀ i : Fin 6, n.val < i.val → t i = 0) :
    unipotentInverseParameters t n = -t n := by
  fin_cases n <;> simp (disch := decide) [unipotentInverseParameters, ht]

private theorem field_product (σ : F ≃+* F) (t : Fin 6 → F) :
    fieldAction σ (unipotentProduct t) = unipotentProduct (σ ∘ t) :=
  long_field_unipotentProduct σ t

private theorem twist_cocycle {G : Type*} [Group G] (σ : MulAut G)
    (hσ : Function.Involutive σ) (g c : G) (hg : g * σ g = 1) :
    (c⁻¹ * g * σ c) * σ (c⁻¹ * g * σ c) = 1 := by
  simp only [map_mul, map_inv, hσ c]
  calc
    _ = c⁻¹ * (g * σ g) * c := by group
    _ = 1 := by rw [hg]; group

private theorem solve_bounded [CharP F 2] (σ : F ≃+* F)
    (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (hact : Function.Involutive (fieldAction σ)) (n : ℕ) (hn : n ≤ 6)
    (t : Fin 6 → F) (ht : ∀ i : Fin 6, n ≤ i.val → t i = 0)
    (hg : unipotentProduct t * fieldAction σ (unipotentProduct t) = 1) :
    ∃ c : Model F, unipotentProduct t = c * fieldAction σ c⁻¹ := by
  induction n generalizing t with
  | zero =>
    have ht0 : t = 0 := funext (fun i => ht i (Nat.zero_le _))
    exact ⟨1, by simp [ht0]⟩
  | succ n ih =>
    let k : Fin 6 := ⟨n, by omega⟩
    have hk : k.val = n := rfl
    have ht' : ∀ i : Fin 6, k.val < i.val → t i = 0 := by
      intro i hi
      exact ht i (by omega)
    have heq : unipotentProductParameters t (σ ∘ t) = 0 := by
      apply unipotentProduct_injective
      simpa only [← unipotentProduct_mul, ← field_product, unipotentProduct_zero] using hg
    have hfix : σ (t k) = t k := by
      have h := congrFun heq k
      rw [top_mul k t (σ ∘ t) ht'] at h
      exact CharTwo.add_eq_zero.mp h
    obtain ⟨a, ha⟩ := InvolutiveTrace.exists_trace σ hσ hne (t k) hfix
    change a + σ a = t k at ha
    let s : Fin 6 → F := fun j => if j = k then a else 0
    have hs : ∀ i : Fin 6, k.val < i.val → s i = 0 := by
      intro i hi
      have hik : i ≠ k := fun h => by subst i; omega
      simp [s, hik]
    have hsi : ∀ i : Fin 6, k.val < i.val → unipotentInverseParameters s i = 0 :=
      fun i hi => bound_inv (n + 1) s (fun j hj => hs j (by omega)) i (by omega)
    have hss : ∀ i : Fin 6, k.val < i.val → (σ ∘ s) i = 0 := by
      intro i hi
      simp [hs i hi]
    let v := unipotentProductParameters (unipotentInverseParameters s) t
    have hv : ∀ i : Fin 6, k.val < i.val → v i = 0 :=
      fun i hi => bound_mul (n + 1) _ _ (fun j hj => hsi j (by omega))
        (fun j hj => ht' j (by omega)) i (by omega)
    let u := unipotentProductParameters v (σ ∘ s)
    have hu' : ∀ i : Fin 6, k.val < i.val → u i = 0 :=
      fun i hi => bound_mul (n + 1) _ _ (fun j hj => hv j (by omega))
        (fun j hj => hss j (by omega)) i (by omega)
    have huk : u k = 0 := by
      rw [show u k = _ from top_mul k v (σ ∘ s) hv]
      rw [show v k = _ from top_mul k (unipotentInverseParameters s) t hsi,
        top_inv k s hs]
      have hsk : s k = a := by simp [s]
      simp only [Function.comp_apply, hsk]
      rw [← ha, CharTwo.neg_eq]
      have hz : a + a = 0 := CharTwo.add_self_eq_zero _
      have hz' : σ a + σ a = 0 := CharTwo.add_self_eq_zero _
      linear_combination hz + hz'
    have hu : ∀ i : Fin 6, n ≤ i.val → u i = 0 := by
      intro i hi
      by_cases he : i = k
      · simpa [he] using huk
      · exact hu' i (by have hne : i.val ≠ k.val := fun h => he (Fin.ext h); omega)
    have hprod : unipotentProduct u =
        (unipotentProduct s)⁻¹ * unipotentProduct t * fieldAction σ (unipotentProduct s) := by
      rw [field_product, unipotentProduct_inv, unipotentProduct_mul, unipotentProduct_mul]
    obtain ⟨c, hc⟩ := ih (by omega) u hu (by
      rw [hprod]
      exact twist_cocycle (fieldAction σ) hact _ _ hg)
    refine ⟨unipotentProduct s * c, ?_⟩
    rw [hprod] at hc
    calc
      unipotentProduct t = unipotentProduct s *
          ((unipotentProduct s)⁻¹ * unipotentProduct t * fieldAction σ (unipotentProduct s)) *
          (fieldAction σ (unipotentProduct s))⁻¹ := by group
      _ = (unipotentProduct s * c) * fieldAction σ (unipotentProduct s * c)⁻¹ := by
        rw [hc]
        simp only [map_inv, map_mul, mul_inv_rev]
        group

end Atlas.G2.EvenFieldFixedResidual.Cocycle
namespace Atlas.G2.EvenFieldFixedResidual.Cocycle
open LieAutomorphismExtensions LieParabolicSetup

private theorem exists_twist_mem_of_odd_index {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hodd : Odd H.index) (σ : MulAut G)
    (hσ : Function.Involutive σ) (hH : ∀ x ∈ H, σ x ∈ H)
    (g : G) (hg : g * σ g = 1) : ∃ c : G, c⁻¹ * g * σ c ∈ H := by
  classical
  let f : G ⧸ H → G ⧸ H := Quotient.map' (fun x => g * σ x) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := hH _ (QuotientGroup.leftRel_apply.mp hab)
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, map_inv] using h)
  have hf : Function.Involutive f := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro a
    change (↑(g * σ (g * σ a)) : G ⧸ H) = ↑a
    rw [map_mul, hσ a, ← mul_assoc, hg, one_mul]
  let e := hf.toPerm f
  have he : e ^ (2 ^ 1) = 1 := by
    apply Equiv.ext
    intro x
    change f (f x) = x
    exact hf x
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : ¬2 ∣ Fintype.card (G ⧸ H) := by
    simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hodd.not_two_dvd_nat
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard he
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨c, ?_⟩
  change (↑(g * σ c) : G ⧸ H) = ↑c at hx
  simpa only [mul_assoc] using QuotientGroup.eq.mp hx.symm


end Atlas.G2.EvenFieldFixedResidual.Cocycle
namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions LieParabolicSetup Cocycle
variable {F : Type*} [Field F] [CharP F 2]

/-- Every coefficient-involution cocycle in the positive-root subgroup is
an actual octonion-automorphism coboundary. -/
theorem unipotent_cocycle_eq_coboundary (σ : F ≃+* F) (hs : orderOf σ = 2)
    (g : Model F) (hU : g ∈ unipotent) (hg : g * fieldAction σ g = 1) :
    ∃ c : Model F, g = c * fieldAction σ c⁻¹ := by
  have hs2 : σ ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one σ
  have hσ : Function.Involutive σ := by
    intro x
    change (σ ^ 2) x = x
    rw [hs2]
    rfl
  have hact2 : fieldAction σ ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
  have hact : Function.Involutive (fieldAction σ) := by
    intro x
    change (fieldAction σ ^ 2) x = x
    rw [hact2]
    rfl
  have hne : ∃ x, σ x ≠ x := by
    by_contra! h
    have he : σ = 1 := RingEquiv.ext h
    rw [he, orderOf_one] at hs
    norm_num at hs
  rw [unipotent_eq_range] at hU
  obtain ⟨t, rfl⟩ := hU
  exact solve_bounded σ hσ hne hact 6 le_rfl t (fun i hi => by omega) hg

/-- An involutory coefficient cocycle in the full split-octonion group is a
coboundary in that same group. The finite odd-index coset action reduces to
the root-coordinate calculation above. -/
theorem cocycle_eq_coboundary [Finite F] (_hq : 2 < Nat.card F)
    (σ : F ≃+* F) (hs : orderOf σ = 2)
    (g : Model F) (hg : g * fieldAction σ g = 1) :
    ∃ c : Model F, g = c * fieldAction σ c⁻¹ := by
  have hs2 : σ ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one σ
  have hact2 : fieldAction σ ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
  have hact : Function.Involutive (fieldAction σ) := by
    intro x
    change (fieldAction σ ^ 2) x = x
    rw [hact2]
    rfl
  have hU : ∀ x ∈ unipotent, fieldAction σ x ∈ (unipotent : Subgroup (Model F)) := by
    intro x hx
    rw [unipotent_eq_range] at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    exact ⟨σ ∘ t, (long_field_unipotentProduct σ t).symm⟩
  obtain ⟨b, hb⟩ := exists_twist_mem_of_odd_index unipotent unipotent_index_odd
    (fieldAction σ) hact hU g hg
  obtain ⟨c, hc⟩ := unipotent_cocycle_eq_coboundary σ hs _ hb
    (twist_cocycle (fieldAction σ) hact g b hg)
  refine ⟨b * c, ?_⟩
  calc
    g = b * (b⁻¹ * g * fieldAction σ b) * (fieldAction σ b)⁻¹ := by group
    _ = (b * c) * fieldAction σ (b * c)⁻¹ := by
      rw [hc]
      simp only [map_inv, map_mul, mul_inv_rev]
      group

end Atlas.G2.EvenFieldFixedResidual
