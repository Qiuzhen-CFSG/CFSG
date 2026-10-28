module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The weak-closure contradiction in 12.6.28

For a noncentralizing subgroup A of a conjugate W of V, 12.6.27 makes W
and V disjoint. Their normalizer intersection therefore centralizes A.
The codimension-two centralizer control gives the fixed-space rigidity
condition on A. Intrinsic 12.6.28(1) excludes corank zero. At corank one,
12.6.28(2) produces three larger fixed spaces over one corank-three subgroup.
The nonsingular-centralizer theorem makes their preimages singular, contrary
to the two-extension property of a singular 2-space in the orthogonal 6-space.

The intrinsic fixed-space facts are explicitly stated in their pullback form
on the original actor. Their derivation from the faithful automizer calculations
is still required for the source theorem. The earlier centralizer and disjointness
inputs are likewise explicit. The last step uses the actual E.3 weak closures
and the extended-natural minimum; it does not assume that this minimum is finite.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 12.6.28(3--4), printed pp.834--835.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
open ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-space condition written on the original actor, before taking
its faithful image. The corank is the binary logarithm of relative index. -/
def CentralizerRigidity (V A : Subgroup G) (k : ℕ) : Prop :=
  ∀ B ≤ A, subgroupCorank A B < k →
    V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G)

private theorem corank_add {W A B : Subgroup G} [IsElementaryAbelian 2 W]
    (hBA : B ≤ A) (hAW : A ≤ W) :
    subgroupCorank W B = subgroupCorank A B + subgroupCorank W A := by
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAW
  have hp (T U : Subgroup G) [IsElementaryAbelian 2 T] :
      U.relIndex T = 2 ^ subgroupCorank T U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank T U
  have hi := Subgroup.relIndex_mul_relIndex B A W hBA hAW
  rw [hp A B, hp W A, hp W B, ← pow_add] at hi
  exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) hi).symm

/-- The source's W₀/W₁ argument from its intrinsic fixed-space and polar-space
inputs. The predicates `singular g E` refer to the quadratic form on Vᵍ.
`no_three` and `three_extensions` are the pullbacks of 12.6.28(1--2) along
A → Aut_A(V); they do not assume weak closure. `disjoint` is 12.6.27,
`control` is 12.6.20(3), and `singular_of_escape` follows from 12.6.2.

This is a conditional source step: transport of the intrinsic module
calculations to the stated pullback inputs remains a separate obligation. -/
theorem small_corank_conjugate_centralizes
    (V T : Subgroup G) [IsElementaryAbelian 2 V]
    (hTN : T ≤ normalizer (V : Set G))
    (singular : G → Subgroup G → Prop)
    (disjoint : ∀ g : G, ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥)
    (control : ∀ (g : G) (B : Subgroup G), B ≤ V.map (MulAut.conj g).toMonoidHom →
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B < 3 →
      centralizer (B : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (no_three : ∀ A : Subgroup G, A ≤ normalizer (V : Set G) →
      IsElementaryAbelian 2 A → CentralizerRigidity V A 3 → A ≤ centralizer (V : Set G))
    (three_extensions : ∀ A : Subgroup G, A ≤ normalizer (V : Set G) →
      IsElementaryAbelian 2 A → ¬ A ≤ centralizer (V : Set G) →
      CentralizerRigidity V A 2 →
      ∃ D ≤ A, subgroupCorank A D = 3 ∧
        ∃ E : Fin 3 → Subgroup G, Function.Injective E ∧
          ∀ i, D ≤ E i ∧ E i ≤ A ∧ subgroupCorank (E i) D = 1 ∧
            V ⊓ centralizer (A : Set G) < V ⊓ centralizer (E i : Set G))
    (singular_of_escape : ∀ (g : G) (E : Subgroup G),
      E ≤ V.map (MulAut.conj g).toMonoidHom →
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) E = 3 →
      ¬ centralizer (E : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      singular g E)
    (two_extensions : ∀ (g : G) (D : Subgroup G),
      D ≤ V.map (MulAut.conj g).toMonoidHom →
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) D = 4 →
      ∀ E : Fin 3 → Subgroup G,
        (∀ i, D ≤ E i ∧ E i ≤ V.map (MulAut.conj g).toMonoidHom ∧
          subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (E i) = 3 ∧ singular g (E i)) →
        ¬ Function.Injective E)
    (g : G) (A : Subgroup G) (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAT : A ≤ T) (hsmall : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1) :
    A ≤ centralizer (V : Set G) := by
  by_contra hnon
  let W := V.map (MulAut.conj g).toMonoidHom
  change A ≤ W at hAW
  change subgroupCorank W A ≤ 1 at hsmall
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAW
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hTN
  have hVW : V ⊓ W = ⊥ := disjoint g (by
    intro hc
    apply hnon
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact le_antisymm ((commutator_mono le_rfl hAW).trans hc.le) bot_le)
  have hcentral : V ⊓ normalizer (W : Set G) ≤ centralizer (A : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_antisymm _ bot_le
    have hv : ⁅V ⊓ normalizer (W : Set G), A⁆ ≤ V :=
      (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hAN)
    have hw : ⁅V ⊓ normalizer (W : Set G), A⁆ ≤ W :=
      (commutator_mono le_rfl hAW).trans
        (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    exact (le_inf hv hw).trans hVW.le
  have hrigid (k : ℕ) (hk : k + subgroupCorank W A ≤ 3) : CentralizerRigidity V A k := by
    intro B hBA hB
    have hWB : subgroupCorank W B < 3 := by
      rw [corank_add hBA hAW]
      omega
    apply le_antisymm
    · exact (le_inf inf_le_left ((inf_le_right : V ⊓ centralizer (B : Set G) ≤ _).trans
        (control g B (hBA.trans hAW) hWB))).trans (le_inf inf_le_left hcentral)
    · exact inf_le_inf_left V (Subgroup.centralizer_le hBA)
  have hcorank : subgroupCorank W A = 1 := by
    by_contra he
    have hz : subgroupCorank W A = 0 := by omega
    exact hnon (no_three A hAN inferInstance (hrigid 3 (by omega)))
  obtain ⟨D, hDA, hD, E, hE, hEs⟩ :=
    three_extensions A hAN inferInstance hnon (hrigid 2 (by omega))
  have hWD : subgroupCorank W D = 4 := by rw [corank_add hDA hAW, hD, hcorank]
  apply two_extensions g D (hDA.trans hAW) hWD E _ hE
  intro i
  obtain ⟨hDE, hEA, hED, hgrow⟩ := hEs i
  have hEW : E i ≤ W := hEA.trans hAW
  have hWE : subgroupCorank W (E i) = 3 := by
    have hh := corank_add hDE hEW
    omega
  refine ⟨hDE, hEW, hWE, singular_of_escape g (E i) hEW hWE ?_⟩
  intro hbad
  apply not_le_of_gt hgrow
  exact le_inf inf_le_left
    ((le_inf inf_le_left ((inf_le_right : V ⊓ centralizer (E i : Set G) ≤ _).trans hbad)).trans hcentral)

omit [Finite G] in
/-- The actual indexed closures, and the extended-natural minimum w(G,V).
No existence of a finite minimizing offender is assumed. -/
theorem weak_closures_and_globalW_of_small_corank
    (V T : Subgroup G)
    (hsmall : ∀ (g : G) (A : Subgroup G), A ≤ V.map (MulAut.conj g).toMonoidHom →
      A ≤ T → subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1 →
      A ≤ centralizer (V : Set G)) :
    indexedWeakClosure V T 0 ≤ centralizer (V : Set G) ∧
      indexedWeakClosure V T 1 ≤ centralizer (V : Set G) ∧ 1 < globalW V T := by
  have hc (i : ℕ) (hi : i ≤ 1) : indexedWeakClosure V T i ≤ centralizer (V : Set G) := by
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    rintro A ⟨⟨g, hA, he⟩, hAT⟩
    apply hsmall g A hA hAT
    simp only [subgroupCorank, he, Nat.log_pow (by decide : 1 < 2)]
    exact hi
  refine ⟨hc 0 (by decide), hc 1 le_rfl, ?_⟩
  have hbound : (2 : ℕ∞) ≤ globalW V T := by
    apply le_iInf
    intro j
    apply le_iInf
    intro hj
    have hlarge : 2 ≤ j := by
      by_contra hn
      exact hj (le_inf (indexedWeakClosure_le V T j) (hc j (by omega)))
    exact_mod_cast hlarge
  exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) hbound
end CFSG.Quasithin.Chapter12.Section06.LocalAlternatives

namespace CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
open Subgroup
variable {G : Type*} [Group G]

/-- A centralizer that escapes the local normalizer forces the entire
subspace to be singular. In the source q is the transported quadratic form,
and `hpoint` is the conjugate of Theorem 12.6.2. This step requires no
assumption on the subspace dimension. -/
theorem singular_of_nonsingular_centralizer_control
    (W E : Subgroup G) (hEW : E ≤ W) (q : W → ZMod 2)
    (hpoint : ∀ w : W, q w ≠ 0 →
      centralizer ({(w : G)} : Set G) ≤ normalizer (W : Set G))
    (hescape : ¬ centralizer (E : Set G) ≤ normalizer (W : Set G)) :
    ∀ e : E, q ⟨e.val, hEW e.property⟩ = 0 := by
  intro e
  by_contra hn
  apply hescape
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr e.property)).trans
    (hpoint ⟨e.val, hEW e.property⟩ hn)
end CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
