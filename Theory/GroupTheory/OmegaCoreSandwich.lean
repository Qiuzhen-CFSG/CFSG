module
public import Stellmacher.OmegaOneCenterMap
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Identifying a core from ordinary and modulo centralizers

For Z = Ω₁Z(Q), the preimage F of Ω₁Z(Q/Z) lies in Q and satisfies
[F,Q] ≤ Z. Suppose N ≤ F ≤ Q ≤ C. The bound C_C(N) ≤ Z₀ puts Z in Z₀;
if every element of C centralizing N modulo Z₀ lies in N, then Q = N.
The proof uses commutators directly, so Z₀ need not be normal in the
ambient group before the equality is established.

Source application: Aschbacher--Smith, 14.6.9(m)--(n), printed p.1027.
Here N is the product of the two residual point-centralizer cores.
-/

public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The preimage of the quotient omega-center lies in the original subgroup
and centralizes it modulo the kernel. -/
theorem omega_center_preimage_le_and_commutator_le
    (Q Z : Subgroup G) [Z.Normal] (hZQ : Z ≤ Q) :
    let F := (omegaOneCenterAmbient (Q.map (QuotientGroup.mk' Z))).comap
      (QuotientGroup.mk' Z)
    F ≤ Q ∧ ⁅F,Q⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  let F := (omegaOneCenterAmbient (Q.map q)).comap q
  change F ≤ Q ∧ ⁅F,Q⁆ ≤ Z
  constructor
  · have homega : omegaOneCenterAmbient (Q.map q) ≤ Q.map q :=
      fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    have hh := comap_mono (f := q) homega
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hZQ] at hh
    exact hh
  · apply commutator_le.mpr
    intro f hf a ha
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅f,a⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hf).2.2
      (q a) (mem_map_of_mem q ha)).symm

/-- The ordinary and modulo centralizer bounds identify a subgroup between
an omega-center preimage and its original two-core. -/
theorem eq_of_omega_center_preimage_centralizer_bounds
    (Q C N Z₀ : Subgroup G) [(omegaOneCenterAmbient Q).Normal]
    (hQC : Q ≤ C)
    (hNF : N ≤ (omegaOneCenterAmbient (Q.map
      (QuotientGroup.mk' (omegaOneCenterAmbient Q)))).comap
      (QuotientGroup.mk' (omegaOneCenterAmbient Q)))
    (hcent : C ⊓ centralizer (N : Set G) ≤ Z₀)
    (hmod : ∀ c ∈ C, (∀ n ∈ N, ⁅n,c⁆ ∈ Z₀) → c ∈ N) :
    Q = N := by
  let Z := omegaOneCenterAmbient Q
  have hZQ : Z ≤ Q := fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  obtain ⟨hFQ,hFcomm⟩ := omega_center_preimage_le_and_commutator_le Q Z hZQ
  have hNQ := hNF.trans hFQ
  have hZZ₀ : Z ≤ Z₀ := by
    intro z hz
    apply hcent
    refine ⟨hQC (hZQ hz),?_⟩
    exact fun n hn => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 n (hNQ hn)
  apply le_antisymm _ hNQ
  intro c hc
  apply hmod c (hQC hc)
  intro n hn
  exact hZZ₀ (hFcomm (commutator_mem_commutator (hNF hn) hc))
end Theory.GroupTheory
