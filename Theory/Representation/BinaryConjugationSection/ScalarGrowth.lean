module
public import Theory.Representation.BinaryConjugationSection.GeneratedImages
public import Theory.Representation.BinaryConjugationSection.DisplacementBound

/-!
# Scalar-image growth and exact kernels

In an irreducible binary section, equal images of nested subgroups would
be invariant under the two actor groups that generate the whole actor.
A proper nonzero smaller image therefore grows strictly. If the scalar
dimension can grow by at most one, the bound is attained and the original
subgroup index forces the exact intersection with the section kernel.

Source application: Aschbacher--Smith, The Classification of Quasithin
Groups, 13.8.30, printed p.964, for the successive tensor spans.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W F : Type*} [Group G] [Finite G] [Field F]
  [AddCommGroup W] [Module (ZMod 2) W] [Module F W]
  {L U N : Subgroup G} {ρ : Representation (ZMod 2) L W}

/-- Generators force one step of scalar-image growth. Saturating the original
index bound identifies the full intersection with the section kernel. -/
theorem scalar_growth_and_kernel [IsIrreducible ρ]
    (q : BinaryConjugationSection L U N ρ)
    (D : Subgroup G) (hDL : D ≤ L) (χ : D →* Fˣ) (hχ : Function.Surjective χ)
    (hscalar : ∀ x w, ρ (inclusion hDL x) w = (χ x : F) • w)
    (B S V : Subgroup G) (hBS : B ≤ S) (hSU : S ≤ U)
    (hVS : V ≤ S) (hVN : V ≤ N)
    (hDB : D ≤ normalizer B) (hDS : D ≤ normalizer S)
    (J K : Subgroup L) (hgen : J ⊔ K = ⊤)
    (hJB : ∀ j : J, ((j : L) : G) ∈ normalizer B)
    (hKS : ∀ k : K, ((k : L) : G) ∈ normalizer S)
    (n : ℕ) (hn : 0 < n) (hF : 1 < Nat.card F)
    (hB : Module.finrank F (q.scalarImage D hDL χ hχ hscalar B hDB) = n)
    (hW : Module.finrank F W ≠ n)
    (hindex : V.relIndex S = Nat.card F ^ (n+1)) :
    Module.finrank F (q.scalarImage D hDL χ hχ hscalar S hDS) = n+1 ∧
      S ⊓ N = V := by
  let : Finite W := Finite.of_surjective (fun x : U => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  let B' := q.scalarImage D hDL χ hχ hscalar B hDB
  let S' := q.scalarImage D hDL χ hχ hscalar S hDS
  have hle : B' ≤ S' := q.imageSpace_mono hBS
  have hne : B' ≠ S' := by
    intro he
    have himage : q.imageSpace B = q.imageSpace S := by
      ext w
      exact (show w ∈ B' ↔ w ∈ S' from he ▸ Iff.rfl)
    have hnB : q.imageSpace S ≠ ⊥ := by
      intro hb
      have hzero : B' = ⊥ := by
        ext w
        change w ∈ q.imageSpace B ↔ w = 0
        rw [himage,hb]
        rfl
      change Module.finrank F B' = n at hB
      rw [hzero,finrank_bot] at hB
      omega
    have ht := q.image_eq_top_of_generators S B J K hgen hJB hKS himage hnB
    have htop : B' = ⊤ := by
      ext w
      change w ∈ q.imageSpace B ↔ True
      rw [himage,ht]
      rfl
    apply hW
    change Module.finrank F B' = n at hB
    rw [htop] at hB
    simpa using hB
  have hlo := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have hc := q.imageSpace_card_le_relative_index S V hVN
  change Nat.card S' ≤ V.relIndex S at hc
  rw [Module.natCard_eq_pow_finrank (K := F),hindex] at hc
  have hhi := (Nat.pow_le_pow_iff_right hF).mp hc
  have hd : Module.finrank F S' = n+1 := by
    change Module.finrank F B' = n at hB
    omega
  refine ⟨hd,?_⟩
  have hcard : Nat.card (q.imageSpace S) = Nat.card F ^ (n+1) := by
    change Nat.card S' = _
    rw [Module.natCard_eq_pow_finrank (K := F),hd]
  have hNS : (S ⊓ N).relIndex S = V.relIndex S := by
    rw [inf_relIndex_left]
    exact (q.imageSpace_card_eq_relIndex S hSU).symm.trans (hcard.trans hindex.symm)
  have hVNS : V ≤ S ⊓ N := le_inf hVS hVN
  have he := relIndex_mul_relIndex V (S ⊓ N) S hVNS inf_le_left
  rw [hNS] at he
  have hi : V.relIndex (S ⊓ N) = 1 := by
    have hp : V.relIndex S ≠ 0 := (V.subgroupOf S).index_ne_zero_of_finite
    exact (mul_left_eq_self₀.mp he).resolve_right hp
  exact le_antisymm (relIndex_eq_one.mp hi) hVNS
end Representation.BinaryConjugationSection
