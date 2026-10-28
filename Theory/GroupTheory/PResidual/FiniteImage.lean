module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Images of prime residuals in finite groups

The quotient by the p-residual of a finite group embeds into the finite
product of all its p-group quotients, so it is itself a p-group. Taking the
image of this quotient proves that surjections preserve the residual.
Restricting any homomorphism to a subgroup then transports the embedded
residual and its commutators without any ambient normality assumption.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Notation 13.2.1 and Lemma 13.2.2(4),
printed pp.877–878. The image of `O²(M₁)` must be computed as the residual
of the image stabilizer; it is not the larger intersection in B.3.4.
-/

public section

private theorem isPGroup_pi_of_finite {p : ℕ} {ι : Type*} [Finite ι]
    {K : ι → Type*} [∀ i, Group (K i)] (h : ∀ i, IsPGroup p (K i)) :
    IsPGroup p (∀ i, K i) := by
  classical
  let _ := Fintype.ofFinite ι
  intro x
  choose n hn using fun i => h i (x i)
  refine ⟨∑ i, n i, ?_⟩
  funext i
  apply orderOf_dvd_iff_pow_eq_one.mp
  exact (orderOf_dvd_of_pow_eq_one (hn i)).trans
    (pow_dvd_pow p (Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
      (Finset.mem_univ i)))

namespace Subgroup

variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- The quotient of a finite group by its p-residual is a p-group. -/
theorem isPGroup_quotient_pResidual (p : ℕ) : IsPGroup p (G ⧸ pResidual p G) := by
  classical
  let _ : Finite (Subgroup G) :=
    Finite.of_injective (fun N : Subgroup G => (N : Set G)) SetLike.coe_injective
  let S := {N : Subgroup G // ∃ hN : N.Normal,
    @IsPGroup p (G ⧸ N) (@QuotientGroup.Quotient.group G _ N hN)}
  let _ (N : S) : N.val.Normal := N.property.choose
  let q : G →* ((N : S) → G ⧸ N.val) :=
    MonoidHom.pi fun N => QuotientGroup.mk' N.val
  have hp : IsPGroup p ((N : S) → G ⧸ N.val) :=
    isPGroup_pi_of_finite fun N => N.property.choose_spec
  have hk : q.ker = pResidual p G := by
    ext x
    rw [MonoidHom.mem_ker, funext_iff]
    change (∀ N : S, QuotientGroup.mk' N.val x = 1) ↔ x ∈ pResidual p G
    simp only [pResidual, mem_sInf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h N hN => h ⟨N, hN⟩, fun h N => h N.val N.property⟩
  have hker : IsPGroup p (G ⧸ q.ker) :=
    (hp.to_subgroup q.range).of_equiv (QuotientGroup.quotientKerEquivRange q).symm
  exact hker.of_equiv (QuotientGroup.quotientMulEquivOfEq hk)

/-- A surjection from a finite group preserves the p-residual. -/
theorem map_pResidual_of_surjective (p : ℕ) (f : G →* H)
    (hf : Function.Surjective f) : (pResidual p G).map f = pResidual p H := by
  apply le_antisymm (map_pResidual_le p f)
  let N := (pResidual p G).map f
  let _ : N.Normal := Normal.map inferInstance f hf
  have hle : pResidual p G ≤ N.comap f := le_comap_map f _
  have hsurj := QuotientGroup.map_surjective_of_surjective (pResidual p G) N f
    (QuotientGroup.mk_surjective.comp hf) hle
  exact sInf_le ⟨inferInstance, (isPGroup_quotient_pResidual p).of_surjective
    (QuotientGroup.map (pResidual p G) N f hle) hsurj⟩

/-- The image of an embedded residual is the embedded residual of the image.
The homomorphism need not be surjective on the ambient group. -/
theorem map_embedded_pResidual (p : ℕ) (M : Subgroup G) (f : G →* H) :
    ((pResidual p M).map M.subtype).map f =
      (pResidual p (M.map f)).map (M.map f).subtype := by
  calc
    _ = ((pResidual p M).map (f.subgroupMap M)).map (M.map f).subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by
      rw [map_pResidual_of_surjective p (f.subgroupMap M) (f.subgroupMap_surjective M)]

/-- Commutators with embedded residuals transport through arbitrary group
homomorphisms. No normality in the ambient groups is required. -/
theorem map_commutator_embedded_pResidual (p : ℕ) (M J : Subgroup G) (f : G →* H) :
    (⁅(pResidual p M).map M.subtype, J⁆).map f =
      ⁅(pResidual p (M.map f)).map (M.map f).subtype, J.map f⁆ := by
  rw [map_commutator, map_embedded_pResidual]

end Subgroup

end
