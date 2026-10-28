module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Basic
public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Residuals of the marked internal S₃ factors

The compatible product map proves that the factors commute, generate H,
and are normal in H. Their embedded two-residuals have order three, are
pairwise distinct, and are subnormal in the star group through H.

If T_v* is transitive on these factors, a T_v*-invariant subgroup equal to
one factor residual forces a single factor. It then equals X = O²(H).
This is the final group-theoretic assembly step in 13.6.13; transitivity
and factor identification remain explicit inputs here.

The coordinate proofs follow the internal-product argument in
ChapterB/Section01/SolvableStructure/OffenderProducts/Internal.lean,
specialized to the actual star subgroups rather than an FF representation.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
variable {G : Type*} [Group G] {z v : G} {X : Subgroup (Gstar z v)}
namespace NormalS3Decomposition
variable (d : NormalS3Decomposition z v X)

/-- The coordinate-compatible internal product, viewed in G_v*. -/
noncomputable def factorProductMap : (∀ i, d.factor i) →* Gstar z v :=
  d.H.subtype.comp d.product.toMonoidHom

@[simp] theorem factorProductMap_single (i : Fin d.count) (a : d.factor i) :
    d.factorProductMap (Pi.mulSingle i a) = (a : Gstar z v) := d.product_single i a

theorem factorProductMap_injective : Function.Injective d.factorProductMap :=
  d.H.subtype_injective.comp d.product.injective

/-- Distinct internal factors commute in the original star group. -/
theorem factor_commute {i j : Fin d.count} (hij : i ≠ j)
    (a : d.factor i) (b : d.factor j) : Commute (a : Gstar z v) (b : Gstar z v) := by
  simpa only [d.factorProductMap_single] using
    (Pi.mulSingle_commute hij a b).map d.factorProductMap

/-- The actual factors generate H. -/
theorem iSup_factor : (⨆ i, d.factor i) = d.H := by
  apply le_antisymm (iSup_le d.factor_le)
  intro a ha
  let x := d.product.symm ⟨a, ha⟩
  have hc : Pairwise fun i j => ∀ (a : d.factor i) (b : d.factor j),
      Commute ((d.factor i).subtype a) ((d.factor j).subtype b) :=
    fun _ _ hij => d.factor_commute hij
  let f := MonoidHom.noncommPiCoprod (fun i => (d.factor i).subtype) hc
  have hf : f = d.factorProductMap := by
    apply MonoidHom.pi_ext
    intro i a
    simp only [f, MonoidHom.noncommPiCoprod_mulSingle,
      d.factorProductMap_single, Subgroup.subtype_apply]
  have hr : f.range = ⨆ i, d.factor i := by
    change (MonoidHom.noncommPiCoprod (fun i => (d.factor i).subtype) hc).range = _
    rw [MonoidHom.noncommPiCoprod_range]
    simp only [Subgroup.range_subtype]
  rw [← hr]
  refine ⟨x, ?_⟩
  rw [hf]
  exact congrArg Subtype.val (d.product.apply_symm_apply ⟨a, ha⟩)

/-- Distinct coordinate factors have trivial intersection. -/
theorem factor_disjoint {i j : Fin d.count} (hij : i ≠ j) :
    Disjoint (d.factor i) (d.factor j) := by
  rw [Subgroup.disjoint_def]
  intro a hai haj
  have he : Pi.mulSingle i (⟨a, hai⟩ : d.factor i) =
      Pi.mulSingle j (⟨a, haj⟩ : d.factor j) :=
    d.factorProductMap_injective
      ((d.factorProductMap_single i ⟨a, hai⟩).trans
        (d.factorProductMap_single j ⟨a, haj⟩).symm)
  have hi := congrFun he i
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at hi
  exact congrArg Subtype.val hi

private theorem factorProductMap_conj_single (x : ∀ i, d.factor i)
    (i : Fin d.count) (a : d.factor i) :
    d.factorProductMap x * (a : Gstar z v) * (d.factorProductMap x)⁻¹ =
      ((x i * a * (x i)⁻¹ : d.factor i) : Gstar z v) := by
  have he : x * Pi.mulSingle i a * x⁻¹ = Pi.mulSingle i (x i * a * (x i)⁻¹) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  simpa only [map_mul, map_inv, d.factorProductMap_single] using
    congrArg d.factorProductMap he

/-- Normality is relative to H, which can have permuted factors in G_v*. -/
theorem factor_normal_in_H (i : Fin d.count) : ((d.factor i).subgroupOf d.H).Normal := by
  refine ⟨fun a ha g => ?_⟩
  change (g : Gstar z v) * (a : Gstar z v) * (g : Gstar z v)⁻¹ ∈ d.factor i
  let x := d.product.symm g
  have hx : d.factorProductMap x = (g : Gstar z v) :=
    congrArg Subtype.val (d.product.apply_symm_apply g)
  rw [← hx, d.factorProductMap_conj_single x i ⟨a, ha⟩]
  exact Subtype.property _

/-- O²(H_i), with the original inclusion in G_v*. -/
abbrev factorResidual (i : Fin d.count) : Subgroup (Gstar z v) :=
  (pResidual 2 (d.factor i)).map (d.factor i).subtype

theorem factorResidual_card (i : Fin d.count) : Nat.card (d.factorResidual i) = 3 :=
  Theory.GroupTheory.NormalSymmetricThreeMarked.residual_card (d.factor i) (d.model i)

theorem factorResidual_le_X (i : Fin d.count) : d.factorResidual i ≤ X :=
  (embedded_pResidual_mono 2 (d.factor_le i)).trans_eq d.residual_eq

/-- Residuals of distinct factors remain distinguishable in the star group. -/
theorem factorResidual_injective : Function.Injective d.factorResidual := by
  intro i j he
  by_contra hij
  have hd : Disjoint (d.factorResidual i) (d.factorResidual j) :=
    (d.factor_disjoint hij).mono (map_subtype_le _) (map_subtype_le _)
  rw [he, disjoint_self] at hd
  have hc := d.factorResidual_card j
  rw [hd, Subgroup.card_bot] at hc
  omega

/-- The residual is subnormal via its normality in H and H's ambient normality. -/
theorem factorResidual_isSubnormal (i : Fin d.count) : (d.factorResidual i).IsSubnormal :=
  IsSubnormal.step _ d.H ((map_subtype_le _).trans (d.factor_le i)) d.normal.isSubnormal
    (normal_embedded_pResidual_subgroupOf 2 (d.factor_le i) (d.factor_normal_in_H i))

/-- The source transitivity statement, retaining the literal conjugating subgroup. -/
def FactorsTransitive (T : Subgroup G) : Prop :=
  ∀ i j : Fin d.count, ∃ t ∈ starImage z v (Tv T v),
    (d.factor i).map (MulAut.conj t).toMonoidHom = d.factor j

variable [Finite G]

/-- Factor transport also transports the embedded residuals. -/
theorem factorResidual_map_conj (i j : Fin d.count) (t : Gstar z v)
    (h : (d.factor i).map (MulAut.conj t).toMonoidHom = d.factor j) :
    (d.factorResidual i).map (MulAut.conj t).toMonoidHom = d.factorResidual j := by
  change ((pResidual 2 (d.factor i)).map (d.factor i).subtype).map _ = _
  rw [map_embedded_pResidual, h]

/-- Transitivity and invariance of one residual force exactly one factor. -/
theorem count_eq_one_of_transitive_invariant_residual (T : Subgroup G)
    (htrans : d.FactorsTransitive T) (B : Subgroup (Gstar z v))
    (hB : starImage z v (Tv T v) ≤ normalizer (B : Set _))
    (i : Fin d.count) (he : B = d.factorResidual i) : d.count = 1 := by
  have hi (j : Fin d.count) : i = j := by
    obtain ⟨t, ht, hmap⟩ := htrans i j
    apply d.factorResidual_injective
    have hb := mem_normalizer_iff_map_conj_eq.mp (hB ht)
    rw [he] at hb
    exact hb.symm.trans (d.factorResidual_map_conj i j t hmap)
  by_contra hcount
  have htwo : 2 ≤ d.count := by have := d.count_pos; omega
  have h01 := (hi ⟨0, by omega⟩).symm.trans (hi ⟨1, by omega⟩)
  have := congrArg Fin.val h01
  norm_num at this

omit [Finite G] in
/-- With one factor its residual is the specified X, by the compatible product. -/
theorem factorResidual_eq_X_of_count_eq_one (hcount : d.count = 1) (i : Fin d.count) :
    d.factorResidual i = X := by
  have hi (j : Fin d.count) : j = i := by
    apply Fin.ext
    have hj := j.isLt
    have hii := i.isLt
    omega
  have hf : d.factor i = d.H := by
    rw [← d.iSup_factor]
    apply le_antisymm (le_iSup d.factor i)
    exact iSup_le fun j => (congrArg d.factor (hi j)).le
  change (pResidual 2 (d.factor i)).map (d.factor i).subtype = X
  rw [hf]
  exact d.residual_eq

/-- The orbit step converts an identified T_v*-invariant residual into X itself. -/
theorem eq_X_of_transitive_invariant_residual (T : Subgroup G)
    (htrans : d.FactorsTransitive T) (B : Subgroup (Gstar z v))
    (hB : starImage z v (Tv T v) ≤ normalizer (B : Set _))
    (i : Fin d.count) (he : B = d.factorResidual i) : B = X :=
  he.trans (d.factorResidual_eq_X_of_count_eq_one
    (d.count_eq_one_of_transitive_invariant_residual T htrans B hB i he) i)

end NormalS3Decomposition
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
end
