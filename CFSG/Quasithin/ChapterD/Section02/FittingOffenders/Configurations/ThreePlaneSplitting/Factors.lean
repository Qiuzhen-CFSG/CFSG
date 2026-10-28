module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.ThreePlaneSplitting.Family
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Marked products and support sums

The invariant-line family is independent and generates the original core.
Its multiplication map is therefore bijective; cardinality identifies the
number of lines with the given exponent `s`. Reindexing by `Fin s` gives
literal subgroups of `P`, without changing their ambient inclusions.
Independence and generation of the moved spaces make their actual addition
map bijective as well. Thus every field of `SupportFactors` is constructed.

Source: Aschbacher--Smith, D.2.14(3),(7)(ii), printed p.187.
-/

public section

open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.FittingConfigurations

private theorem product_bijective {H I : Type*} [CommGroup H] [Fintype I]
    (F : I → Subgroup H) (hi : iSupIndep F) (hg : ⨆ i, F i = ⊤) :
    Function.Bijective (fun x : (i : I) → F i => ∏ i, (x i : H)) := by
  have hc : Pairwise (fun i j : I => ∀ x y : H, x ∈ F i → y ∈ F j → Commute x y) :=
    fun _ _ _ x y _ _ => Commute.all x y
  have he : (fun x : (i : I) → F i => ∏ i, (x i : H)) = Subgroup.noncommPiCoprod hc := by
    funext x
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  rw [he]
  refine ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hi, ?_⟩
  apply MonoidHom.range_eq_top.mp
  rw [Subgroup.noncommPiCoprod_range, hg]

private theorem sum_bijective {W I : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype I] (U : I → Submodule (ZMod 2) W)
    (hi : iSupIndep U) (hg : ⨆ i, U i = ⊤) :
    Function.Bijective (fun v : (i : I) → U i => ∑ i, (v i : W)) := by
  classical
  let f : ((i : I) → U i) →ₗ[ZMod 2] W :=
    { toFun := fun v => ∑ i, (v i : W)
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  constructor
  · intro v w he
    funext i
    apply Subtype.ext
    exact (iSupIndep_iff_finsetSum_eq_imp_eq U).mp hi Finset.univ
      (fun j => (v j : W)) (fun j => (w j : W))
      (fun j _ => ⟨(v j).property, (w j).property⟩) he i (Finset.mem_univ i)
  · change Function.Surjective f
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hg]
    apply iSup_le
    intro i v hv
    refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
    change ∑ j, ((Pi.single i (⟨v, hv⟩ : U i) : (j : I) → U j) j : W) = v
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Construction of all literal factors and support summands, before the
ratio inequality rules out two planes. -/
theorem Reduced.exists_invariant_supportFactors {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hsmall : SmallInvariantSupports ρ P A) :
    ∃ d : SupportFactors ρ P s, ∀ i, A ≤ Subgroup.normalizer (d.ambient i : Set G) := by
  classical
  let : IsElementaryAbelian 3 P := h.elementary
  let : CommGroup P := IsMulCommutative.instCommGroup
  let I := {Z : Subgroup G // IsInvariantLine P A Z}
  let : Fintype I := Fintype.ofFinite I
  let F : I → Subgroup P := fun Z => Z.val.subgroupOf P
  have hm (Z : I) : (F Z).map P.subtype = Z.val :=
    Subgroup.map_subgroupOf_eq_of_le Z.property.1
  have hcard (Z : I) : Nat.card (F Z) = 3 := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hm]
    exact Z.property.2.1
  have hi : iSupIndep F := by
    rw [iSupIndep_def]
    intro Z
    apply Subgroup.disjoint_def.mpr
    intro z hz hrest
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp ((h.invariant_lines_independent ρ hsmall) Z) hz
    have hh := Subgroup.mem_map_of_mem P.subtype hrest
    rw [Subgroup.map_iSup] at hh
    simp only [Subgroup.map_iSup, hm] at hh
    exact hh
  have hg : (⨆ Z, F Z) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_iSup]
    simp only [hm, ← MonoidHom.range_eq_map, P.range_subtype]
    exact h.invariant_lines_generate ρ
  have hb := product_bijective F hi hg
  have hpow : 3 ^ Fintype.card I = 3 ^ s := by
    calc
      3 ^ Fintype.card I = Nat.card ((Z : I) → F Z) := by simp [Nat.card_pi, hcard]
      _ = Nat.card P := Nat.card_congr (Equiv.ofBijective _ hb)
      _ = 3 ^ s := h.card_core
  have hI : Fintype.card I = s := (Nat.pow_right_injective (by decide : 2 ≤ 3)) hpow
  let e : Fin s ≃ I := (Fintype.equivFinOfCardEq hI).symm
  let factor : Fin s → Subgroup P := F ∘ e
  have hif : iSupIndep factor := hi.comp e.injective
  have hgf : (⨆ i, factor i) = ⊤ := by
    simpa only [factor, Function.comp_def, e.surjective.iSup_comp] using hg
  have hmf (i : Fin s) : (factor i).map P.subtype = (e i).val := hm (e i)
  have hvs : iSupIndep (fun i : Fin s => subspaceCommutator ρ ⊤ ((factor i).map P.subtype)) := by
    simp only [hmf]
    exact (h.invariant_supports_independent ρ hsmall).comp e.injective
  have hvg : (⨆ i : Fin s, subspaceCommutator ρ ⊤ ((factor i).map P.subtype)) = ⊤ := by
    simp only [hmf]
    rw [e.surjective.iSup_comp (fun Z : I => subspaceCommutator ρ ⊤ Z.val)]
    exact h.invariant_supports_generate ρ
  refine ⟨{
    factor := factor
    card_factor := fun i => hcard (e i)
    multiply_bijective := ?_
    support_dim := ?_
    add_bijective := sum_bijective _ hvs hvg }, ?_⟩
  · simpa only [Fin.prod_ofFn] using product_bijective factor hif hgf
  · intro i
    rw [hmf]
    exact hsmall _ (e i).property
  · intro i
    change A ≤ Subgroup.normalizer ((factor i).map P.subtype : Set G)
    rw [hmf]
    exact (e i).property.2.2

end CFSG.Quasithin.ChapterD.FittingConfigurations
