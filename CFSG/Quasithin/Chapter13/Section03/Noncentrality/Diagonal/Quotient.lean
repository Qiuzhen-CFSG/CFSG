module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Basic
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PStar.Supplement
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.AutomorphismOvergroupCore


/-!
# The diagonal projection and its residual supplement

For a two-perfect subgroup A normalizing K, a two-group outer automorphism
quotient kills the outer action on K/O₂(K). Centerlessness constructs the
unique inner projection to that actual quotient. Lifting individual elements
through K → K/O₂(K) proves KA = K C, where C is the kernel of the literal
conjugation action. Two-perfectness then replaces C by its embedded O²(C).

The full kernel C contains O₂(K). It must not be identified with a subgroup
centralizing K: that would force [O₂(K),K]=1. The terminal argument uses
D=O²(C), retaining both groups and their actual inclusions.

These are group-theoretic constructions in the final paragraph of 13.3.14,
not a classification of K or a proof of the source block alternatives.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.893,
PDF p.910. The local projection argument also follows the checked construction
in Section06/.../SourceContainment/LinearThree/Projection.lean, without any
of that later section's hypotheses or results.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
variable {G : Type*} [Group G]

/-- The literal centralizer of K/O₂(K) in KL₊, embedded in G. -/
def quotientCentralizer (K A : Subgroup G) (hn : A ≤ normalizer K) : Subgroup G :=
  (pCoreJoinAction 2 hn).ker.map (K ⊔ A).subtype

/-- The two-residual of that centralizer, kept distinct from the centralizer. -/
def centralizerResidual (K A : Subgroup G) (hn : A ≤ normalizer K) : Subgroup G :=
  (pResidual 2 (quotientCentralizer K A hn)).map (quotientCentralizer K A hn).subtype

theorem quotientCentralizer_le (K A : Subgroup G) (hn : A ≤ normalizer K) :
    quotientCentralizer K A hn ≤ K ⊔ A := map_subtype_le _

theorem core_le_quotientCentralizer (K A : Subgroup G) (hn : A ≤ normalizer K) :
    K.pCoreIn 2 ≤ quotientCentralizer K A hn := by
  rintro x ⟨k, hk, rfl⟩
  refine mem_map.mpr ⟨inclusion le_sup_left k, ?_, rfl⟩
  change pCoreJoinAction 2 hn (inclusion le_sup_left k) = 1
  rw [pCoreJoinAction_on_component]
  have hq : QuotientGroup.mk' (pCore 2 K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
  rw [hq, map_one]

/-- The two-perfect actor has no outer action when the outer automorphism
 group of the actual quotient is a two-group. Centerlessness makes the
 inner lift unique. -/
theorem exists_quotient_projection (K A : Subgroup G) (hn : A ≤ normalizer K)
    (hA : IsPPerfect 2 A) (hc : center (K ⧸ pCore 2 K) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) :
    ∃ f : A →* K ⧸ pCore 2 K,
      (MulAut.conj : (K ⧸ pCore 2 K) →* MulAut (K ⧸ pCore 2 K)).comp f =
        (pCoreJoinAction 2 hn).comp (inclusion le_sup_right) := by
  let a := (pCoreJoinAction 2 hn).comp (inclusion le_sup_right)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore 2 K))
  have ht := hA.hom_eq_one_of_isPGroup ho (q.comp a)
  have hi : ∀ x, a x ∈ MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    intro x
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun f : A →* MulAut.Outer (K ⧸ pCore 2 K) => f x) ht)
  let j : (K ⧸ pCore 2 K) ≃* MulAut.innerSubgroup (K ⧸ pCore 2 K) :=
    MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hc)
  refine ⟨j.symm.toMonoidHom.comp (a.codRestrict _ hi), ?_⟩
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (j.apply_symm_apply ⟨a x, hi x⟩)

/-- Lift the inner projection through the actual quotient map. The remaining
 factor belongs to the literal quotient-action kernel. -/
theorem sup_quotientCentralizer (K A : Subgroup G) (hn : A ≤ normalizer K)
    (f : A →* K ⧸ pCore 2 K)
    (hf : (MulAut.conj : (K ⧸ pCore 2 K) →* MulAut (K ⧸ pCore 2 K)).comp f =
      (pCoreJoinAction 2 hn).comp (inclusion le_sup_right)) :
    K ⊔ quotientCentralizer K A hn = K ⊔ A := by
  apply le_antisymm (sup_le le_sup_left (quotientCentralizer_le K A hn))
  apply sup_le le_sup_left
  intro a ha
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (f ⟨a, ha⟩)
  let ka : (K ⊔ A : Subgroup G) := inclusion le_sup_left k
  let aa : (K ⊔ A : Subgroup G) := inclusion le_sup_right ⟨a, ha⟩
  have he : pCoreJoinAction 2 hn ka = pCoreJoinAction 2 hn aa := by
    rw [pCoreJoinAction_on_component, hk]
    exact DFunLike.congr_fun hf ⟨a, ha⟩
  have hm : (ka⁻¹ * aa : (K ⊔ A : Subgroup G)) ∈ (pCoreJoinAction 2 hn).ker := by
    change pCoreJoinAction 2 hn (ka⁻¹ * aa) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hh : (k : G)⁻¹ * a ∈ quotientCentralizer K A hn :=
    mem_map.mpr ⟨ka⁻¹ * aa, hm, rfl⟩
  simpa only [mul_inv_cancel_left] using
    (K ⊔ quotientCentralizer K A hn).mul_mem (mem_sup_left k.property) (mem_sup_right hh)

private theorem join_twoPerfect (K A : Subgroup G)
    (hK : IsPPerfect 2 K) (hA : IsPPerfect 2 A) : IsPPerfect 2 (K ⊔ A : Subgroup G) := by
  let H := K ⊔ A
  have hk : IsPPerfect 2 (K.subgroupOf H) :=
    hK.of_surjective (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm.surjective
  have ha : IsPPerfect 2 (A.subgroupOf H) :=
    hA.of_surjective (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).symm.surjective
  apply (pResidual_eq_top_iff 2 H).mp
  apply top_unique
  have hg : K.subgroupOf H ⊔ A.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ H from le_sup_left) (show A ≤ H from le_sup_right)]
    exact subgroupOf_self H
  rw [← hg]
  exact sup_le (le_pResidual_of_isPPerfect _ hk) (le_pResidual_of_isPPerfect _ ha)

/-- Replacing the quotient centralizer by its two-residual preserves KL₊.
 The residual is the actor to which the source's coprime argument applies. -/
theorem sup_centralizerResidual [Finite G] (K A : Subgroup G)
    (hn : A ≤ normalizer K) (hK : IsPPerfect 2 K) (hA : IsPPerfect 2 A)
    (hgen : K ⊔ quotientCentralizer K A hn = K ⊔ A) :
    K ⊔ centralizerResidual K A hn = K ⊔ A := by
  let H := K ⊔ A
  let C := quotientCentralizer K A hn
  let C' := C.subgroupOf H
  have hCH : C ≤ H := quotientCentralizer_le K A hn
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hn)
  have hg : K.subgroupOf H ⊔ C' = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ H from le_sup_left) hCH, hgen]
    exact subgroupOf_self H
  have hs := Theory.GroupTheory.sup_embedded_pResidual_eq_top
    (join_twoPerfect K A hK hA) (K.subgroupOf H) C' hg
  have hm := congrArg (map H.subtype) hs
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
    ← MonoidHom.range_eq_map, range_subtype] at hm
  have he : ((pResidual 2 C').map C'.subtype).map H.subtype =
      (pResidual 2 C).map C.subtype := by
    let e : C' ≃* C := subgroupOfEquivOfLe hCH
    rw [map_map]
    have hf : H.subtype.comp C'.subtype = C.subtype.comp e.toMonoidHom := rfl
    rw [hf, ← map_map, map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
  rw [he] at hm
  exact hm

open scoped commutatorElement

/-- The kernel definition really centralizes the original core quotient. -/
theorem quotientCentralizer_commutator_le_core (K A : Subgroup G)
    (hn : A ≤ normalizer K) :
    ⁅quotientCentralizer K A hn, K⁆ ≤ K.pCoreIn 2 := by
  apply commutator_le.mpr
  rintro c ⟨c', hc, rfl⟩ k hk
  have he : pCoreJoinAction 2 hn c' = 1 := hc
  have hx := DFunLike.congr_fun he (QuotientGroup.mk' (pCore 2 K) ⟨k, hk⟩)
  rw [pCoreJoinAction_mk] at hx
  let a := K.normalizerMonoidHom (inclusion (sup_le K.le_normalizer hn) c')
  have hm : a ⟨k, hk⟩ * (⟨k, hk⟩ : K)⁻¹ ∈ pCore 2 K := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hx
  exact mem_map.mpr ⟨_, hm, rfl⟩

/-- Every element of the residual stays in the same quotient centralizer. -/
theorem centralizerResidual_le (K A : Subgroup G) (hn : A ≤ normalizer K) :
    centralizerResidual K A hn ≤ quotientCentralizer K A hn := map_subtype_le _

theorem centralizerResidual_twoPerfect [Finite G] (K A : Subgroup G)
    (hn : A ≤ normalizer K) : IsPPerfect 2 (centralizerResidual K A hn) :=
  isPPerfect_embedded_pResidual 2 _

/-- The intrinsic inner projection constructs a residual supplement, with
 no assumed diagonal decomposition in G. -/
theorem exists_projection_and_residual_supplement [Finite G] (K A : Subgroup G)
    (hn : A ≤ normalizer K) (hK : IsPPerfect 2 K) (hA : IsPPerfect 2 A)
    (hc : center (K ⧸ pCore 2 K) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) :
    (∃ f : A →* K ⧸ pCore 2 K,
      (MulAut.conj : (K ⧸ pCore 2 K) →* MulAut (K ⧸ pCore 2 K)).comp f =
        (pCoreJoinAction 2 hn).comp (inclusion le_sup_right)) ∧
      K ⊔ centralizerResidual K A hn = K ⊔ A := by
  obtain ⟨f, hf⟩ := exists_quotient_projection K A hn hA hc ho
  exact ⟨⟨f, hf⟩, sup_centralizerResidual K A hn hK hA
    (sup_quotientCentralizer K A hn f hf)⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
