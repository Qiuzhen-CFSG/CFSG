module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Recovering the tensor family and its moved subgroups from quotient calculations

Source: Aschbacher–Smith, Lemma 14.4.10(1),(4), printed pp.1010–1011,
combined manuscript of 1 March 2004. Star denotes H/O₂(H), whereas tilde
always denotes U/Z(U). Both quotients and all subgroup maps are literal.

An A₄ image of the actual Borel is two-perfect and has two-core quotient
of order three. This proves membership of its lifted residual X₂ and
separates it from X₁, whose image has order three. An exhaustive image
calculation then recovers the whole source family.

For the moved subgroup, we reuse the checked extraspecial lifting theorem
from the Mathieu branch: U-normality forces the central line into any
nonzero moved image. Thus a quotient plane lifts to order eight. Containment
in E lifts because E contains that central line. The finite-model image
catalogue and the tensor plane/containment calculations remain explicit;
this module alone does not prove Lemma 14.4.10.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G]

/-- The literal image in the extraspecial central quotient, distinct from `star`. -/
def tilde (U A : Subgroup G) : Subgroup (U ⧸ center U) :=
  (A.subgroupOf U).map (QuotientGroup.mk' (center U))

/-- Solvable residuals commute with the actual star quotient. -/
theorem star_component (H : Subgroup G) :
    star H (component H) = solvableResidual (coreQuotient H) := by
  unfold star component
  rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
  exact map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _)

/-- Every source actor gives a two-perfect, T*-invariant model actor of index three. -/
theorem star_mem_X {H T X : Subgroup G} (hX : X ∈ XFamily H T) :
    star H X ∈ XFamily ⊤ (star H T) := by
  refine ⟨le_top, ?_, ?_, ?_⟩
  · have hn : T.subgroupOf H ≤ normalizer (X.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hX.le_H]
      exact subgroupOf_mono H hX.T_normalizes
    exact (map_mono hn).trans ((X.subgroupOf H).le_normalizer_map _)
  · have he := congrArg (star H) hX.residual_eq
    rwa [star_twoResidual hX.le_H] at he
  · rw [← coreQuotient_card_eq_index]
    exact star_quotient_card_three hX

private theorem a4_twoPerfect : IsPPerfect 2 (alternatingGroup (Fin 4)) := by
  rw [← Equiv.Perm.twoResidual_eq_alternating]
  exact isPPerfect_pResidual 2

/-- The actual A₄ Borel image equals its two-residual. -/
theorem star_second_of_borel_equiv {H T : Subgroup G}
    (e : star H (borel H T) ≃* alternatingGroup (Fin 4)) :
    star H (second H T) = star H (borel H T) := by
  have hp : IsPPerfect 2 (star H (borel H T)) :=
    a4_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective
  rw [second, star_twoResidual (show borel H T ≤ H from
    inf_le_left.trans (map_subtype_le _))]
  unfold twoResidual
  rw [(pResidual_eq_top_iff 2 _).mpr hp, ← MonoidHom.range_eq_map, range_subtype]

/-- An A₄ identification of B* supplies every source X-condition for X₂. -/
theorem second_mem_X_of_borel_equiv {H T : Subgroup G} (hT : T ≤ H)
    (e : star H (borel H T) ≃* alternatingGroup (Fin 4)) :
    second H T ∈ XFamily H T := by
  refine ⟨second_le H T, second_T_normalized hT, twoResidual_idempotent _, ?_⟩
  rw [← coreQuotient_card_eq_index,
    Nat.card_congr (starCoreQuotientEquiv (second_le H T)).toEquiv,
    star_second_of_borel_equiv e]
  rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  have hc : Nat.card (pCore 2 (alternatingGroup (Fin 4))) = 4 := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have h := (pCore 2 (alternatingGroup (Fin 4))).card_mul_index
  rw [index_eq_card, hc, nat_card_alternatingGroup] at h
  norm_num at h ⊢
  omega

/-- The two literal residual subgroups have images of orders three and twelve. -/
theorem first_ne_second_of_borel_equiv {H T : Subgroup G}
    (hmodel : Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (e : star H (borel H T) ≃* alternatingGroup (Fin 4)) :
    first H ≠ second H T := by
  intro he
  have h := congrArg (fun X => Nat.card (star H X)) he
  rw [star_first, Theory.SpecificGroups.TensorThreeFive.tensor_threeCore_card hmodel,
    star_second_of_borel_equiv e, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup] at h
  norm_num at h

/-- Assembly from the remaining concrete Borel and exhaustive image calculations. -/
theorem family_eq_pair_of_borel_images {H T : Subgroup G}
    (hT : T ≤ H) (hcore : twoCore H ≤ T)
    (hmodel : Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (e : star H (borel H T) ≃* alternatingGroup (Fin 4))
    (hex : ∀ X ∈ XFamily H T,
      star H X = pCore 3 (coreQuotient H) ∨ star H X = star H (borel H T)) :
    XFamily H T = {first H, second H T} ∧ first H ≠ second H T := by
  refine ⟨family_eq_pair_of_star hcore (first_mem_X hT hmodel)
    (second_mem_X_of_borel_equiv hT e) ?_, first_ne_second_of_borel_equiv hmodel e⟩
  intro X hX
  simpa only [star_first, star_second_of_borel_equiv e] using hex X hX

omit [Finite G] in
/-- Containment lifts through the central quotient when E contains its kernel. -/
theorem tilde_le_iff {U A E : Subgroup G}
    (hAU : A ≤ U) (hZE : center U ≤ E.subgroupOf U) :
    tilde U A ≤ tilde U E ↔ A ≤ E := by
  unfold tilde
  rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk', sup_eq_left.mpr hZE]
  constructor
  · intro h x hx
    exact h (show (⟨x, hAU hx⟩ : U) ∈ A.subgroupOf U from hx)
  · exact subgroupOf_mono U

/-- A quotient plane in E gives actual Y-membership, including the central factor two. -/
theorem mem_Y_of_tilde_calculation {H T U V₂ E X : Subgroup G}
    [IsExtraspecial 2 U] (hX : X ∈ XFamily H T) (hUT : U ≤ T)
    (hHU : H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hcard : Nat.card (tilde U (movedSpace V₂ X)) = 4)
    (hE : tilde U (movedSpace V₂ X) ≤ tilde U E) :
    X ∈ YFamily H T V₂ E := by
  have hMU : movedSpace V₂ X ≤ U :=
    (commutator_mono hVU le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hX.le_H.trans hHU))
  exact ⟨hX, Mathieu.movedSpace_card_eight_of_extraspecial_image H T U V₂ X hX hUT
    hHU hVU hZV (QuotientGroup.mk' (center U)) (QuotientGroup.ker_mk' _) hcard,
    (tilde_le_iff hMU hZE).mp hE⟩

/-- Application to the literal X₁. Only the tensor image calculations remain. -/
theorem first_mem_Y_of_tilde_calculation {H T U V₂ E : Subgroup G}
    [IsExtraspecial 2 U] (hT : T ≤ H) (hUT : U ≤ T)
    (hHU : H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hmodel : Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (hcard : Nat.card (tilde U (movedSpace V₂ (first H))) = 4)
    (hE : tilde U (movedSpace V₂ (first H)) ≤ tilde U E) :
    first H ∈ YFamily H T V₂ E :=
  mem_Y_of_tilde_calculation (first_mem_X hT hmodel) hUT hHU hVU hZV hZE hcard hE

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
