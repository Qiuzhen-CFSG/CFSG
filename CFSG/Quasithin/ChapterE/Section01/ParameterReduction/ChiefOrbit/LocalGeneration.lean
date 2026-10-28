module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalAction

/-!
# The local generation dichotomy for a chief component

The stabilizer S normalizes the exact local weak closure W₀. Factoring an
element of JS as js therefore gives `N_JS(W₀) = N_J(W₀) S`. Applying local
generation to the literal intersection family and mapping into G proves
`JS = ⟨ℰₙ(JS,S,Γ), N_J(W₀) S⟩`, the source identity preceding `(!)`.
The final theorem applies this identity once the two branch containments have
been proved. It does not assert either diagonal branch.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The normalizer in the local product has precisely the source `J₀ S` form. -/
theorem map_localWeakClosure_normalizer (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    (normalizer (weakClosure ((stabilizer T J).subgroupOf (localGroup T J))
      (intersectionFamily (localGroup T J) Ω) : Set (localGroup T J))).map
        (localGroup T J).subtype = localNormalizer T J Ω ⊔ stabilizer T J := by
  let H := localGroup T J
  let S := stabilizer T J
  let W := localWeakClosure T J Ω
  have hSW := stabilizer_le_localWeakClosure_normalizer T J hΩ
  have hWH : W ≤ H := (localWeakClosure_le T J Ω).trans le_sup_right
  have he : W.subgroupOf H = weakClosure (S.subgroupOf H) (intersectionFamily H Ω) := by
    exact comap_map_eq_self (by rw [H.ker_subtype]; exact bot_le)
  rw [← he, ← subgroupOf_normalizer_eq hWH, subgroupOf_map_subtype]
  change normalizer (W : Set G) ⊓ H = (J ⊓ normalizer (W : Set G)) ⊔ S
  apply le_antisymm
  · rintro x ⟨hxW, hxH⟩
    have hxprod : x ∈ (J : Set G) * (S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left J S (show S ≤ normalizer J from inf_le_right)]
      exact hxH
    obtain ⟨j, hj, s, hs, rfl⟩ := hxprod
    have hjW : j ∈ normalizer (W : Set G) :=
      (normalizer (W : Set G)).mul_mem_cancel_right (hSW hs) |>.mp hxW
    exact mul_mem (mem_sup_left ⟨hj, hjW⟩) (mem_sup_right hs)
  · exact sup_le (le_inf inf_le_right (inf_le_left.trans le_sup_left))
      (le_inf hSW le_sup_right)

/-- Local generation gives the source dichotomy `(!)`, using the actual
intersection family and the exact intrinsic normalizer. -/
theorem local_generation {n : ℕ} (T : Sylow 2 G) {X J : Subgroup G}
    (hX : ChiefFactor.IsChief X ⊥) (hna : ¬ IsMulCommutative X)
    (hJ : IsComponentIn J X) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hgen : IsEGenerated n
      (pCoreJoinAction 2 (show stabilizer T J ≤ normalizer J from inf_le_right)).range) :
    localEFamily n T J Ω ⊔ (localNormalizer T J Ω ⊔ stabilizer T J) = localGroup T J := by
  let H := localGroup T J
  have hsub : J.IsSubnormal :=
    hJ.2.1.trans hJ.1 hX.normal_upper.isSubnormal
  obtain ⟨R, hR⟩ := exists_localSylow T J hsub
  have hg := local_isEGenerated T hX hna hJ hgen R
    (intersectionFamily H Ω) (intersectionFamily_elementary H hΩ)
  have hm := congrArg (Subgroup.map H.subtype) hg
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hR,
    map_localWeakClosure_normalizer T J hΩ] at hm
  exact hm

/-- Once both source branches lie in the ambient target, their component does too. -/
theorem component_le_of_local_branches {n : ℕ} (T : Sylow 2 G) {X J M : Subgroup G}
    (hX : ChiefFactor.IsChief X ⊥) (hna : ¬ IsMulCommutative X)
    (hJ : IsComponentIn J X) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hgen : IsEGenerated n
      (pCoreJoinAction 2 (show stabilizer T J ≤ normalizer J from inf_le_right)).range)
    (hTM : (T : Subgroup G) ≤ M) (hP : localEFamily n T J Ω ≤ M)
    (hJ₀ : localNormalizer T J Ω ≤ M) : J ≤ M := by
  have hlocal : localGroup T J ≤ M := by
    rw [← local_generation T hX hna hJ hΩ hgen]
    exact sup_le hP (sup_le hJ₀ (inf_le_left.trans hTM))
  exact le_sup_left.trans hlocal

end CFSG.Quasithin.ChapterE.ChiefOrbit
