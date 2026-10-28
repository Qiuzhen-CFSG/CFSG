module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# Normalizers of perfect covers of J₄

Every automorphism of the actual J₄ model is inner. Faithfulness of descent
through the center lifts this assertion to every perfect central cover.
Consequently the full normalizer of such a subgroup is its product with
its centralizer. No assertion that the covering kernel is trivial is needed.

The relative version keeps the entire covering subgroup inside its original
ambient overgroup. It supplies the factorization at the start of the J₄
argument in Aschbacher--Smith 4.2.13, printed p.612, and the odd-normalizer
factorization used in 4.4.3, printed pp.621--623.
-/

public section
open Subgroup
open scoped Pointwise
namespace Janko4
variable {E G : Type*} [Group E] [Group G]

/-- Innerness on the simple quotient lifts to the full perfect cover. -/
theorem perfect_cover_conj_surjective [Group.IsPerfect E]
    (e : (E ⧸ center E) ≃* Model) :
    Function.Surjective (MulAut.conj : E →* MulAut E) := by
  intro a
  obtain ⟨x,hx⟩ := (MulAut.centralQuotientAction_inner_iff e a).mp
    (AdequateLocal.exists_eq_conj (MulAut.centralQuotientAction e a))
  exact ⟨x,hx.symm⟩

/-- The normalizer of a perfect cover is its central product with the
literal ambient centralizer. -/
theorem perfect_cover_normalizer (K : Subgroup G) [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Model) :
    normalizer (K : Set G) = K ⊔ centralizer (K : Set G) := by
  apply le_antisymm
  · intro g hg
    have hinner : K.normalizerMonoidHom ⟨g,hg⟩ ∈
        (MulAut.conj : K →* MulAut K).range :=
      perfect_cover_conj_surjective e _
    have h := K.normalizerMonoidHom_comap_conj_range
    exact (h ▸ hinner : (⟨g,hg⟩ : normalizer (K : Set G)) ∈
      (K ⊔ centralizer (K : Set G)).subgroupOf (normalizer (K : Set G)))
  · exact sup_le K.le_normalizer (centralizer_le_normalizer _)

/-- Relative factorization retains the original overgroup and its centralizer
intersection, even when the cover has nontrivial center. -/
theorem perfect_cover_overgroup (K H : Subgroup G) [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Model) (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) :
    H = K ⊔ (H ⊓ centralizer (K : Set G)) := by
  apply le_antisymm
  · intro h hh
    have hm : h ∈ (K : Set G) * (centralizer (K : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left K _ (centralizer_le_normalizer _),
        ← perfect_cover_normalizer K e]
      exact hHK hh
    obtain ⟨k,hk,c,hc,rfl⟩ := hm
    have hcH : c ∈ H := by
      simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem (hKH hk)) hh
    exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨hcH,hc⟩)
  · exact sup_le hKH inf_le_left

/-- The actual model is its full automorphism group under conjugation. -/
noncomputable def modelConjEquiv : Model ≃* MulAut Model :=
  MulEquiv.ofBijective MulAut.conj ⟨by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    rw [← model_center_eq_bot]
    apply mem_center_iff.mpr
    intro y
    have hy := DFunLike.congr_fun hx y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm,
    AdequateLocal.conj_surjective⟩

/-- The ambient action on the full cover, expressed in the actual J₄ model. -/
noncomputable def perfectCoverAction (K : Subgroup G) [K.Normal]
    (e : (K ⧸ center K) ≃* Model) : G →* Model :=
  modelConjEquiv.symm.toMonoidHom.comp
    ((MulAut.centralQuotientAction e).comp MulAut.conjNormal)

theorem perfectCoverAction_on_subgroup (K : Subgroup G) [K.Normal]
    (e : (K ⧸ center K) ≃* Model) (k : K) :
    perfectCoverAction K e (k : G) = e (QuotientGroup.mk' (center K) k) := by
  apply modelConjEquiv.injective
  change modelConjEquiv (modelConjEquiv.symm
    (MulAut.centralQuotientAction e (MulAut.conjNormal (k : G)))) = _
  rw [modelConjEquiv.apply_symm_apply]
  have hk : (MulAut.conjNormal (k : G) : MulAut K) = MulAut.conj k := by
    ext z
    rfl
  rw [hk]
  exact MulAut.centralQuotientAction_conj e k

theorem perfectCoverAction_surjective (K : Subgroup G) [K.Normal]
    (e : (K ⧸ center K) ≃* Model) :
    Function.Surjective (perfectCoverAction K e) := by
  intro y
  obtain ⟨q,rfl⟩ := e.surjective y
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) q
  exact ⟨k,perfectCoverAction_on_subgroup K e k⟩

theorem perfectCoverAction_ker (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Model) :
    (perfectCoverAction K e).ker = centralizer (K : Set G) := by
  have hi : Function.Injective
      (modelConjEquiv.symm.toMonoidHom.comp (MulAut.centralQuotientAction e)) :=
    modelConjEquiv.symm.injective.comp (MulAut.centralQuotientAction_injective e)
  ext g
  change (modelConjEquiv.symm.toMonoidHom.comp (MulAut.centralQuotientAction e))
    (MulAut.conjNormal g) = 1 ↔ g ∈ centralizer (K : Set G)
  rw [map_eq_one_iff _ hi]
  constructor
  · intro hg k hk
    have hkg := congrArg K.subtype (DFunLike.congr_fun hg (⟨k,hk⟩ : K))
    change g * k * g⁻¹ = k at hkg
    exact (mul_inv_eq_iff_eq_mul.mp hkg).symm
  · intro hg
    ext k
    change g * (k : G) * g⁻¹ = (k : G)
    rw [← hg k k.property,mul_inv_cancel_right]

end Janko4
