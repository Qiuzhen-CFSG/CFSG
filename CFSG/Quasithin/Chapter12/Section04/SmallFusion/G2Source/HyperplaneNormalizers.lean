module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplanePreparation
public import Theory.Representation.G2OrthogonalCover.HyperplaneStabilizers
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# The original binary G₂ cover-hyperplane normalizers

An escaping hyperplane in the chosen seven-dimensional cover avoids its fixed
scalar line. Transporting it through the full normalizer action identifies its
literal normalizer with the preimage of a model hyperplane stabilizer. The actor
image contains the derived G₂ group, so this stabilizer is maximal of index 36
or 28. The final theorem applies this to the original subgroup LT.

This is the maximal-normalizer premise in Aschbacher--Smith, Lemma 12.4.8,
printed p.815. It does not assert the later ambient-centralizer containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterE ChapterE.Section06 Atlas.G2.Natural
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "E" => TraceZero F

/-- The literal normalizer is maximal in each intermediate actor containing L. -/
theorem cover_hyperplane_normalizer_in
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    ∀ (A : Subgroup G), L ≤ A → A ≤ normalizer (L : Set G) →
      localNormalizer A U ⋖ A ∧
        ((localNormalizer A U).relIndex A = 36 ∨
         (localNormalizer A U).relIndex A = 28) := by
  intro A hLA hAN
  classical
  let _ := D.elementary
  have hg := escaping_cover_subspaces h D structural e hne hUV hcor hescape
  obtain ⟨z,hz,hfix,_,_,_,_⟩ := exists_fixed_involution_setup h D structural e hne
  obtain ⟨b,φ,hφ,hφL⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  let c : Additive V ≃ₗ[F] E := by
    let ca : Additive V ≃+ E := {
      toFun v := (b v.toMul).toAdd
      invFun x := Additive.ofMul (b.symm (Multiplicative.ofAdd x))
      left_inv v := congrArg Additive.ofMul (b.symm_apply_apply v.toMul)
      right_inv x := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
      map_add' v w := congrArg Multiplicative.toAdd (map_mul b v.toMul w.toMul) }
    exact { ca with map_smul' := ZMod.map_smul ca }
  let W₀ := AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup
  let W := W₀.map c.toLinearMap
  have hW (x : E) : x ∈ W ↔ (b.symm (Multiplicative.ofAdd x) : G) ∈ U := by
    constructor
    · rintro ⟨v,hv,rfl⟩
      change (b.symm (b v.toMul) : G) ∈ U
      rwa [b.symm_apply_apply]
    · intro hx
      refine ⟨Additive.ofMul (b.symm (Multiplicative.ofAdd x)),hx,?_⟩
      change (b (b.symm (Multiplicative.ofAdd x))).toAdd = x
      rw [b.apply_symm_apply]
      exact toAdd_ofAdd x
  have hd : finrank F W = 6 := by
    change finrank F (W₀.map c.toLinearMap) = 6
    rw [c.finrank_map_eq]
    let eu : W₀ ≃ U := {
      toFun v := ⟨v.val.toMul,v.property⟩
      invFun u := ⟨Additive.ofMul ⟨u,hUV u.property⟩,u.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    have hc : Nat.card W₀ = 64 := (Nat.card_congr eu).trans hg.1
    rw [Module.natCard_eq_pow_finrank (K := F),Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hc)
  let zi : V := b.symm (Multiplicative.ofAdd (identity F))
  have hzi1 : (zi : G) ≠ 1 := by
    intro heq
    have he : zi = 1 := Subtype.ext heq
    have hh := congrArg (fun v : V => (b v).toAdd) he
    have hi : identity F = 0 := by
      change (b (b.symm (Multiplicative.ofAdd (identity F)))).toAdd = (b 1).toAdd at hh
      rw [b.apply_symm_apply,map_one] at hh
      simpa only [toAdd_ofAdd, toAdd_one] using hh
    exact Atlas.SplitOctonion.unit_ne_zero (congrArg Subtype.val hi)
  have hziL : (zi : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := hφ ⟨l,L.le_normalizer hl⟩ (identity F)
    rw [traceZeroAction_identity] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hzieq : (zi : G) = z := by
    have hzmem : (zi : G) ∈ zpowers z := hfix ▸ ⟨zi.property,hziL⟩
    rw [mem_zpowers_iff_mem_range_orderOf,hz] at hzmem
    obtain ⟨n,hn,hnz⟩ := Finset.mem_image.mp hzmem
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hzi1 (by simpa using hnz.symm)).elim
    · simpa using hnz.symm
  have hi : identity F ∉ W := by
    intro hin
    have hzU : z ∈ U := hzieq ▸ (hW (identity F)).mp hin
    apply hg.2.1
    change V ⊓ centralizer (L : Set G) ≤ U
    rw [hfix]
    exact zpowers_le.mpr hzU
  let f : A →* Atlas.G2.Model F := φ.comp (inclusion hAN)
  have hderived : commutator (Atlas.G2.Model F) ≤ f.range := by
    intro g hg
    obtain ⟨k,hk⟩ := e.groupEquiv.surjective ⟨g,hg⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) k
    refine ⟨⟨l,hLA l.property⟩,?_⟩
    change φ ⟨l,hAN (hLA l.property)⟩ = g
    rw [hφL]
    exact congrArg Subtype.val hk
  let S := subspaceStabilizer ((traceZeroAction F).comp f.range.subtype) W
  obtain ⟨hmax,hindex⟩ := OrthogonalCover.Hyperplanes.cover_hyperplane_stabilizer
    f.range hderived W hd hi
  have hstab : S.comap f.rangeRestrict = (localNormalizer A U).subgroupOf A := by
    ext a
    change (∀ x, traceZeroAction F (f a) x ∈ W ↔ x ∈ W) ↔
      (a : G) ∈ A ∧ (a : G) ∈ normalizer (U : Set G)
    rw [and_iff_right a.property]
    constructor
    · intro ha
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply eq_of_le_of_card_ge
      · rintro _ ⟨u,hu,rfl⟩
        let v : V := ⟨u,hUV hu⟩
        have hv : (b v).toAdd ∈ W := by
          rw [hW]
          rw [ofAdd_toAdd, b.symm_apply_apply]
          exact hu
        have hv' := (hW _).mp ((ha _).mpr hv)
        change (b.symm (Multiplicative.ofAdd (traceZeroAction F
          (φ (inclusion hAN a)) (b v).toAdd)) : G) ∈ U at hv'
        rw [hφ] at hv'
        change (a : G) * (b.symm (b v) : G) * (a : G)⁻¹ ∈ U at hv'
        rw [b.symm_apply_apply] at hv'
        change (a : G) * (u : G) * (a : G)⁻¹ ∈ U at hv'
        simpa only [MonoidHom.coe_coe, MulAut.conj_apply] using hv'
      · rw [card_map_of_injective (MulAut.conj (a : G)).injective]
    · intro ha x
      rw [hW,hW]
      change (b.symm (Multiplicative.ofAdd
        (traceZeroAction F (φ (inclusion hAN a)) x)) : G) ∈ U ↔ _
      rw [hφ]
      exact (mem_normalizer_iff.mp ha _).symm
  have hco : IsCoatom ((localNormalizer A U).subgroupOf A) :=
    hstab ▸ isCoatom_comap_of_surjective f.rangeRestrict_surjective hmax
  have hcov := (covBy_map_subtype_iff A _ _).mpr hco.covBy_top
  have hm : ((localNormalizer A U).subgroupOf A).map A.subtype = localNormalizer A U :=
    map_subgroupOf_eq_of_le inf_le_left
  rw [hm,←MonoidHom.range_eq_map,range_subtype] at hcov
  refine ⟨hcov,?_⟩
  change ((localNormalizer A U).subgroupOf A).index = 36 ∨
    ((localNormalizer A U).subgroupOf A).index = 28
  rw [←hstab,index_comap_of_surjective S f.rangeRestrict_surjective]
  exact hindex

/-- The maximal-normalizer and index conclusions for the original subgroup LT. -/
theorem cover_hyperplane_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G) ∧
      ((localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex (L ⊔ (T : Subgroup G)) = 36 ∨
       (localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex (L ⊔ (T : Subgroup G)) = 28) :=
  cover_hyperplane_normalizer_in h D structural e hne hUV hcor hescape _ le_sup_left
    (sup_le L.le_normalizer (structural L h).1)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
