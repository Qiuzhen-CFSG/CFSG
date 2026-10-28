module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplaneNormalizers
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.ThreeAction

/-!
# Faithful cubic action on the original G₂ cover hyperplane

The derived actor has order 6048, while the original hyperplane normalizer
has relative index 36 or 28. Thus its order is divisible by three. Cauchy's
theorem supplies an actual cubic element in L; the pointwise-fixer calculation
and the original quotient by O₂(L) force its action on U to be nontrivial.
Its prime-order cyclic subgroup therefore acts faithfully on U.

This discharges the faithful-three-action premise of the E.6.14 application
in Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterE ChapterE.Section06 Atlas.G2.Natural
open ChapterB.QuasisimpleSource ChapterE.Section06.InvariantSubspaces
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2

/-- An original cubic element of L normalizes U and acts nontrivially on U. -/
theorem exists_cover_cubic_hyperplane_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    ∃ x : G, x ∈ L ∧ orderOf x = 3 ∧
      x ∈ normalizer (U : Set G) ∧ x ∉ centralizer (U : Set G) := by
  classical
  have hg := escaping_cover_subspaces h D structural e hne hUV hcor hescape
  have hi := (cover_hyperplane_normalizer_in h D structural e hne hUV hcor hescape
    L le_rfl L.le_normalizer).2
  let S := (localNormalizer L U).subgroupOf L
  have hcardQ : Nat.card (L ⧸ pCore 2 L) = 6048 :=
    (Nat.card_congr e.groupEquiv.toEquiv).trans
      (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))
  have hL := (pCore 2 L).card_mul_index
  change Nat.card (pCore 2 L) * Nat.card (L ⧸ pCore 2 L) = Nat.card L at hL
  rw [hcardQ] at hL
  have hS := S.card_mul_index
  have hthree : 3 ∣ Nat.card S := by
    change S.index = 36 ∨ S.index = 28 at hi
    rcases hi with hi | hi <;> rw [hi] at hS <;> omega
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hthree
  have hxG : orderOf ((x : L) : G) = 3 :=
    (orderOf_coe (x : L)).trans ((orderOf_coe x).trans hx)
  refine ⟨x, (x : L).property, hxG, x.property.2, ?_⟩
  intro hxU
  have hxV : ((x : L) : G) ∈ centralizer (V : Set G) :=
    hg.2.2.1.le ⟨D.normalizes (x : L).property, hxU⟩
  obtain ⟨b,φ,hφ,hφL⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  let m : normalizer (L : Set G) := ⟨(x : L), L.le_normalizer (x : L).property⟩
  have hm : φ m = 1 := by
    apply traceZeroAction_injective_binary
    apply LinearMap.ext
    intro w
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hφ,map_one,Module.End.one_apply]
    change ((x : L) : G) * (b.symm (Multiplicative.ofAdd w) : G) *
      ((x : L) : G)⁻¹ = (b.symm (Multiplicative.ofAdd w) : G)
    rw [← hxV _ (b.symm (Multiplicative.ofAdd w)).property, mul_inv_cancel_right]
  have hxcore : (x : L) ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff (x : L)).mp
    apply e.groupEquiv.injective
    apply Subtype.ext
    rw [map_one]
    exact (hφL (x : L)).symm.trans hm
  let y : pCore 2 L := ⟨(x : L), hxcore⟩
  have hy : orderOf y = 3 := (orderOf_coe y).symm.trans ((orderOf_coe x).trans hx)
  have hc := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) y
  rw [hy] at hc
  norm_num at hc

/-- The literal faithful-three-action input of the E.6.14 source application. -/
theorem cover_faithful_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    HasFaithfulThreeAction U := by
  obtain ⟨x,_,hx,hxn,hxc⟩ :=
    exists_cover_cubic_hyperplane_actor h D structural e hne hUV hcor hescape
  let A := zpowers x
  have hA : Nat.card A = 3 := (Nat.card_zpowers x).trans hx
  have hAN : A ≤ normalizer (U : Set G) := zpowers_le.mpr hxn
  let f : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hAN)
  refine ⟨A,hAN,hA,?_⟩
  change Function.Injective f
  apply f.ker_eq_bot_iff.mp
  let : IsSimpleGroup A := isSimpleGroup_of_prime_card hA
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with he | he
  · exact he
  · have hk : (⟨x,mem_zpowers x⟩ : A) ∈ f.ker := he ▸ mem_top _
    have hf : f ⟨x,mem_zpowers x⟩ = 1 := hk
    apply (hxc ?_).elim
    intro u hu
    have hh := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : G)) hf
    change x * u * x⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
