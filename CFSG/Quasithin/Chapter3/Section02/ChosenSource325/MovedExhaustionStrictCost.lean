module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLinearThreeFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLinearThree

/-!
# The exact local displacement in the remaining natural SL₃ branch

For an elementary two-subgroup of SL₃(2^m), write c for its natural
fixed-space codimension over the defining field and d for its commutator
space dimension. The natural-plus-dual binary cost is m(c+d). Both c and
d are positive, while the actor rank is at most both mcd and 2m. A cost
strictly below twice that rank therefore forces c+d = 3.

Transport this calculation to distinct marked natural constituents spanning
a subspace and to an inner lift realizing the original actor on that subspace.
The Chapter12 consumer applies it to the literal W = componentOrbit V T,
with the exact image rank and component-centralizer kernel. The movement
premise of D.3.18 and the remaining support/multiplicity argument are retained
by qt-baumann-fsu; this calculation does not prove orbit exhaustion.
Source: Aschbacher--Smith, D.3.19 and the final D.3.10 argument, pp.203--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree
open CFSG.Quasithin.ChapterK.Linear.Natural
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

/-- Strict ratio below two forces the natural-plus-dual cost to be exactly 3m. -/
theorem linearThree_dual_cost_eq_of_strict
    (F : BinaryField) (A : Subgroup SL(3,F.Carrier)) (hA : IsElementaryTwo A)
    (hs : fixedCodim (linearNatural F 3) A + fixedCodim (linearNatural F 3).dual A <
      2 * rank A) :
    fixedCodim (linearNatural F 3) A + fixedCodim (linearNatural F 3).dual A = 3 * F.degree := by
  let := hA.2
  have hr : rank A ≤ 2 * F.degree := by
    have hh := IsElementaryAbelian.primeRank_ge_of_card A hA.card_eq_two_pow_rank
    rwa [Representation.HermitianTensorThree.ImageOuter.OuterRank.specialLinearThree_twoRank
      F.Carrier F.degree_pos F.card_eq] at hh
  obtain ⟨hc,hd⟩ := field_dimensions_pos F 3 hA.1
  have hb := field_displacement_rank_bound F 3 A
  rw [fixedCodim_eq_field_codim,dual_fixedCodim_eq_field_commutator,←mul_add] at hs ⊢
  have hp := F.degree_pos
  let c := Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ fieldFixedSpace F 3 A)
  let d := Module.finrank F.Carrier (fieldCommutator F 3 A)
  change F.degree * (c+d) < 2 * rank A at hs
  change rank A ≤ F.degree * (c*d) at hb
  change 0 < c at hc
  change 0 < d at hd
  change F.degree * (c+d) = 3 * F.degree
  have hsum : c+d < 4 := by nlinarith
  have hne : c+d ≠ 2 := by
    intro he
    have hc1 : c=1 := by omega
    have hd1 : d=1 := by omega
    rw [hc1,hd1] at hb hs
    norm_num at hb hs
    omega
  have he : c+d=3 := by omega
  rw [he,Nat.mul_comm]

private theorem equiv_fixedCodim
    {H X Y : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {σ : Representation (ZMod 2) H X} {τ : Representation (ZMod 2) H Y}
    (e : σ.Equiv τ) (A : Subgroup H) : fixedCodim σ A = fixedCodim τ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ τ (MonoidHom.id H)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

/-- Distinct natural markings identify the second constituent with the dual
for the same original acting group. -/
theorem distinct_linearThree_cost_eq_of_strict
    {H X Y : Type*} [Group H] [Finite H]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) H X) (τ : Representation (ZMod 2) H Y)
    (F : BinaryField) (a : ActionEquiv σ (linearNatural F 3))
    (b : ActionEquiv τ (linearNatural F 3))
    (hne : ¬ Nonempty (σ.Equiv τ)) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hs : fixedCodim σ A + fixedCodim τ A < 2 * rank A) :
    fixedCodim σ A + fixedCodim τ A = 3 * F.degree := by
  obtain ⟨c⟩ := (SourceCompletion.linearThree_naturals_same_or_dual
    τ σ F F ⟨b⟩ ⟨a⟩).resolve_left (fun he => hne (he.map Representation.Equiv.symm))
  have hc := equiv_fixedCodim c A
  have hσ := fixedCodim_map_equivariant σ (linearNatural F 3)
    a.groupEquiv.toMonoidHom a.linearEquiv a.intertwines A
  have hτ : fixedCodim σ.dual A = fixedCodim (linearNatural F 3).dual
      (A.map a.groupEquiv.toMonoidHom) := by
    apply fixedCodim_map_equivariant _ _ _ a.linearEquiv.symm.dualMap
    intro g f
    apply LinearMap.ext
    intro w
    change f (σ g⁻¹ (a.linearEquiv.symm w)) =
      f (a.linearEquiv.symm (linearNatural F 3 (a.groupEquiv g)⁻¹ w))
    apply congrArg f
    apply a.linearEquiv.injective
    rw [a.intertwines,a.linearEquiv.apply_symm_apply,a.linearEquiv.apply_symm_apply,map_inv]
  rw [hc,hσ,hτ] at hs ⊢
  rw [←rank_map_injective a.groupEquiv.toMonoidHom a.groupEquiv.injective A] at hs
  let := hA.2
  have hB : IsElementaryTwo (A.map a.groupEquiv.toMonoidHom) :=
    ⟨fun hz => hA.1 ((map_eq_bot_iff_of_injective _ a.groupEquiv.injective).mp hz),
      IsElementaryAbelian.map _⟩
  exact linearThree_dual_cost_eq_of_strict F _ hB hs

/-- The cost calculation on a complementary pair of actual constituents. -/
theorem complementary_linearThree_cost_eq_of_strict
    {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (I J : Subrepresentation ρ)
    (hIJ : IsCompl I.toSubmodule J.toSubmodule)
    (F : BinaryField) (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hs : fixedCodim ρ A < 2 * rank A) :
    fixedCodim ρ A = 3 * F.degree := by
  let e : (I.toRepresentation.prod J.toRepresentation).Equiv ρ :=
    .mk (I.toSubmodule.prodEquivOfIsCompl J.toSubmodule hIJ) (by
      intro g
      apply LinearMap.ext
      intro v
      exact (map_add (ρ g) v.1.val v.2.val).symm)
  have he := equiv_fixedCodim e A
  rw [fixedCodim_prod] at he
  rw [←he] at hs ⊢
  exact distinct_linearThree_cost_eq_of_strict _ _ F a b hne A hA hs

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]

omit [Finite H] in
/-- An inner lift agreeing on W preserves the actual action image rank and cost. -/
theorem inner_lift_restricted_rank_and_cost
    (ρ : Representation (ZMod 2) H E) (W : Submodule (ZMod 2) E)
    (K A : Subgroup H) (hK : K ≤ subspaceStabilizer ρ W)
    (hA : A ≤ subspaceStabilizer ρ W)
    (hf : Function.Injective (invariantSubspace ρ K W hK).toRepresentation)
    (f : A →* K) (he : ∀ (a : A) (v : W), ρ (f a : H) v.val = ρ a.val v.val) :
    rank f.range = rank (restrictedSubgroup ρ W A) ∧
      fixedCodim (invariantSubspace ρ K W hK).toRepresentation f.range =
        fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ∧
      (f.range = ⊥ ↔ restrictedSubgroup ρ W A = ⊥) := by
  let r := subgroupActionHom ρ W K hK
  have hr : Function.Injective r := by
    intro k l hh
    apply hf
    apply LinearMap.ext
    intro v
    exact congrArg (fun q => subspaceImageRepresentation ρ W q v) hh
  have hh : r.comp f = subgroupActionHom ρ W A hA := by
    apply MonoidHom.ext
    intro a
    apply subspaceImageRepresentation_injective ρ W
    apply LinearMap.ext
    intro v
    exact Subtype.ext (he a v)
  have hm : f.range.map r = restrictedSubgroup ρ W A := by
    rw [←MonoidHom.range_comp,hh,subgroupActionHom_range]
  refine ⟨?_,?_,?_⟩
  · rw [←hm,rank_map_injective r hr]
  · rw [←hm]
    exact fixedCodim_map_equivariant _ _ r (LinearEquiv.refl (ZMod 2) W)
      (fun _ _ => rfl) f.range
  · rw [←hm]
    exact (map_eq_bot_iff_of_injective f.range hr).symm

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

/-- The same calculation inside an invariant overmodule spanned by the pair. -/
theorem spanning_pair_linearThree_cost_eq_of_strict
    {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (I J W : Subrepresentation ρ)
    (hIW : I ≤ W) (hJW : J ≤ W)
    (hd : Disjoint I.toSubmodule J.toSubmodule)
    (hspan : I.toSubmodule ⊔ J.toSubmodule = W.toSubmodule)
    (F : BinaryField) (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation))
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hs : fixedCodim W.toRepresentation A < 2 * rank A) :
    fixedCodim W.toRepresentation A = 3 * F.degree := by
  let I' := sectionLower ρ I W
  let J' := sectionLower ρ J W
  let e : I'.toRepresentation.Equiv I.toRepresentation :=
    .mk (sectionLowerEquiv ρ hIW) (by intro g; rfl)
  let f : J'.toRepresentation.Equiv J.toRepresentation :=
    .mk (sectionLowerEquiv ρ hJW) (by intro g; rfl)
  have hd' : Disjoint I'.toSubmodule J'.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro v hi hj
    exact Subtype.ext ((Submodule.disjoint_def.mp hd) v.val hi hj)
  have hc' : Codisjoint I'.toSubmodule J'.toSubmodule := by
    apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    have hv : v.val ∈ I.toSubmodule ⊔ J.toSubmodule := hspan.symm ▸ v.property
    obtain ⟨i,hi,j,hj,hij⟩ := Submodule.mem_sup.mp hv
    exact Submodule.mem_sup.mpr
      ⟨⟨i,hIW hi⟩,hi,⟨j,hJW hj⟩,hj,Subtype.ext hij⟩
  let a' : ActionEquiv I'.toRepresentation (linearNatural F 3) :=
    ⟨a.groupEquiv,e.toLinearEquiv.trans a.linearEquiv,by intro g v; exact a.intertwines g (e v)⟩
  let b' : ActionEquiv J'.toRepresentation (linearNatural F 3) :=
    ⟨b.groupEquiv,f.toLinearEquiv.trans b.linearEquiv,by intro g v; exact b.intertwines g (f v)⟩
  apply complementary_linearThree_cost_eq_of_strict W.toRepresentation I' J' ⟨hd',hc'⟩ F a' b'
    (fun ⟨c⟩ => hne ⟨e.symm.trans (c.trans f)⟩) A hA hs

/-- Literal internal coordinates preserve joins of subgroups contained in U. -/
theorem internalSection_sup
    {G : Type*} [Group G] (U V Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hV : V ≤ U) (hZ : Z ≤ U) :
    internalSection U (V ⊔ Z) = internalSection U V ⊔ internalSection U Z := by
  change (AddSubgroup.toZModSubmodule 2) ((V ⊔ Z).subgroupOf U).toAddSubgroup = _
  rw [subgroupOf_sup hV hZ]
  rw [(Subgroup.toAddSubgroup : Subgroup U ≃o AddSubgroup (Additive U)).map_sup]
  exact (AddSubgroup.toZModSubmodule (M := Additive U) 2).map_sup _ _

/-- A natural constituent makes the component faithful on every containing submodule. -/
theorem faithful_overmodule_of_linearThree
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (I W : Subrepresentation ρ)
    (hIW : I ≤ W) (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3)) :
    Function.Injective W.toRepresentation := by
  intro k l he
  apply a.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := a.linearEquiv.surjective v
  have hw := LinearMap.congr_fun he ⟨w.val,hIW w.property⟩
  have hI : I.toRepresentation k w = I.toRepresentation l w :=
    Subtype.ext (congrArg (fun v : W => (v : E)) hw)
  exact (a.intertwines k w).symm.trans
    ((congrArg a.linearEquiv hI).trans (a.intertwines l w))

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
