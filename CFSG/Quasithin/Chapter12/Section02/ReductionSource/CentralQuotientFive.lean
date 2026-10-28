module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenModules
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.ProjectiveCentralCover
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Reconstructing the original A₅ module from its central quotient

The natural binary A₅ module is projective. Reindex the original chosen
module by its literal L/O₂(L) marking and split an equivariant natural
quotient. Its fixed kernel vanishes because the Irr⁺ module is generated
by L-commutators. Thus the quotient marking lifts to a conjugation model
on the same original V, with no assumed splitting or trivial centralizer.

The last theorem takes the literal central quotient of the chosen subspace
in R₂(LT). The earlier source theorem must still identify that quotient
as natural; no universal 12.2.2 or 13.3.2 classification is asserted here.

Source: Aschbacher--Smith, 12.2.2(3d) and 13.3.2(3), printed pp.795 and
885, using I.1.6(1) and the projective-cover observation I.1.5, p.408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual L-action on the chosen subspace, with its original inclusion. -/
@[expose] def chosenAction : Representation (ZMod 2) L D.space :=
  ((invariantSubspace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G))) D.space D.irrPlus.invariant).toRepresentation).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom

/-- The literal two-core of L acts trivially on its original chosen section. -/
theorem chosenAction_core : pCore 2 L ≤ D.chosenAction.ker := by
  let H := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hc : L.pCoreIn 2 ≤ H.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn L H 2 le_sup_left
      (show (L.subgroupOf H).Normal from inferInstance).isSubnormal
  intro l hl
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
  have hv : (v.val.toMul.val : G) ∈ V :=
    D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
  have hh := D.core_centralizes (hc (mem_map_of_mem L.subtype hl))
    (v.val.toMul.val : G) hv
  change (v.val.toMul.val : G) * (l : G) = (l : G) * (v.val.toMul.val : G) at hh
  rw [← hh, mul_inv_cancel_right]

set_option backward.isDefEq.respectTransparency false in
/-- A natural quotient of the original chosen A₅ module has no fixed kernel. -/
theorem a5_quotient_injective
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (p : D.space →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (hp : Function.Surjective p)
    (he : ∀ (l : L) (v : D.space),
      p (D.chosenAction l v) =
        Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (p v))
    (hk : ∀ v : D.space, p v = 0 → ∀ l : L,
      D.chosenAction l v = v) :
    Function.Injective p := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) D.space :=
    (QuotientGroup.lift (pCore 2 L) D.chosenAction D.chosenAction_core).comp e.symm.toMonoidHom
  have hσ (l : L) (v : D.space) :
      σ (e (QuotientGroup.mk' (pCore 2 L) l)) v =
        D.chosenAction l v := by
    change (QuotientGroup.lift (pCore 2 L) D.chosenAction D.chosenAction_core)
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))) v = _
    rw [e.symm_apply_apply]
    rfl
  have hsurj : Function.Surjective (fun l : L => e (QuotientGroup.mk' (pCore 2 L) l)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  let f : σ.IntertwiningMap Chapter6.Source.a5Module :=
    { toLinearMap := p
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        obtain ⟨l, rfl⟩ := hsurj g
        change p (σ _ v) = _
        rw [hσ]
        exact he l v }
  have hfixed : ∀ v, f v = 0 → ∀ g, σ g v = v := by
    intro v hv g
    obtain ⟨l, rfl⟩ := hsurj g
    rw [hσ]
    exact hk v hv l
  have hc : Coinvariants.ker σ = ⊤ := by
    have hle : D.space ≤ (Coinvariants.ker σ).map D.space.subtype := by
      apply D.irrPlus.isIrrPlus.choose_spec.1.ge.trans
      apply Submodule.span_le.mpr
      rintro _ ⟨l, hl, v, hv, rfl⟩
      let l' : L := ⟨l.val, hl⟩
      let v' : D.space := ⟨v, hv⟩
      refine ⟨σ (e (QuotientGroup.mk' (pCore 2 L) l')) v' - v',
        Coinvariants.sub_mem_ker _ _, ?_⟩
      rw [hσ]
      rfl
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hle v.property
    exact (Subtype.ext he : w = v) ▸ hw
  let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      Chapter6.Source.a5Module.asModule := BinaryPermutation.alternatingFive_natural_projective
  exact f.injective_of_projective_of_fixed_kernel hp hfixed hc

/-- The fixed-kernel natural quotient reconstructs V itself, preserving the
given L/O₂(L) marking and the original ambient conjugation action. -/
theorem a5_model_of_natural_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (p : D.space →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (hp : Function.Surjective p)
    (he : ∀ (l : L) (v : D.space),
      p (D.chosenAction l v) =
        Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (p v))
    (hk : ∀ v : D.space, p v = 0 → ∀ l : L, D.chosenAction l v = v) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let a := LinearEquiv.ofBijective p ⟨D.a5_quotient_injective e p hp he hk, hp⟩
  let f := D.spaceEquiv.symm.trans a.toAddEquiv.toMultiplicative
  refine ⟨e, f, ?_⟩
  intro l v
  let v' : D.space := (D.spaceEquiv.symm v).toAdd
  have hv : (v'.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply v').symm.trans
      (congrArg (fun w : V => (w : G)) (D.spaceEquiv.apply_symm_apply v))
  change (D.spaceEquiv (Multiplicative.ofAdd
    (a.symm (Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l))
      (a v')))) : G) = _
  have ha : a (D.chosenAction l v') =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v') := he l v'
  rw [← ha, a.symm_apply_apply, D.spaceEquiv_apply]
  change (l : G) * (v'.val.toMul.val : G) * (l : G)⁻¹ = _
  rw [hv]

/-- The source central quotient of the original Irr⁺ subspace. -/
abbrev chosenCentralQuotient := centralQuotient
  (reducedRepresentation (L ⊔ (T : Subgroup G)))
  (L.subgroupOf (L ⊔ (T : Subgroup G))) D.space

/-- The induced L-action on that literal central quotient. -/
@[expose] def chosenCentralAction : Representation (ZMod 2) L D.chosenCentralQuotient :=
  (centralQuotientRepresentation (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G))) D.space D.irrPlus.invariant).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom

/-- The A₅ central-quotient alternative of 12.2.2(3d) gives the full
conjugation model needed in 13.3.2(3). -/
theorem a5_model_of_central_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v)) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let C := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  let p := a.toLinearMap.comp C.mkQ
  apply D.a5_model_of_natural_quotient e p
    (a.surjective.comp (Submodule.mkQ_surjective _))
  · intro l v
    exact ha l (C.mkQ v)
  · intro v hv l
    have hq : C.mkQ v = 0 := a.injective (hv.trans (map_zero a).symm)
    have hz : v ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hq
    exact Subtype.ext (hz ((subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
