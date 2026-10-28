module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Configuration

/-!
# Bringing the smaller factor back into the original module

The second fixed space consists exactly of globally fixed vectors. Mapping a
submodule of the second action through its original inclusion preserves its
fixed supplement and moved-space clauses. Its quotient image is identified
with the literal image in V/C_V(G) through the original quotient maps.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.8, p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
  (c : Configuration ρ A)

/-- The smaller submodule, carried by its original inclusion into V. -/
@[expose] def Configuration.liftSpace (U : Subrepresentation c.secondAction) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.map c.secondSpace.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := by
    obtain ⟨w,hw,rfl⟩ := hv
    obtain ⟨a,b,rfl⟩ := c.product.exists_mul g
    refine ⟨c.secondAction b w,U.apply_mem_toSubmodule b hw,?_⟩
    have hm : (c.secondAction b w : V) ∈ fixedSpace ρ c.first := by
      rw [← c.secondSpace_eq]
      exact (c.secondAction b w).property
    change ρ (b : G) (w : V) = ρ ((a : G) * (b : G)) (w : V)
    rw [map_mul,Module.End.mul_apply]
    exact (hm a).symm

theorem Configuration.liftSpace_le (U : Subrepresentation c.secondAction) :
    (c.liftSpace U).toSubmodule ≤ c.secondSpace.toSubmodule := by
  rintro _ ⟨v,_,rfl⟩
  exact v.property

theorem Configuration.map_second_invariants :
    (Representation.invariants c.secondAction).map c.secondSpace.toSubmodule.subtype =
      ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact (c.second_invariants_iff v).mp hv
  · intro v hv
    exact ⟨⟨v,c.invariants_le_second hv⟩,
      (c.second_invariants_iff _).mpr hv,rfl⟩

theorem Configuration.lift_supplement (f : FactorModuleConclusion c.secondAction) :
    (c.liftSpace f.space).toSubmodule ⊔ ρ.invariants = c.secondSpace.toSubmodule := by
  change f.space.toSubmodule.map c.secondSpace.toSubmodule.subtype ⊔ _ = _
  rw [← c.map_second_invariants, ← Submodule.map_sup, f.supplement,
    Submodule.map_top, Submodule.range_subtype]

/-- No moved vectors are lost by restricting to the complementary summand. -/
theorem Configuration.map_second_moved :
    (moved c.secondAction ⊤).map c.secondSpace.toSubmodule.subtype = moved ρ c.second := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨b,_,v,_,rfl⟩
    exact Submodule.subset_span ⟨b,b.property,v,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,_,rfl⟩
    have hv : v ∈ c.firstSpace.toSubmodule ⊔ c.secondSpace.toSubmodule := by
      rw [c.decomposition.sup_eq_top]; trivial
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
    let b' : c.second := ⟨b,hb⟩
    let w' : c.secondSpace := ⟨w,hw⟩
    refine ⟨c.secondAction b' w' - w',Submodule.subset_span
      ⟨b',Subgroup.mem_top _,w',Submodule.mem_top,rfl⟩,?_⟩
    have hbu : ρ b u = u := c.cross_fixed hu b'
    change ρ b w - w = ρ b (u+w) - (u+w)
    rw [map_add,hbu]
    abel

/-- The original quotient map on the fixed complement. -/
private noncomputable def Configuration.quotientMap : c.secondSpace.toSubmodule →ₗ[ZMod 2] (V ⧸ ρ.invariants) :=
  ρ.invariants.mkQ.comp c.secondSpace.toSubmodule.subtype

private theorem Configuration.quotientMap_kernel :
    Representation.invariants c.secondAction = c.quotientMap.ker := by
  ext v
  rw [c.second_invariants_iff]
  exact (Submodule.Quotient.mk_eq_zero ρ.invariants).symm

/-- A quotient embedding, not an abstract vector-space isomorphism. -/
private noncomputable def Configuration.quotientEmbedding :
    (c.secondSpace.toSubmodule ⧸ Representation.invariants c.secondAction) →ₗ[ZMod 2]
      (V ⧸ ρ.invariants) :=
  (Representation.invariants c.secondAction).liftQ c.quotientMap c.quotientMap_kernel.le

private theorem quotientEmbedding_injective : Function.Injective c.quotientEmbedding := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ c.quotientMap_kernel

/-- Its image is precisely the quotient image of the included submodule. -/
noncomputable def Configuration.factorImageEquiv (U : Subrepresentation c.secondAction) :
    ActionEquiv (((fixed c.secondAction).quotientImage U).toRepresentation.comp
      (⊤ : Subgroup c.second).subtype)
      (((fixed ρ).quotientImage (c.liftSpace U)).toRepresentation.comp c.second.subtype) := by
  let Q := (fixed c.secondAction).quotientImage U
  let R := (fixed ρ).quotientImage (c.liftSpace U)
  let f : Q.toSubmodule →ₗ[ZMod 2] R.toSubmodule :=
    { toFun := fun v => ⟨c.quotientEmbedding v.val,by
        obtain ⟨w,hw,he⟩ := v.property
        rw [← he]
        exact ⟨w,⟨w,hw,rfl⟩,rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hi : Function.Injective f := by
    intro v w h
    exact Subtype.ext (quotientEmbedding_injective c (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    rintro ⟨q,v,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨⟨(Representation.invariants c.secondAction).mkQ w,⟨w,hw,rfl⟩⟩,rfl⟩
  refine ⟨Subgroup.topEquiv,LinearEquiv.ofBijective f ⟨hi,hs⟩,?_⟩
  intro g v
  apply Subtype.ext
  change c.quotientEmbedding (Q.toRepresentation g v).val =
      (fixed ρ).quotientRepresentation (g : c.second) (c.quotientEmbedding v.val)
  obtain ⟨w,hw,he⟩ := v.property
  have hv : v = (⟨(Representation.invariants c.secondAction).mkQ w,⟨w,hw,rfl⟩⟩ : Q) :=
    Subtype.ext he.symm
  subst v
  rfl

end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
