module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.FixedCopy
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Fixed simple copies from a two-group outer action

Conjugation acts on the actual subrepresentations of a normal subgroup.
Inner automorphisms and the relative centralizer preserve every simple type.
When the outer group is a two-group, a Sylow-stable type is therefore stable
under the full group. Clifford generation makes an irreducible ambient
module isotypic for that type. Odd-copy selection then supplies actual
copies fixed by any two-subgroup, with the original representation operators.

Source: Aschbacher–Smith, D.3.9(1), printed pp.199–200, using A.1.42(2).
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
open Subgroup
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]

def normalTypeAction : TypeAction (ρ.comp N.subtype) G where
  conjugate := conjugateSubrepresentationOrderIso ρ N
  one := conjugateSubrepresentationOrderIso_one ρ N
  mul := conjugateSubrepresentationOrderIso_mul ρ N
  same g U W := by
    rw [sameModule_iff_repEquiv, sameModule_iff_repEquiv]
    exact isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff ρ N g U W

def subgroupTypeAction (P : Subgroup G) : TypeAction (ρ.comp N.subtype) P where
  conjugate g := (normalTypeAction ρ N).conjugate g.val
  one := (normalTypeAction ρ N).one
  mul g h := (normalTypeAction ρ N).mul g.val h.val
  same g := (normalTypeAction ρ N).same g.val

theorem fixed_simple_copy [Finite V] (P : Subgroup G) (hP : IsPGroup 2 P)
    (S : Subrepresentation (ρ.comp N.subtype)) (hS : S.toRepresentation.IsIrreducible)
    (hstable : ∀ p : P, SameModule S ((normalTypeAction ρ N).conjugate p S)) :
    ∃ U : Subrepresentation (ρ.comp N.subtype), SameModule S U ∧
      U.toRepresentation.IsIrreducible ∧
      ∀ p : P, U.toSubmodule.map (ρ p) = U.toSubmodule := by
  let c := subgroupTypeAction ρ N P
  obtain ⟨U,_,he,hu,hh⟩ := c.exists_homogeneous_copy hP S hS
  refine ⟨U,he,hu,?_⟩
  intro p
  have hp : p ∈ c.inertia U := by
    rw [← c.inertia_eq_of_sameModule he]
    exact hstable p
  have hf := (c.homogeneous_iff_inertia_fixes U hu).mp hh p hp
  have hs := congrArg Subrepresentation.toSubmodule hf
  exact (conjugateSubrepresentationOrderIso_toSubmodule ρ N p U).symm.trans hs


theorem normalTypeAction_fix_inner (S : Subrepresentation (ρ.comp N.subtype)) (n : N) :
    (normalTypeAction ρ N).conjugate n S = S := by
  apply Subrepresentation.toSubmodule_injective
  rw [show ((normalTypeAction ρ N).conjugate n S).toSubmodule =
    S.toSubmodule.map (ρ n) from conjugateSubrepresentationOrderIso_toSubmodule ρ N n S]
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact S.apply_mem_toSubmodule n hv
  · intro v hv
    refine ⟨ρ (n : G)⁻¹ v,S.apply_mem_toSubmodule n⁻¹ hv,?_⟩
    simp only [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

theorem normal_le_typeInertia (S : Subrepresentation (ρ.comp N.subtype)) :
    N ≤ (normalTypeAction ρ N).inertia S := by
  intro n hn
  change SameModule S ((normalTypeAction ρ N).conjugate n S)
  rw [normalTypeAction_fix_inner ρ N S ⟨n,hn⟩]
  exact SameModule.refl S

theorem centralizer_le_typeInertia (S : Subrepresentation (ρ.comp N.subtype)) :
    centralizer (N : Set G) ≤ (normalTypeAction ρ N).inertia S := by
  intro g hg
  change SameModule S ((normalTypeAction ρ N).conjugate g S)
  let U := (normalTypeAction ρ N).conjugate g S
  have hm : S.toSubmodule.map (ρ g) = U.toSubmodule :=
    (conjugateSubrepresentationOrderIso_toSubmodule ρ N g S).symm
  let e : S.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule :=
    (S.toSubmodule.equivMapOfInjective (ρ g) (apply_bijective ρ g).injective).trans
      (LinearEquiv.ofEq _ _ hm)
  refine ⟨e,?_⟩
  intro n v
  apply Subtype.ext
  change ρ g (ρ n v) = ρ n (ρ g v)
  rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul,hg n n.property]

theorem typeInertia_eq_top_of_outer_two [Finite G]
    (houter : IsPGroup 2 (MulAut.Outer N)) (P : Sylow 2 G)
    (S : Subrepresentation (ρ.comp N.subtype))
    (hP : ∀ p : P, SameModule S ((normalTypeAction ρ N).conjugate p S)) :
    (normalTypeAction ρ N).inertia S = ⊤ := by
  let f : G →* MulAut.Outer N :=
    (QuotientGroup.mk' (MulAut.innerSubgroup N)).comp MulAut.conjNormal
  have hk : f.ker = N ⊔ centralizer (N : Set G) := by
    ext g
    change QuotientGroup.mk' (MulAut.innerSubgroup N) (MulAut.conjNormal g) = 1 ↔ _
    exact (QuotientGroup.eq_one_iff (MulAut.conjNormal g)).trans
      (SetLike.ext_iff.mp (MulAut.conjNormal_comap_innerSubgroup N) g)
  have hf : IsPGroup 2 (G ⧸ f.ker) :=
    (houter.to_subgroup f.range).of_injective
      (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  apply top_unique
  rw [← P.sup_eq_top_of_quotient_isPGroup f.ker hf]
  apply sup_le
  · intro p hp
    exact hP ⟨p,hp⟩
  · rw [hk]
    exact sup_le (normal_le_typeInertia ρ N S) (centralizer_le_typeInertia ρ N S)


theorem restriction_isotypic_of_typeInertia_top [ρ.IsIrreducible]
    (S : Subrepresentation (ρ.comp N.subtype)) (hS : S.toRepresentation.IsIrreducible)
    (hI : (normalTypeAction ρ N).inertia S = ⊤) :
    IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) S.asSubmodule := by
  let := simple_asSubmodule S hS
  apply IsIsotypicOfType.of_isotypicComponent_eq_top
  apply top_unique
  have hgen := iSup_conjugateSubrepresentations_eq_top ρ N inferInstance S hS
  have hh := congrArg Subrepresentation.asSubmodule hgen
  change Subrepresentation.subrepresentationSubmoduleOrderIso
      (⨆ g, conjugateSubrepresentation ρ N S g) = _ at hh
  rw [OrderIso.map_iSup] at hh
  change (⨆ g, (conjugateSubrepresentation ρ N S g).asSubmodule) = ⊤ at hh
  rw [← hh]
  refine iSup_le fun g => ?_
  have he : SameModule S ((normalTypeAction ρ N).conjugate g⁻¹ S) :=
    show g⁻¹ ∈ (normalTypeAction ρ N).inertia S from hI.symm ▸ mem_top _
  have he' : SameModule S (conjugateSubrepresentation ρ N S g) := by
    simpa only [normalTypeAction,conjugateSubrepresentationOrderIso_apply,inv_inv] using he
  exact le_sSup ((sameModule_iff_linearEquiv _ _).mp he'.symm)

end Representation.BinaryOffender.Homogeneous
