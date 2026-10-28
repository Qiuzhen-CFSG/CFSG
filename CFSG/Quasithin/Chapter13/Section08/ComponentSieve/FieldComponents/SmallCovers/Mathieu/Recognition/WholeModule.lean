module
public import Theory.Representation.BinaryOffender.StrictCentralQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.NativeSource
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The whole moved M22 module has an irreducible central quotient

A noncentral action of a group with generalized Fitting subgroup M22 is
faithful: its kernel centralizes the component, whose centralizer is trivial.
The native no-FF theorem gives a strict displacement bound for every such
section. Restrict the original quadratic actor and component to their join.
That overgroup still has generalized Fitting subgroup M22. The strict section
bound then proves that the entire fully moved module belongs to Irr⁺, retaining
the original central quotient and allowing a nonzero central subspace.

This discharges the Mathieu specialization of the F.9.18 selection used in
13.8.21(2). It needs no universal F.9.18 classification premise. The original
source adapter supplies full movement and the quadratic actor.
Source: Aschbacher–Smith, F.9.18(7), p.326, and 13.8.21(2), p.956.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.NativeSource
universe u
variable {D : Type u} [Group D] [Finite D]
  (e : generalizedFitting D ≃* Sporadic.Mathieu.M22)
include e

theorem noncentral_faithful {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (hn : ¬ generalizedFitting D ≤ σ.ker) :
    Function.Injective σ := by
  let : IsQuasisimple (generalizedFitting D) := ModelSieve.SectionImages.quasisimple e
  have hcomp : IsComponent D (generalizedFitting D) :=
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,inferInstance⟩
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  rcases hcomp.normal_dichotomy σ.ker with h | h
  · exact (hn h).elim
  · have hc := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)
    exact bot_unique (hc.trans (ModelSieve.SectionImages.centralizer_fitting_eq_bot e).le)

theorem strict_noncentral_bound (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) D W) (hn : ¬ generalizedFitting D ≤ σ.ker) :
    rank A < fixedCodim σ A := by
  have hno := noFaithfulFF D W σ hD (noncentral_faithful e σ hn) ⟨e⟩
  exact lt_of_not_ge (fun hb => hno ⟨A,hA,hb⟩)

theorem whole_isIrrPlus {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (hfull : subspaceCommutator ρ ⊤ (generalizedFitting D) = ⊤)
    (hn : ¬ generalizedFitting D ≤ ρ.ker)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) : IsIrrPlus ρ (generalizedFitting D) ⊤ := by
  let K := generalizedFitting D
  let J := K ⊔ A
  let K₀ := K.subgroupOf J
  let A₀ := A.subgroupOf J
  let σ := ρ.comp J.subtype
  have hKJ : K ≤ J := le_sup_left
  have hAJ : A ≤ J := le_sup_right
  have hfit : generalizedFitting J = K₀ := ModelSieve.SectionImages.overgroup_fitting e J hKJ
  let e₀ : K₀ ≃* Sporadic.Mathieu.M22 := (subgroupOfEquivOfLe hKJ).trans e
  let eJ : generalizedFitting J ≃* Sporadic.Mathieu.M22 :=
    (MulEquiv.subgroupCongr hfit).trans e₀
  let : IsQuasisimple K₀ := ModelSieve.SectionImages.quasisimple e₀
  let : IsElementaryAbelian 2 A := hA.2
  have hA₀ : IsElementaryTwo A₀ := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAJ⟩
    intro he
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAJ,show A.subgroupOf J = ⊥ from he,Subgroup.map_bot]
  have hgen : K₀ ⊔ A₀ = ⊤ := by
    rw [← subgroupOf_sup hKJ hAJ]
    exact subgroupOf_self J
  have hq₀ : IsQuadratic σ A₀ := fun a ha b hb v => hq a ha b hb v
  have hb₀ : fixedCodim σ A₀ ≤ 2 * rank A₀ := by
    rw [fixedCodim_subgroupOf ρ hAJ,rank_subgroupOf hAJ]
    exact hb
  have hAC : A₀ ⊓ centralizer (K₀ : Set J) = ⊥ := by
    rw [← hfit,ModelSieve.SectionImages.centralizer_fitting_eq_bot eJ,inf_bot_eq]
  have hfull₀ : subspaceCommutator σ ⊤ K₀ = ⊤ := by
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKJ]
    exact hfull
  have hn₀ : ¬ K₀ ≤ σ.ker := by
    intro hk
    apply hn
    intro k hkK
    exact hk (show (⟨k,hKJ hkK⟩ : J) ∈ K₀ from hkK)
  have hi := top_isIrrPlus_of_strict_sections σ K₀
    (ModelSieve.SectionImages.center_eq_bot e₀) A₀ hgen hA₀ hq₀ hb₀ hAC hfull₀ hn₀
    (fun W _ _ _ τ ht => strict_noncentral_bound eJ (hD.subgroup J) A₀ hA₀ W τ
      (by rwa [hfit]))
  exact (IsIrrPlus.subgroupOf_iff ρ K J hKJ ⊤).mp hi
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.NativeSource
