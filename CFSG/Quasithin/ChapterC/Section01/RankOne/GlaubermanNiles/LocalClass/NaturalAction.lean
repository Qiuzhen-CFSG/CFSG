module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Elementary
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.GeneralizedFitting.FaithfulRestriction

/-!
# The faithful natural quotient action in C.1.17

Ambient conjugation preserves both the moved subgroup and its fixed subgroup.
It descends through the literal action kernel, then the source module
isomorphism supplies binary coordinates on the quotient. Its restriction to
F*(H*) is exactly the given natural action. Faithfulness on F*(H*) therefore
proves faithfulness on all of H*. Consequently the centralizer of the moved
subgroup equals the original centralizer of V.

This constructs the full action and the actual surjective coordinate map from
the marking in C.1.17; neither is supplied as a new premise. The derived
PSL₂(2) actor is retained in the smallest-field case.

Source: Aschbacher–Smith C.1.17, printed p.126, and the generalized-Fitting
self-centralizer theorem.
-/

public section

open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}

theorem exists_moved_quotient_action :
    ∃ α : LocalStar e →* MulAut (MovedModule e),
      ∀ (g : H) (w : moved e), α (QuotientGroup.mk' (localKernel e) g)
        (QuotientGroup.mk' (movedFixed e) w) =
        QuotientGroup.mk' (movedFixed e) (movedConjugate e g w) := by
  obtain ⟨γ,hγ⟩ := exists_quotient_conjugation_action (⊤ : Subgroup H) (moved e)
    (centralizer (actorLift e : Set H)) le_normalizer_of_normal
    le_normalizer_of_normal (movedFixed_normal e)
  let δ : H →* MulAut (MovedModule e) := γ.comp Subgroup.topEquiv.symm.toMonoidHom
  have hδ (g : H) (w : moved e) :
      δ g (QuotientGroup.mk' (movedFixed e) w) =
      QuotientGroup.mk' (movedFixed e) (movedConjugate e g w) := hγ ⟨g,mem_top g⟩ w
  let q := QuotientGroup.mk' (localKernel e)
  have hq := QuotientGroup.mk'_surjective (localKernel e)
  have hkill : q.ker ≤ δ.ker := by
    intro g hg
    have hg' : g ∈ localKernel e := by simpa [q] using hg
    apply MonoidHom.mem_ker.mpr
    ext v
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (movedFixed e) v
    rw [hδ]
    change QuotientGroup.mk' (movedFixed e) _ = QuotientGroup.mk' (movedFixed e) w
    congr 1
    apply Subtype.ext
    change g * (w : H) * g⁻¹ = w
    rw [← hg' w (moved_le_localV e w.property),mul_inv_cancel_right]
  let α : LocalStar e →* MulAut (MovedModule e) := q.liftOfSurjective hq ⟨δ,hkill⟩
  refine ⟨α,?_⟩
  intro g w
  have he : α (q g) = δ g := q.liftOfRightInverse_comp_apply _ _ _ g
  rw [he]
  exact hδ g w

variable {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

theorem InLocalClass.exists_moved_representation (h : InLocalClass e) (m : NaturalModel e F) :
    let _ : IsElementaryAbelian 2 (moved e) := by
      let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
      exact IsElementaryAbelian.of_le (moved_le_localV e)
    ∃ (ρ : Representation (ZMod 2) (LocalStar e) (Fin 2 → F))
      (f : Additive (moved e) →ₗ[ZMod 2] (Fin 2 → F)),
      Function.Surjective f ∧
      (∀ w : moved e, f (Additive.ofMul w) =
        (m.moduleIso (QuotientGroup.mk' (movedFixed e) w)).toAdd) ∧
      (∀ (g : H) (w : moved e), f (Additive.ofMul (movedConjugate e g w)) =
        ρ (QuotientGroup.mk' (localKernel e) g) (f (Additive.ofMul w))) := by
  let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let _ : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  dsimp only
  obtain ⟨α,hα⟩ := exists_moved_quotient_action (e := e)
  let β : LocalStar e →* MulAut (Multiplicative (Fin 2 → F)) :=
    (MulAut.congr m.moduleIso).toMonoidHom.comp α
  let ρ : Representation (ZMod 2) (LocalStar e) (Fin 2 → F) := {
    toFun := fun g => (AddMonoidHom.toMultiplicative.symm (β g).toMonoidHom).toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      change β 1 (Multiplicative.ofAdd v) = Multiplicative.ofAdd v
      rw [map_one]
      rfl
    map_mul' := by
      intro g k
      apply LinearMap.ext
      intro v
      change β (g*k) (Multiplicative.ofAdd v) = β g (β k (Multiplicative.ofAdd v))
      rw [map_mul]
      rfl }
  let f : Additive (moved e) →ₗ[ZMod 2] (Fin 2 → F) :=
    (m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (movedFixed e))).toAdditiveLeft.toZModLinearMap 2
  refine ⟨ρ,f,?_,fun _ => rfl,?_⟩
  · intro v
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (movedFixed e)
      (m.moduleIso.symm (Multiplicative.ofAdd v))
    refine ⟨Additive.ofMul w,?_⟩
    change (m.moduleIso (QuotientGroup.mk' (movedFixed e) w)).toAdd = v
    rw [hw,m.moduleIso.apply_symm_apply]
    rfl
  · intro g w
    change (m.moduleIso (QuotientGroup.mk' (movedFixed e) (movedConjugate e g w))).toAdd =
      (m.moduleIso (α (QuotientGroup.mk' (localKernel e) g)
        (m.moduleIso.symm (m.moduleIso (QuotientGroup.mk' (movedFixed e) w))))).toAdd
    rw [m.moduleIso.symm_apply_apply,hα]
end CFSG.Quasithin.ChapterC.GlaubermanNiles



namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}
    {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

theorem InLocalClass.exists_faithful_natural_action (h : InLocalClass e) (m : NaturalModel e F) :
    let _ : IsElementaryAbelian 2 (moved e) := by
      let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
      exact IsElementaryAbelian.of_le (moved_le_localV e)
    ∃ (ρ : Representation (ZMod 2) (LocalStar e) (Fin 2 → F))
      (f : Additive (moved e) →ₗ[ZMod 2] (Fin 2 → F)),
      Function.Injective ρ ∧ Function.Surjective f ∧
      (∀ w : moved e, f (Additive.ofMul w) =
        (m.moduleIso (QuotientGroup.mk' (movedFixed e) w)).toAdd) ∧
      (∀ (g : H) (w : moved e), f (Additive.ofMul (movedConjugate e g w)) =
        ρ (QuotientGroup.mk' (localKernel e) g) (f (Additive.ofMul w))) ∧
      (∀ (a : generalizedFitting (LocalStar e)) (v : Fin 2 → F),
        ρ a v = Representation.specialLinearNatural 2
          (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (m.actorIso a : PSL(2,F))) v) ∧
      centralizer (moved e : Set H) = localKernel e := by
  let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let _ : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  dsimp only
  obtain ⟨ρ,f,hf,hcoords,hconj⟩ := InLocalClass.exists_moved_representation h m
  have hnat (a : generalizedFitting (LocalStar e)) (v : Fin 2 → F) :
      ρ a v = Representation.specialLinearNatural 2
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (m.actorIso a : PSL(2,F))) v := by
    obtain ⟨w,rfl⟩ := hf v
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (localKernel e) (a : LocalStar e)
    let b : actorLift e := ⟨g,by change QuotientGroup.mk' (localKernel e) g ∈ generalizedFitting (LocalStar e); rw [hg]; exact a.property⟩
    have hb : actorProjection e b = a := Subtype.ext hg
    have he := m.intertwining b w.toMul
    rw [hb] at he
    rw [← hg]
    change ρ (QuotientGroup.mk' (localKernel e) g) (f (Additive.ofMul w.toMul)) = _
    rw [← hconj,hcoords]
    rw [show f w = f (Additive.ofMul w.toMul) from rfl,hcoords]
    exact he
  have hfaith : Function.Injective ρ := by
    apply injective_of_injective_on_generalizedFitting
    intro a b hab
    apply m.actorIso.injective
    apply Subtype.ext
    apply Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm.injective
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    exact (hnat a v).symm.trans ((congrArg (fun z : Module.End (ZMod 2) (Fin 2 → F) => z v) hab).trans (hnat b v))
  refine ⟨ρ,f,hfaith,hf,hcoords,hconj,hnat,?_⟩
  apply le_antisymm ?_ (centralizer_le (moved_le_localV e))
  intro x hx
  change x ∈ localKernel e
  apply (QuotientGroup.eq_one_iff x).mp
  change QuotientGroup.mk' (localKernel e) x = 1
  apply hfaith
  rw [map_one]
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := hf v
  change ρ (QuotientGroup.mk' (localKernel e) x) (f (Additive.ofMul w.toMul)) = f w
  rw [← hconj]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change x * (w.toMul : H) * x⁻¹ = w.toMul
  rw [← hx w.toMul w.toMul.property,mul_inv_cancel_right]

end CFSG.Quasithin.ChapterC.GlaubermanNiles
