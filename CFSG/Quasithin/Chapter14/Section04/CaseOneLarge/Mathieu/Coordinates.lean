module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Geometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit

/-!
# Compatible Sylow coordinates for the original Mathieu action

Sylow conjugacy changes the actual quotient isomorphism by an inner
automorphism. Applying the same group element to the module coordinates
preserves equivariance and sends the source Sylow subgroup to the native
marked Sylow. Thus the source branch requires no extra Sylow-marking input.

The transport is proved over an abstract target representation before the
native matrix action is substituted, avoiding unnecessary matrix reduction.
Source: Aschbacher--Smith 14.4.12, printed pp.1011--1012.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open LargerDimension LargerDimension.Mathieu
open LargerDimension.Mathieu.ModuleGeometry.Native hiding Group
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

private theorem surjective_sylow_conjugator
    {A D : Type*} [Group A] [Finite A] [Group D] [Finite D]
    (f : A →* D) (hf : Function.Surjective f) (S : Sylow 2 A) (S₀ : Sylow 2 D) :
    ∃ q : D, (S : Subgroup A).map ((MulAut.conj q).toMonoidHom.comp f) = S₀ := by
  let S' : Sylow 2 D := S.mapSurjective hf
  obtain ⟨q,hq⟩ := MulAction.exists_smul_eq D S' S₀
  refine ⟨q,?_⟩
  have hm : (S' : Subgroup D).map (MulAut.conj q).toMonoidHom = S₀ :=
    congrArg Sylow.toSubgroup hq
  simpa only [S', Sylow.coe_mapSurjective, map_map] using hm

private theorem exists_sylow_marking
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (S₀ : Sylow 2 D)
    (δ : D → W ≃ₗ[ZMod 2] W)
    (hδ : ∀ q a w, δ q (σ a w) = σ ((MulAut.conj q) a) (δ q w))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (e : coreQuotient F.H ≃* D)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] W)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      σ (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    ∃ (e' : coreQuotient F.H ≃* D)
      (c' : Additive F.Uhat ≃ₗ[ZMod 2] W),
      (∀ (a : F.H) (w : Additive F.Uhat),
        σ (ActorCatalogue.starProjection F.H e' a) (c' w) =
          c' (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) ∧
      ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
        (ActorCatalogue.starProjection F.H e') = S₀ := by
  have hs : Function.Surjective (ActorCatalogue.starProjection F.H e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 F.H))
  obtain ⟨q,hq⟩ := surjective_sylow_conjugator (ActorCatalogue.starProjection F.H e) hs
    (T.subtype (F.invariant 1)) S₀
  refine ⟨e.trans (MulAut.conj q), c.trans (δ q), ?_, hq⟩
  intro a w
  change σ ((MulAut.conj q) (ActorCatalogue.starProjection F.H e a))
    (δ q (c w)) = δ q
      (c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
  exact (hδ q (ActorCatalogue.starProjection F.H e a) (c w)).symm.trans
    (congrArg (δ q) (he a w))


/-- A simultaneous conjugation of the quotient and module coordinates marks
    the actual Sylow subgroup without imposing an additional hypothesis. -/
theorem exists_mathieu_sylow_marking
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    ∃ (e' : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
      (c' : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space),
      (∀ (a : F.H) (w : Additive F.Uhat),
        ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e' a) (c' w) =
          c' (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) ∧
      ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
        (ActorCatalogue.starProjection F.H e') = markedSylow := by
  exact exists_sylow_marking ActorCatalogue.Native.action markedSylow actionEquiv
    actionEquiv_equivariant F e c he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
