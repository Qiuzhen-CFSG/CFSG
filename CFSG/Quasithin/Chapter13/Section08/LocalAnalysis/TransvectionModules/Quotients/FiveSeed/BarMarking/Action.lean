module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Flags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import Theory.GroupAction.SubgroupConjugation

/-!
# Six-letter coordinates for the original natural module

Conjugation constructs the LT-action on the literal elementary subgroup V.
An equivariant natural identification for L places the whole action in the
linear normalizer of the natural A₆ image. The proved intrinsic normalizer
calculation gives the six-letter homomorphism. Its kernel is exactly C_LT(V),
so it descends faithfully to the source barred actor.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.2.5(2), p.796; 13.5.2(3) and 13.5.3, pp.915–916;
and 13.8.6(5), p.948. The original natural-module coordinates remain an
explicit earlier input. No identification with the action on the distinct
five-dimensional K* cover is made, so an outer twist is not discarded.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open BinaryPermutation
variable {G : Type*} [Group G]
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

/-- Conjugation by P on its normalized subgroup V. -/
def conjugationAut (P V : Subgroup G) (hn : P ≤ normalizer (V : Set G)) : P →* MulAut V :=
  let _ := conjMulDistribMulActionOfLeNormalizer P V hn
  MulDistribMulAction.toMulAut P V

/-- The actual conjugation action on the binary vector space underlying V. -/
def conjugationRepresentation (P V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set G)) : Representation (ZMod 2) P (Additive V) where
  toFun p := (conjugationAut P V hn p).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul ((conjugationAut P V hn 1) v.toMul) = v
    rw [map_one]
    rfl
  map_mul' p q := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul ((conjugationAut P V hn (p * q)) v.toMul) = _
    rw [map_mul]
    rfl

theorem conjugationRepresentation_apply (P V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set G)) (p : P) (v : Additive V) :
    ((conjugationRepresentation P V hn p v).toMul : G) = p * (v.toMul : G) * (p : G)⁻¹ := rfl

theorem conjugationRepresentation_kernel (P V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set G)) :
    (conjugationRepresentation P V hn).ker = actorKernel P V := by
  ext p
  constructor
  · intro hp v hv
    have h := congrArg (fun f : Module.End (ZMod 2) (Additive V) =>
      ((f (Additive.ofMul ⟨v,hv⟩)).toMul : G)) hp
    change (p : G) * v * (p : G)⁻¹ = v at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hp
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (p : G) * (v.toMul : G) * (p : G)⁻¹ = (v.toMul : G)
    have hc : (v.toMul : G) * (p : G) = (p : G) * (v.toMul : G) := hp v.toMul v.toMul.property
    rw [← hc, mul_inv_cancel_right]

/-- Extend the prescribed original natural L-action by the intrinsic normalizer
calculation, preserving its coordinates and identifying the exact kernel. -/
theorem natural_extension (P L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hLP : L ≤ P) (hPL : P ≤ normalizer (L : Set G))
    (hPV : P ≤ normalizer (V : Set G))
    (α : L →* alternatingGroup (Fin 6)) (hα : Function.Surjective α)
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ (l : L) (v : Additive V),
      e (conjugationRepresentation P V hPV (inclusion hLP l) v) =
        alternatingNaturalRepresentation (Fin 6) (α l) (e v)) :
    ∃ f : P →* Equiv.Perm (Fin 6),
      (∀ l : L, f (inclusion hLP l) = (α l).val) ∧
      (∀ p v, e (conjugationRepresentation P V hPV p v) =
        naturalRepresentation (Fin 6) (f p) (e v)) ∧
      f.ker = actorKernel P V := by
  let ρ := conjugationRepresentation P V hPV
  let c := LinearMap.GeneralLinearGroup.congrLinearEquiv e
  let γ : P →* LinearGroup := c.toMonoidHom.comp ρ.asGroupHom
  have hγL (l : L) : γ (inclusion hLP l) = alternatingHom (α l) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change e (ρ (inclusion hLP l) (e.symm v)) = alternatingAction (α l) v
    simpa using he l (e.symm v)
  have hmap : (L.subgroupOf P).map γ = alternatingImage := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact ⟨α ⟨l, hl⟩, (hγL ⟨l, hl⟩).symm⟩
    · rintro _ ⟨a, rfl⟩
      obtain ⟨l, rfl⟩ := hα a
      exact ⟨inclusion hLP l, l.property, hγL l⟩
  let : (L.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPL
  have hγmem (p : P) : γ p ∈ symmetricImage := by
    rw [← normalizer_alternatingImage, ← hmap]
    apply (L.subgroupOf P).le_normalizer_map γ
    exact ⟨p, by rw [normalizer_eq_top]; trivial, rfl⟩
  let γ' : P →* symmetricImage := γ.codRestrict symmetricImage hγmem
  let eS : Symmetric ≃* symmetricImage := MonoidHom.ofInjective symmetricHom_injective
  let f : P →* Symmetric := eS.symm.toMonoidHom.comp γ'
  have hsf (p : P) : symmetricHom (f p) = γ p :=
    congrArg Subtype.val (eS.apply_symm_apply (γ' p))
  have hfL (l : L) : f (inclusion hLP l) = (α l).val := by
    apply symmetricHom_injective
    rw [hsf, hγL]
    rfl
  have hact (p : P) (v : Additive V) : e (ρ p v) = symmetricAction (f p) (e v) := by
    have h := congrArg (fun x : LinearGroup => x.val (e v)) (hsf p)
    change symmetricAction (f p) (e v) = e (ρ p (e.symm (e v))) at h
    simpa using h.symm
  refine ⟨f, hfL, hact, ?_⟩
  rw [← conjugationRepresentation_kernel P V hPV]
  ext p
  constructor
  · intro hp
    apply LinearMap.ext
    intro v
    apply e.injective
    rw [hact, show f p = 1 from hp, map_one]
    rfl
  · intro hp
    apply symmetricAction_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [← hact]
    rw [show ρ p = 1 from hp, map_one]
    rfl
/-- Descending the faithful six-letter action uses the literal source bar kernel. -/
def barHom (P V : Subgroup G) (hn : P ≤ normalizer (V : Set G))
    (f : P →* Equiv.Perm (Fin 6)) (hker : f.ker = actorKernel P V) :
    letI := actorKernel_normal P V hn
    (P ⧸ actorKernel P V) →* Equiv.Perm (Fin 6) := by
  let := actorKernel_normal P V hn
  exact QuotientGroup.lift (actorKernel P V) f (by rw [← hker])

theorem barHom_mk (P V : Subgroup G) (hn : P ≤ normalizer (V : Set G))
    (f : P →* Equiv.Perm (Fin 6)) (hker : f.ker = actorKernel P V) (p : P) :
    letI := actorKernel_normal P V hn
    barHom P V hn f hker (QuotientGroup.mk' _ p) = f p := rfl

theorem barHom_injective (P V : Subgroup G) (hn : P ≤ normalizer (V : Set G))
    (f : P →* Equiv.Perm (Fin 6)) (hker : f.ker = actorKernel P V) :
    letI := actorKernel_normal P V hn
    Function.Injective (barHom P V hn f hker) := by
  let := actorKernel_normal P V hn
  apply (barHom P V hn f hker).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (actorKernel P V) a
  apply (QuotientGroup.eq_one_iff p).mpr
  rw [← hker]
  exact ha
/-- Coordinates for the original natural L-module. This is the mathematical
content to be supplied by 13.5.2(3), not coordinates on the K* cover. -/
structure NaturalCoordinates (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) where
  action : L →* alternatingGroup (Fin 6)
  surjective : Function.Surjective action
  equiv : Additive V ≃ₗ[ZMod 2] natural (Fin 6)
  conjugation : ∀ (l : L) (v : V),
    equiv (Additive.ofMul ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (hn l.property) v).mp v.property⟩) =
    alternatingNaturalRepresentation (Fin 6) (action l) (equiv (Additive.ofMul v))

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking

end
