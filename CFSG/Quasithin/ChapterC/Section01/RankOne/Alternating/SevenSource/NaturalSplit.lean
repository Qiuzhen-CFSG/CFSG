module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalThompsonBaumann

/-!
# Natural S₇ actions cannot have an idempotent Baumann Sylow

A natural submodule with the same fixed codimensions as the full module
makes the Baumann image an eight-group. A Sylow image in S₇ has order
sixteen, so the original Sylow is not its own Baumann subgroup. The supplied
group and module markings are transported together through the literal
conjugation quotient.
Source: Aschbacher--Smith B.2.20, C.1.24, 13.2.12, pp.82,131,882.
-/
public section
open scoped IsMulCommutative
open Subgroup Stellmacher Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
variable {G : Type*} [Group G] [Finite G]

/-- Fixed summands are allowed: only the natural embedding and the literal
fixed codimensions are needed for the original Sylow contradiction. -/
theorem natural_not_baumann_sylow
    {E : Type*} [Group E] [Finite E]
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* E) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (e : E ≃* Equiv.Perm (Fin 7))
    (T : Sylow 2 G) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker)
    (hB : ChapterB.baumann (T : Subgroup G) = (T : Subgroup G))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation U q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) (A.map e.toMonoidHom))
    (s : natural (Fin 7) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s)
    (he : ∀ g v, s (naturalRepresentation (Fin 7) (e g) v) =
      NormalElementaryQuotient.representation U q hq hk g (s v)) : False := by
  let q' := e.toMonoidHom.comp q
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hker : q'.ker = q.ker := MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective
  have hk' : q'.ker = centralizer (U : Set G) := hker.trans hk
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let σ := NormalElementaryQuotient.representation U q' hq' hk'
  have hcomp : σ.comp e.toMonoidHom = ρ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨g,rfl⟩ := hq g
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((σ (q' g) v).toMul:G) = ((ρ (q g) v).toMul:G)
    rw [NormalElementaryQuotient.representation_apply,NormalElementaryQuotient.representation_apply]
  have hc' (A : Subgroup (Equiv.Perm (Fin 7))) :
      fixedCodim σ A = fixedCodim (naturalRepresentation (Fin 7)) A := by
    have h := hc (A.map e.symm.toMonoidHom)
    change fixedCodim ρ _ = _ at h
    rw [←hcomp,fixedCodim,fixedSpace_comp_map] at h
    have hm : (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := e.mapSubgroup.apply_symm_apply A
    rw [hm] at h
    exact h
  have he' (g : Equiv.Perm (Fin 7)) (v : natural (Fin 7)) :
      s (naturalRepresentation (Fin 7) g v) = σ g (s v) := by
    obtain ⟨g,rfl⟩ := e.surjective g
    rw [he]
    exact congrArg (fun r : Representation (ZMod 2) E (Additive U) => r g (s v)) hcomp.symm
  obtain ⟨a,_,_,hcard⟩ := natural_thompson_baumann_images_of_natural_coordinates
    U T hUT q' hq' hk' hc' (by rwa [hker]) s hs he'
  rw [hB] at hcard
  let P := T.mapSurjective hq'
  have hP : Nat.card P = 16 := by
    rw [Nat.card_congr (P.equiv
      Representation.AlternatingSevenConjugatePair.ElementaryGeometry.standardSylow).toEquiv]
    exact Representation.AlternatingSevenConjugatePair.ElementaryGeometry.sylowTwo_card
  change Nat.card P = 8 at hcard
  omega
end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
