module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.CentralKernel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.CentralAction
import Mathlib.Tactic

/-!
# Nontrivial component action below the natural eight-point quotient

Let W be a subrepresentation of the actual conjugation representation on
Ũ_H = U_H/V₁, whose quotient is the natural module for a specified H* ≃ S₈
carrying K* onto A₈. If K centralizes W, the central-kernel bridge gives
C_{Ũ_H}(K)=W. The generation equality U_H=[U_H,K] from 13.8.21 identifies
the literal image Ũ_K of that commutator with all of Ũ_H. The first
isomorphism theorem then constructs the natural action on
Ũ_K/C_{Ũ_K}(K), with equivariance checked on every representative.

The relative C-component hypothesis supplies the actual equivalence
K/O₂(K) ≃ K*. Composing it with the specified permutation marking makes
the natural section compatible with the intrinsic component quotient.
Applying universal 13.7.6(3) forces n=6 or n=7, contradicting n=8. Thus an
explicit element of K* moves a vector of W.

This conditional helper takes the compatible natural quotient and the genuine
universal earlier implication as inputs. Their construction and source-theorem
assembly belong to the respective owners. No splitting or centralization of W
is an input to the exported theorem, and no arbitrary chief factor replaces Ũ_K.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, 13.7.6(3), printed pp.938–939, and the proof of
13.8.25, printed pp.959–960 (PDF pp.976–977).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.CentralAction

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.CentralAction

private theorem naturalSection_of_eightNatural_generated
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (W : Subrepresentation ρ)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hnatural : IsEightNatural W.quotientRepresentation eH)
    (hW : ∀ k ∈ K, ∀ w : W.toSubmodule, W.toRepresentation k w = w)
    (S : Submodule (ZMod 2) E) (hS : S = ⊤)
    {J : Type*} [Group J] (a : J →* H) (π : J →* Equiv.Perm (Fin 8))
    (hπ : ∀ j, π j = eH (a j)) : NaturalSection ρ S K a 8 π := by
  have hf := fixedSpace_eq_of_centralized_submodule ρ W K hW
    (eightNatural_fixedSpace_eq_bot W.quotientRepresentation eH K hK hnatural)
  obtain ⟨e, he⟩ := hnatural
  let p : S →ₗ[ZMod 2] natural (Fin 8) :=
    e.toLinearMap.comp (W.toSubmodule.mkQ.comp S.subtype)
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨q, rfl⟩ := e.surjective v
    obtain ⟨u, rfl⟩ := W.toSubmodule.mkQ_surjective q
    exact ⟨⟨u, hS.ge Submodule.mem_top⟩, rfl⟩
  have hk : (fixedSpace ρ K).comap S.subtype = p.ker := by
    ext s
    change s.val ∈ fixedSpace ρ K ↔ e (W.toSubmodule.mkQ s) = 0
    rw [hf, e.map_eq_zero_iff]
    exact (Submodule.Quotient.mk_eq_zero _).symm
  let f := (Submodule.quotEquivOfEq _ _ hk).trans
    (p.quotKerEquivOfSurjective hp)
  refine ⟨fun _ _ => hS.ge Submodule.mem_top, f, ?_⟩
  intro j s
  change e (W.quotientRepresentation (a j) (W.toSubmodule.mkQ s)) =
    naturalRepresentation _ (π j) (e (W.toSubmodule.mkQ s))
  rw [he, hπ]

variable {G : Type*} [Group G] [Finite G]
variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

omit [Finite G] in
private theorem commutatorImage_eq_top (K : Subgroup G)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆) :
    commutatorImage H V₃ V₁ K = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ :=
    QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  exact ⟨u, hgen ▸ u.property, hu⟩

/-- A component element moves a vector of W when the quotient is the
compatible natural eight-point module. The earlier universal implication is
applied to the literal image of [U_H,K], with its quotient by fixed vectors. -/
theorem nontrivial_on_submodule
    (L L₁ T G₁ M K : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (hKalt : (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (W : Subrepresentation ρ)
    (hnatural : IsEightNatural W.quotientRepresentation eH)
    (h1376 : AlternatingNaturalImplication L L₁ T G₁ M ρ) :
    ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w := by
  by_contra! hW
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 8) :=
    ((Components.componentStarEquiv H K hKH hK).trans
      ((Source.starImage H K).equivMapOfInjective eH.toMonoidHom eH.injective)).trans
        (MulEquiv.subgroupCongr hKalt)
  have heK (k : K) : alternatingHom K eK k = eH (starHom K hKH k) := by
    change eH ((Components.componentStarEquiv H K hKH hK
      (QuotientGroup.mk' (pCore 2 K) k)) : Source.Hstar H) = _
    rw [Components.componentStarEquiv_mk]
    rfl
  have hnat := naturalSection_of_eightNatural_generated ρ W eH
    (Source.starImage H K) hKalt hnatural hW
    (commutatorImage H V₃ V₁ K) (commutatorImage_eq_top K hgen)
    (starHom K hKH) (alternatingHom K eK) heK
  obtain ⟨_, _, _, h6 | h7⟩ := h1376 hH hV₁ hρ K hKH hK 8 eK hnat
  · omega
  · omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.CentralAction
