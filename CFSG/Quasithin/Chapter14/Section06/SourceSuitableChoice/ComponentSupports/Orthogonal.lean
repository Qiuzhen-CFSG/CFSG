module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.OriginalAction

/-!
# The original-action orthogonal lift supplies suitability

Apply I.2.3 to the central cover over the actual normal component image L
in the acting quotient J. The map from the original support actor A retains
both its component image and its Sylow image. In particular the universal
cover and its cohomology dimension concern L, not an unquotiented component
with a possibly nontrivial two-core.

The resulting vector is fixed by the Sylow image and moved by L. The exact
binary section lifts it to W, and the separated support geometry proves
(U0)--(U3) for H=Mc. The orthogonal geometry and model markings remain explicit
inputs. This does not assert the source component classification or construct
its supports, and permits the fixed radical of the five-dimensional A6 cover.

Source: Aschbacher--Smith, I.2.3, printed p.413, and the vector choice before
14.6.24, printed p.1038. Relevant model inputs are in
`ModuleCovers/SymplecticFour/SylowFlag.lean` and its `Stabilizers` extension.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
open Representation.BinaryOffender Module
variable {G : Type*} [Group G] [Finite G]
variable {J : Type*} [Group J] [Finite J]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable {N U V : Type*}
  [AddCommGroup N] [Module (ZMod 2) N] [Nontrivial N] [FiniteDimensional (ZMod 2) N]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Apply the genuine I.2.3 lift and supply all (U0)--(U3) on the original W/Z.
The model producer must supply the orthogonal geometry and the marking of
S as the actual Sylow image; no fixed-free condition on the cover is assumed. -/
theorem source_exists_of_orthogonal_cover
    (K W S A : Subgroup G) (π : A →* J) (L : Subgroup J) [L.Normal]
    (hKimage : (K.subgroupOf A).map π = L) (hSA : S ≤ A)
    (d : Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    (η : Representation (ZMod 2) J N)
    (ρ : Representation (ZMod 2) L N)
    (σ : Representation (ZMod 2) L U)
    (hρ : ∀ k : L, ∀ v, η k v = ρ k v)
    (p : σ.IntertwiningMap ρ)
    (hp : IsCover (restrictCoverMap (k := ZMod 2) p))
    (hd : finrank (ZMod 2) (p.toLinearMap.restrictScalars (ZMod 2)).ker =
      finrank (ZMod 2) (H1 (restrictScalars (k := ZMod 2) ρ).dual))
    (hscalar : HasScalarCommutant ρ)
    (B : LinearMap.BilinForm (ZMod 2) N) (hB : B.Nondegenerate)
    (hBinv : ∀ k v w, B (ρ k v) (ρ k w) = B v w)
    (Q : QuadraticForm (ZMod 2) U) (hQ : ∀ k u, Q (σ k u) = Q u)
    (hpolar : ∀ u v, Q.polarBilin u v = B (p u) (p v))
    (r : U) (hr : p r = 0) (hQr : Q r ≠ 0)
    (haniso : ∀ u, p u = 0 → Q u = 0 → u = 0)
    (hfixed : fixed (restrictScalars (k := ZMod 2) ρ) = ⊥)
    (τ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection A W (centralInvolutions T) (τ.comp π))
    (q : τ.IntertwiningMap η) (hq : IsCover q)
    (line : Submodule (ZMod 2) N) (hne : line ≠ ⊥)
    (hisotropic : ∀ v ∈ line, ∀ w ∈ line, B v w = 0)
    (S₀ : Sylow 2 J) (hS : (S.subgroupOf A).map π = (S₀ : Subgroup J))
    (hline : S₀.toSubgroup ≤ subspaceStabilizer η (line.restrictScalars (ZMod 2)))
    [IsIrreducible (stabilizerRepresentation η (line.restrictScalars (ZMod 2)))] :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  obtain ⟨⟨v,_,hmove,hfix⟩,_,_⟩ :=
    ChapterI.ModuleCovers.OriginalAction.fixed_point_and_normalizer_centrality
      L η ρ σ hρ p hp hd hscalar B hB hBinv Q hQ hpolar
      r hr hQr haniso hfixed τ q hq line hne hisotropic S₀ hline
  have hmove' : v ∉ fixed ((τ.comp π).comp (K.subgroupOf A).subtype) := by
    intro hv
    apply hmove
    intro l
    obtain ⟨k,hk,hkl⟩ :=
      show (l : J) ∈ (K.subgroupOf A).map π from hKimage.symm ▸ l.property
    have he := hv (⟨k,hk⟩ : K.subgroupOf A)
    change τ (π k) v = v at he
    rwa [hkl] at he
  apply source_exists_of_section_vector hG T hempty hM hunique hmany hcard e hab
    K W S A d (τ.comp π) c hSA v _ hmove'
  intro s hs
  have hs' : π ⟨s,hSA hs⟩ ∈ (S₀ : Subgroup J) :=
    hS ▸ mem_map_of_mem π (show (⟨s,hSA hs⟩ : A) ∈ S.subgroupOf A from hs)
  exact hfix ⟨π ⟨s,hSA hs⟩,hs'⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
