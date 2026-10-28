module

public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Frattini.PGroup

/-!
# Exact local inputs for the exceptional A₈ branch

These are the local consequences of the earlier source setup in
Aschbacher–Smith, Lemmas 2.5.19 and 2.5.21–25, used on printed pp.568–569
of the combined 1 March 2004 manuscript. Global simple-QTKE and maximal
local hypotheses stay with the caller; the algebra uses only quasithinness.

The residual is the solvable residual of C_Ki(t), mapped to the ambient
group. The component is relative to C_G(i). Conjugation here is x a x⁻¹,
as in the consuming Fusion module; replace the source's right conjugator
by its inverse when supplying these data. The action of t is an actual
transposition on the fixed A₈ carrier. No dihedral shape, order of S,
normality of Ki, or symmetric-group extension is an incoming hypothesis.

`SmallExtensionModel` describes the outstanding marked carrier construction.
Independently, one must prove C_S(i) ≤ ⟨Ki,i,t⟩. Together these give
`ExtensionModel`, retaining the images of Ki, i and t. Neither construction
is an assumed source theorem; the assembly must discharge both.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction

/-- The earlier local setup and the applicable exceptional outputs of 2.5.19. -/
structure LocalData (G : Type*) [Group G] where
  H : Subgroup G
  K : Subgroup G
  S : Subgroup G
  SC : Subgroup G
  Ki : Subgroup G
  t : G
  i : G
  x : G
  centralizer_t : H = centralizer {t}
  generated : H = K ⊔ S
  modelK : K ≃* alternatingGroup (Fin 6)
  modelKi : Ki ≃* alternatingGroup (Fin 8)
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H).map H.subtype = S
  centralizer_K : SC = S ⊓ centralizer (K : Set G)
  core : SC = H.pCoreIn 2
  t_mem : t ∈ SC
  t_order : orderOf t = 2
  t_central : ∀ s : G, s ∈ S → s * t = t * s
  x_normalizes : x ∈ normalizer (S : Set G)
  disjoint_conjugate : Disjoint SC (SC.map (MulAut.conj x).toMonoidHom)
  frattini_ne : frattini SC ≠ ⊥
  i_mem : i ∈ SC
  i_order : orderOf i = 2
  i_ne_t : i ≠ t
  centralizer_i : centralizer ({(⟨i, i_mem⟩ : SC)} : Set SC) =
    zpowers (⟨i, i_mem⟩ : SC) ⊔ zpowers (⟨t, t_mem⟩ : SC)
  Ki_le_centralizer : Ki ≤ centralizer {i}
  component : Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
    (Ki.subgroupOf (centralizer {i}))
  residual : K = (solvableResidual (Ki ⊓ centralizer ({t} : Set G) : Subgroup G)).map
    (Ki ⊓ centralizer ({t} : Set G)).subtype
  t_action : ∀ k : Ki,
    (modelKi.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (modelKi k)) : G) =
      t * k * t⁻¹
  action : H →* MulAut (alternatingGroup (Fin 6))
  action_surjective : Function.Surjective action
  action_compatible : ∀ (h : H) (k : K),
    (modelK.symm (action h (modelK k)) : G) = (h : G) * k * (h : G)⁻¹
  action_kernel : action.ker = SC.subgroupOf H

namespace LocalData
variable {G : Type*} [Group G]

/-- Ki C_S(i), initially expressed as a join. -/
@[expose] def extension (d : LocalData G) : Subgroup G := d.Ki ⊔ (d.S ⊓ centralizer {d.i})
/-- The source subgroup H₀ = ⟨Ki,i,t⟩. -/
@[expose] def smallExtension (d : LocalData G) : Subgroup G := d.Ki ⊔ zpowers d.i ⊔ zpowers d.t

end LocalData

/-- The actual carrier of C₂ × S₈. -/
abbrev SymmetricExtension := Multiplicative (ZMod 2) × Equiv.Perm (Fin 8)

/-- The marked carrier of H₀ = ⟨Ki,i,t⟩, independently of the larger C_S(i). -/
structure SmallExtensionModel {G : Type*} [Group G] (d : LocalData G) where
  equiv : d.smallExtension ≃* SymmetricExtension
  map_Ki : ∀ (k : d.Ki) (j : d.smallExtension), (j : G) = k →
    equiv j = (1, (d.modelKi k : Equiv.Perm (Fin 8)))
  map_i : ∀ j : d.smallExtension, (j : G) = d.i →
    equiv j = (Multiplicative.ofAdd 1, 1)
  map_t : ∀ j : d.smallExtension, (j : G) = d.t →
    equiv j = (1, Equiv.swap (0 : Fin 8) 1)

/-- A compatible construction result, not a field of the incoming local setup. -/
structure ExtensionModel {G : Type*} [Group G] (d : LocalData G) where
  equiv : d.extension ≃* SymmetricExtension
  generated : d.smallExtension = d.extension
  map_Ki : ∀ (k : d.Ki) (j : d.extension), (j : G) = k →
    equiv j = (1, (d.modelKi k : Equiv.Perm (Fin 8)))
  map_i : ∀ j : d.extension, (j : G) = d.i →
    equiv j = (Multiplicative.ofAdd 1, 1)
  map_t : ∀ j : d.extension, (j : G) = d.t →
    equiv j = (1, Equiv.swap (0 : Fin 8) 1)

/-- Combine the marked carrier and the independently proved generation equality. -/
def ExtensionModel.ofSmall {G : Type*} [Group G] {d : LocalData G}
    (m : SmallExtensionModel d) (h : d.smallExtension = d.extension) : ExtensionModel d where
  equiv := (MulEquiv.subgroupCongr h.symm).trans m.equiv
  generated := h
  map_Ki k j hj := m.map_Ki k (MulEquiv.subgroupCongr h.symm j) hj
  map_i j hj := m.map_i (MulEquiv.subgroupCongr h.symm j) hj
  map_t j hj := m.map_t (MulEquiv.subgroupCongr h.symm j) hj

end CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction
