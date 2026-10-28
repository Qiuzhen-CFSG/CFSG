module

public import Theory.SpecificGroups.Suzuki.BorelInvolutionCore
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.Frattini.OmegaProducts

/-!
# Omega geometry for arbitrary Suzuki Sylow subgroups

An actual isomorphism with the matrix Suzuki group can be adjusted by Sylow
conjugacy to carry the standard root group to a prescribed Sylow subgroup.
Its normalizer, first omega and embedded center then transport along the same
map. In particular the omega has order q, whereas the Sylow has order q².

Source: GLS, Volume 4, Chapter 4, Lemma 3.2(b,c), and the concrete root
calculations of Huppert--Blackburn, Finite Groups III, XI.3.1.
-/

namespace BenderSuzuki.MatrixGroups
open Subgroup

variable {G : Type*} [Group G] [Finite G] {m : ℕ}

/-- Align the standard root and its Borel with the prescribed Sylow and normalizer. -/
public theorem suzukiSylow_aligned_equiv (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    ∃ f : SuzukiMatrixGroup m ≃* G,
      (SuzukiRootSubgroup m).map f.toMonoidHom = (P : Subgroup G) ∧
      (SuzukiBorelSubgroup m).map f.toMonoidHom = normalizer (P : Set G) := by
  obtain ⟨S, hS⟩ := suzukiRootSubgroup_isSylow m hm
  let S' : Sylow 2 G := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' P
  let f := e.symm.trans (MulAut.conj g)
  have hP : (SuzukiRootSubgroup m).map f.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup (SuzukiMatrixGroup m)).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup G) at hh
    change (SuzukiRootSubgroup m).map
      ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    simpa only [hS, map_map] using hh
  refine ⟨f, hP, ?_⟩
  rw [← suzukiRootSubgroup_normalizer m hm, map_equiv_normalizer_eq, hP]
  rfl

/-- The first omega of any Suzuki Sylow is its embedded center. -/
public theorem suzukiSylow_omega_eq_center (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype := by
  obtain ⟨f, hP, _⟩ := suzukiSylow_aligned_equiv hm e P
  rw [← hP, ← map_omegaOneAmbient_injective f.toMonoidHom f.injective,
    suzukiRootSubgroup_omega_eq_center m hm,
    map_embeddedCenter _ f.toMonoidHom f.injective]

/-- Its first omega is elementary abelian, with the actual ambient embedding. -/
public theorem suzukiSylow_omega_elementary (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) := by
  obtain ⟨f, hP, _⟩ := suzukiSylow_aligned_equiv hm e P
  rw [← hP, ← map_omegaOneAmbient_injective f.toMonoidHom f.injective]
  let := suzukiRootSubgroup_omega_elementary m hm
  exact IsElementaryAbelian.map _

/-- Its first omega has order q. -/
public theorem suzukiSylow_omega_card (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    Nat.card (omegaOneAmbient (P : Subgroup G)) = 2 ^ (2 * m + 1) := by
  obtain ⟨f, hP, _⟩ := suzukiSylow_aligned_equiv hm e P
  rw [← hP, ← map_omegaOneAmbient_injective f.toMonoidHom f.injective,
    card_map_of_injective f.injective, suzukiRootSubgroup_omega_card m hm]

/-- The full Sylow has order q². -/
public theorem suzukiSylow_card (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    Nat.card P = (2 ^ (2 * m + 1)) ^ 2 := by
  obtain ⟨f, hP, _⟩ := suzukiSylow_aligned_equiv hm e P
  rw [← hP, card_map_of_injective f.injective, suzukiRootSubgroup_card m hm]

/-- The ambient involution-generated subgroup of the normalizer is precisely Ω₁(P). -/
public theorem suzukiSylow_normalizer_involutionCore (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    (involutionCore (normalizer (P : Set G))).map
      (normalizer (P : Set G)).subtype = omegaOneAmbient (P : Subgroup G) := by
  obtain ⟨f, hP, hB⟩ := suzukiSylow_aligned_equiv hm e P
  rw [suzukiBorel_involutionCore_map hm f.toMonoidHom f.injective _ hB,
    map_omegaOneAmbient_injective f.toMonoidHom f.injective, hP]

end BenderSuzuki.MatrixGroups
