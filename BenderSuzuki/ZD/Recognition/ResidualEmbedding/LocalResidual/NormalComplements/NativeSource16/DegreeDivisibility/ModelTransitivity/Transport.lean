module

public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Transport of root fusion and Sylow normalizer control

Fusion of nonidentity elements passes through homomorphisms. Sylow
conjugacy aligns a concrete root with the prescribed Sylow of an isomorphic
group. When omega lies in the Sylow center, Burnside fusion supplies the
conjugator in the actual Sylow normalizer.

Source: GLS4, Chapter 2, Lemma 16.4(c), using Chapter 4, Lemma 3.2(b,c).
-/

namespace BenderSuzuki.ZD.Source16ModelTransitivity
open Subgroup
variable {G H : Type*} [Group G] [Group H]

public theorem fusion_map (Q : Subgroup G)
    (hQ : ∀ z ∈ Q, z ≠ 1 → ∀ x ∈ Q, x ≠ 1 → IsConj z x)
    (f : G →* H) :
    ∀ z ∈ Q.map f, z ≠ 1 → ∀ x ∈ Q.map f, x ≠ 1 → IsConj z x := by
  rintro _ ⟨z,hz,rfl⟩ hz1 _ ⟨x,hx,rfl⟩ hx1
  exact f.map_isConj (hQ z hz (fun he => hz1 (by rw [he,map_one]))
    x hx (fun he => hx1 (by rw [he,map_one])))

public theorem sylow_omega_fusion_of_equiv [Finite G] [Finite H]
    (e : G ≃* H) (S : Sylow 2 H)
    (hS : ∀ z ∈ omegaOneAmbient (S : Subgroup H), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (S : Subgroup H), x ≠ 1 → IsConj z x)
    (P : Sylow 2 G) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 → IsConj z x := by
  let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S' P
  let f := e.symm.trans (MulAut.conj g)
  have hf : (S : Subgroup H).map f.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup H).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup G) at hh
    change (S : Subgroup H).map
      ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    simpa only [map_map] using hh
  have ho : (omegaOneAmbient (S : Subgroup H)).map f.toMonoidHom =
      omegaOneAmbient (P : Subgroup G) := by
    rw [map_omegaOneAmbient_injective _ f.injective,hf]
  rw [← ho]
  exact fusion_map _ hS f.toMonoidHom

public theorem normalizer_transitive_of_omega_fusion [Finite G] (P : Sylow 2 G)
    (hcenter : omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype)
    (hf : ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 → IsConj z x) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 →
        ∃ g ∈ normalizer (P : Set G), MulAut.conj g z = x := by
  have hC : omegaOneAmbient (P : Subgroup G) ≤ centralizer (P : Set G) := by
    rw [hcenter]
    rintro _ ⟨a,ha,rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨b,hb⟩ : P))
  intro z hz hz1 x hx hx1
  obtain ⟨g,hg⟩ := isConj_iff.mp (hf z hz hz1 x hx hx1)
  obtain ⟨a,ha,he⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer z g⁻¹
    (hC hz) (by simpa only [inv_inv] using hg.symm ▸ hC hx)
  simp only [inv_inv] at he
  refine ⟨a⁻¹,(normalizer (P : Set G)).inv_mem ha,?_⟩
  change a⁻¹ * z * (a⁻¹)⁻¹ = x
  simpa only [inv_inv] using he.symm.trans hg

end BenderSuzuki.ZD.Source16ModelTransitivity
