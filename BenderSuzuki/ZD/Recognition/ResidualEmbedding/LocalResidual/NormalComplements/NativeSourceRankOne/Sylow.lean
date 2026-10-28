module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Selection
public import Theory.GroupTheory.RelativeSylowNormalizer

/-!
# The actual Sylow subgroup of the selected centralizer

Every Sylow two-subgroup T₁ of C_M(u) contains u, because u is central there.
Two-centrality supplies z in Z∩M centralizing T₁; Sylow maximality puts z
inside T₁. Its presence forces N_G(T₁) into M, so the same T₁ is Sylow in
C_G(u). This proves the Sylow assertion of 16.3(b) and the z-part of (16E).

Source: GLS4, Chapter 2, (16C), (16E), Lemma 16.3(b), Proposition 3.1(d).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem involution_mem_sylow_of_centralizes
    (S : Sylow 2 G) {u : G} (hu : IsInvolution u)
    (hc : ∀ x ∈ (S : Subgroup G), Commute u x) : u ∈ S := by
  have huN : u ∈ normalizer (S : Set G) :=
    _root_.centralizer_le_normalizer (S : Subgroup G) (fun x hx => (hc x hx).symm.eq)
  have hm : u ∈ zpowers u ⊓ normalizer (S : Set G) := ⟨mem_zpowers u,huN⟩
  have hp : IsPGroup 2 (zpowers u) := isPGroup_zpowers_of_involution hu
  have he := hp.inf_normalizer_sylow S
  rw [he] at hm
  exact hm.2

/-- The original T₁ in C_M(u) contains both u and a central distinguished
involution z, and is literally the image of a Sylow subgroup of C_G(u). -/
public theorem involutionCentralizer_sylow_and_marked_center
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u : G} (hu : IsInvolution u) (huM : u ∈ M)
    (S : Sylow 2 (centralizer ({u} : Set G) ⊓ M : Subgroup G)) :
    let B := centralizer ({u} : Set G)
    let H := B ⊓ M
    let T := (S : Subgroup H).map H.subtype
    u ∈ T ∧ ∃ z ∈ Z, z ∈ T ∧ T ≤ centralizer ({z} : Set G) ∧
      ∃ P : Sylow 2 B, (P : Subgroup B).map B.subtype = T := by
  let B := centralizer ({u} : Set G)
  let H := B ⊓ M
  let T := (S : Subgroup H).map H.subtype
  have huH : u ∈ H := ⟨mem_centralizer_singleton_iff.mpr rfl,huM⟩
  have huS : (⟨u,huH⟩ : H) ∈ S := by
    apply involution_mem_sylow_of_centralizes S (IsInvolution.subtype hu huH)
    intro x _
    apply Commute.of_map H.subtype_injective
    exact (mem_centralizer_singleton_iff.mp x.property.1).symm
  have huT : u ∈ T := ⟨⟨u,huH⟩,huS,rfl⟩
  have hTH : T ≤ H := map_subtype_le _
  obtain ⟨z,hz,hzM,hzc⟩ := twoSubgroup_exists_distinguished_centralizer h r T
    (S.isPGroup'.map H.subtype) (hTH.trans inf_le_right)
  have hzH : z ∈ H := ⟨mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hzc huT)).symm,hzM⟩
  have hzS : (⟨z,hzH⟩ : H) ∈ S := by
    apply involution_mem_sylow_of_centralizes S (IsInvolution.subtype (h.involutions z hz) hzH)
    intro x hx
    apply Commute.of_map H.subtype_injective
    exact (mem_centralizer_singleton_iff.mp (hzc ⟨x,hx,rfl⟩)).symm
  have hzT : z ∈ T := ⟨⟨z,hzH⟩,hzS,rfl⟩
  have hn : normalizer (T : Set G) ≤ M := normalizer_le h (hTH.trans inf_le_right) ⟨z,hz,hzT⟩
  exact ⟨huT,z,hz,hzT,hzc,
    exists_sylow_eq_of_relative_normalizer_le ⟨S,rfl⟩ inf_le_left
      (le_inf inf_le_left (inf_le_right.trans hn))⟩

end BenderSuzuki.ZD
