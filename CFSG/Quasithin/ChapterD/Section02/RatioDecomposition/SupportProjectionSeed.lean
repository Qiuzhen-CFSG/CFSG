module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SupportStabilizerSylow
public import Theory.Representation.BinaryOffender.ProjectedSeed
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Mathlib.GroupTheory.Index
/-!
# The stabilizer span of the projected original seed

For at most two permuted factor supports, a support stabilizer is normal and
supplements the original Sylow subgroup. The ambient fixed seed therefore
already spans under this stabilizer. Projecting along the actor fixed space
recovers a spanning local seed fixed by the restricted Sylow subgroup.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData
omit [FiniteDimensional (ZMod 2) V] in
theorem support_stabilizer_sylow_supplement
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (hc : Nat.card d.Index ≤ 2) (P : Sylow 2 G) (i : d.Index) :
    (P : Subgroup G) ⊔ subspaceStabilizer ρ (c.ambientFactor d i).space = ⊤ := by
  let N := subspaceStabilizer ρ (c.ambientFactor d i).space
  let := c.ambient_space_stabilizer_normal_of_count d π hs hc i
  have hker : π.ker ≤ N := by
    intro g hg
    apply (subspace_map_eq_iff ρ _ _).mp
    rw [hs,show π g = 1 from hg]
    rfl
  have hd : N.index ∣ 2 := by
    apply dvd_trans (Subgroup.index_dvd_of_le hker)
    rw [Subgroup.index_ker]
    apply dvd_trans π.range.card_subgroup_dvd_card
    rw [Nat.card_perm]
    exact (Nat.factorial_dvd_factorial hc).trans (by decide)
  have hq : IsPGroup 2 (G ⧸ N) := IsPGroup.of_card_dvd_pow (n := 1) (by change N.index ∣ 2^1; simpa using hd)
  exact P.sup_eq_top_of_quotient_isPGroup N hq
omit [FiniteDimensional (ZMod 2) V] in
theorem support_stabilizer_fixed_seed_full
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (hc : Nat.card d.Index ≤ 2) (P : Sylow 2 G) (i : d.Index)
    (hcompl : IsCompl (c.ambientFactor d i).space
      (fixedSpace ρ (c.ambientFactor d i).actor))
    (hnormalizes : subspaceStabilizer ρ (c.ambientFactor d i).space ≤
      normalizer ((c.ambientFactor d i).actor : Set G))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ fixedSpace ρ (P : Subgroup G) ∧ ρ g v = w} = ⊤) :
    Homogeneous.orbitSpan ρ (subspaceStabilizer ρ (c.ambientFactor d i).space)
      (fixedSpace ρ ((P : Subgroup G) ⊓
        subspaceStabilizer ρ (c.ambientFactor d i).space) ⊓
          (c.ambientFactor d i).space) = (c.ambientFactor d i).space := by
  classical
  let F := c.ambientFactor d i
  let N := subspaceStabilizer ρ F.space
  let C := fixedSpace ρ F.actor
  have hFC : IsCompl F.space C := hcompl
  let Q := Homogeneous.orbitSpan ρ N (fixedSpace ρ ((P : Subgroup G) ⊓ N) ⊓ F.space)
  let := c.ambient_space_stabilizer_normal_of_count d π hs hc i
  have hgen : N ⊔ (P : Subgroup G) = ⊤ := by
    rw [sup_comm]
    exact c.support_stabilizer_sylow_supplement d π hs hc P i
  have hCN : N ≤ subspaceStabilizer ρ C := fixedSpace_invariant_normalizer ρ hnormalizes
  let pr : V →ₗ[ZMod 2] V := F.space.subtype.comp (F.space.projectionOnto C hFC)
  have hpr (n : N) (v : V) : pr (ρ n v) = ρ n (pr v) := by
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ F.space ⊔ C from hFC.sup_eq_top ▸ Submodule.mem_top)
    have hnu : ρ n u ∈ F.space := (n.property u).2 hu
    have hnw : ρ n w ∈ C := (hCN n.property w).2 hw
    simp only [pr,LinearMap.comp_apply,map_add,
      Submodule.projectionOnto_apply_of_mem_left hFC hu,
      Submodule.projectionOnto_apply_of_mem_left hFC hnu,
      Submodule.projectionOnto_apply_of_mem_right hFC hw,
      Submodule.projectionOnto_apply_of_mem_right hFC hnw,
      Submodule.subtype_apply,map_zero,add_zero]
  have hprseed {z : V} (hz : z ∈ fixedSpace ρ (P : Subgroup G)) :
      pr z ∈ fixedSpace ρ ((P : Subgroup G) ⊓ N) ⊓ F.space := by
    refine ⟨?_,(F.space.projectionOnto C hFC z).property⟩
    intro n
    change ρ (n:G) (pr z) = pr z
    have hnz : ρ (n:G) z = z := hz ⟨n,n.property.1⟩
    rw [←hpr ⟨n,n.property.2⟩,hnz]
  have hle : Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ fixedSpace ρ (P : Subgroup G) ∧ ρ g v = w} ≤ Q.comap pr := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,z,hz,rfl⟩
    obtain ⟨n,hn,p,hp,rfl⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top g)
    change pr (ρ (n*p) z) ∈ Q
    have hpz : ρ p z = z := hz ⟨p,hp⟩
    rw [map_mul,Module.End.mul_apply,hpz,hpr ⟨n,hn⟩]
    exact le_iSup (fun n : N =>
      (fixedSpace ρ ((P : Subgroup G) ⊓ N) ⊓ F.space).map (ρ n)) ⟨n,hn⟩
        ⟨pr z,hprseed hz,rfl⟩
  apply le_antisymm
  · exact Homogeneous.orbitSpan_le ρ inf_le_right le_rfl
  · intro v hv
    have hh := hle (hspan ▸ (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top))
    change pr v ∈ Q at hh
    simpa only [pr,LinearMap.comp_apply,Submodule.projectionOnto_apply_of_mem_left hFC hv,Submodule.subtype_apply] using hh
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
