module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OrbitSupports
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ClassifiedFactors
public import Theory.Representation.BinaryOffender.PermutedSupportReducibility

/-!
# A reducible factor from a proper support-orbit seed span

Let the literal ratio factors be permuted by the ambient group. A proper
span of the Sylow-fixed seed in one support orbit misses a factor support
whose actor acts nontrivially on that span. Their intersection is therefore
nonzero and proper, and is invariant under the factor together with its
Sylow stabilizer. The binary fixed-vector argument is isolated in
`PermutedSupportReducibility`; no bound on the orbit size is used.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)

namespace FactorData
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ambient_space_fixed_compl [K.Normal] (hcore : pCore 2 G = ⊥)
    (hd : d.FittingFull) (i : d.Index) :
    IsCompl (c.ambientFactor d i).space (fixedSpace ρ (c.ambientFactor d i).actor) := by
  let F := c.ambientFactor d i
  have hz : fixedSpace F.action ⊤ = ⊥ :=
    fixedSpace_top_eq_bot_of_fitting_moved (d.factor i).action
      (c.factor_twoCore d hcore i) (hd i)
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr F.embedding.fixed_complement⟩
  rintro v ⟨w,rfl⟩ hv
  have hw : w ∈ fixedSpace F.action ⊤ := by
    intro g
    apply F.embedding.space_injective
    change F.embedding.spaceMap (F.action g w) = F.embedding.spaceMap w
    rw [F.embedding.equivariant]
    exact hv ⟨F.embedding.groupMap g,⟨g,rfl⟩⟩
  have hw0 : w = 0 := (Submodule.mem_bot (R := ZMod 2)).mp (hz ▸ hw)
  simp only [hw0,map_zero]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem seed_orbit_invariant
    (A S : Subgroup G) [A.Normal] (W : Submodule (ZMod 2) V) :
    S ≤ subspaceStabilizer ρ
      (Homogeneous.orbitSpan ρ A (fixedSpace ρ S ⊓ W)) := by
  apply le_subspaceStabilizer
  intro s hs v hv
  change v ∈ ⨆ a : A, (fixedSpace ρ S ⊓ W).map (ρ a) at hv
  refine Submodule.iSup_induction (fun a : A => (fixedSpace ρ S ⊓ W).map (ρ a))
    (motive := fun v => ρ s v ∈ Homogeneous.orbitSpan ρ A (fixedSpace ρ S ⊓ W)) hv ?_ ?_ ?_
  · rintro a _ ⟨z,hz,rfl⟩
    let a' : A := ⟨s * a * s⁻¹, (inferInstance : A.Normal).conj_mem _ a.property s⟩
    apply le_iSup (fun a : A => (fixedSpace ρ S ⊓ W).map (ρ a)) a'
    refine ⟨z,hz,?_⟩
    change ρ (s * a * s⁻¹) z = ρ s (ρ a z)
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      show ρ s⁻¹ z = z from hz.1 ⟨s⁻¹,S.inv_mem hs⟩]
  · simp
  · intro x y hx hy
    simpa only [map_add] using
      (Homogeneous.orbitSpan ρ A (fixedSpace ρ S ⊓ W)).add_mem hx hy

omit [Finite G] in
theorem proper_orbit_factor_subspace [K.Normal] (hcore : pCore 2 G = ⊥)
    (hd : d.FittingFull) (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (S : Subgroup G) (hS : IsPGroup 2 S) (i : d.Index)
    (hproper : Homogeneous.orbitSpan ρ (c.orbitActor d π i)
      (fixedSpace ρ S ⊓ c.orbitSpace d π i) < c.orbitSpace d π i) :
    ∃ j : d.Index, (∃ g : G, π g i = j) ∧
      ∃ B : Submodule (ZMod 2) V, B ≠ ⊥ ∧ B < (c.ambientFactor d j).space ∧
        (c.ambientFactor d j).actor ⊔
          (S ⊓ subspaceStabilizer ρ (c.ambientFactor d j).space) ≤
            subspaceStabilizer ρ B := by
  classical
  let A := c.orbitActor d π i
  let W := c.orbitSpace d π i
  let R := Homogeneous.orbitSpan ρ A (fixedSpace ρ S ⊓ W)
  let : A.Normal := c.orbitActor_normal d π hp i
  have hRA : A ≤ subspaceStabilizer ρ R := Homogeneous.orbitSpan_invariant ρ A _
  have hRS : S ≤ subspaceStabilizer ρ R := seed_orbit_invariant A S W
  let O : Set d.Index := {j | ∃ g : G, π g i = j}
  have hW : W = ⨆ j : O, (c.ambientFactor d j.val).space := by
    apply le_antisymm
    · exact iSup_le fun g => le_iSup (fun j : O => (c.ambientFactor d j.val).space) ⟨π g i,⟨g,rfl⟩⟩
    · refine iSup_le fun j => ?_
      obtain ⟨g,hg⟩ := j.property
      exact hg ▸ le_iSup (fun g : G => (c.ambientFactor d (π g i)).space) g
  have hex := PermutedSupports.exists_missing_nonfixed_support ρ S hS
    (fun j => (c.ambientFactor d j).actor) (fun j => (c.ambientFactor d j).space)
    (fun j => c.ambient_space_fixed_compl d hcore hd j)
    (fun j k hjk => c.ambient_cross d hjk) O W R hW hRS
    (Homogeneous.le_orbitSpan ρ A _) hproper (by
      intro s hsm j hj
      obtain ⟨g,hg⟩ := hj
      refine ⟨π s j,⟨s*g,?_⟩,hs s j⟩
      simp only [map_mul,Equiv.Perm.mul_apply,hg])
  obtain ⟨j,hjo,hjn,hjf⟩ := hex
  let F := c.ambientFactor d j
  let B := R ⊓ F.space
  have hFA : F.actor ≤ A := by
    obtain ⟨g,hg⟩ := hjo
    change (c.ambientFactor d j).actor ≤ A
    rw [←hg]
    exact le_iSup (fun g : G => (c.ambientFactor d (π g i)).actor) g
  have hBR : subspaceCommutator ρ R F.actor ≤ B := by
    apply le_inf
    · exact subspaceCommutator_le_of_invariant ρ (hFA.trans hRA)
    · rw [F.space_eq_support]
      exact subspaceCommutator_mono_left ρ le_top _
  refine ⟨j,hjo,B,?_,?_,?_⟩
  · intro hB
    apply hjf
    exact (subspaceCommutator_eq_bot_iff ρ R F.actor).mp
      (le_bot_iff.mp (hBR.trans_eq hB))
  · refine lt_of_le_of_ne inf_le_right ?_
    intro he
    exact hjn (he ▸ inf_le_left)
  · apply sup_le
    · apply le_subspaceStabilizer
      intro g hg v hv
      have hF : F.actor ≤ subspaceStabilizer ρ F.space := by
        rw [F.space_eq_support]
        exact subspaceCommutator_invariant ρ ⊤ F.actor
      exact ⟨(hRA (hFA hg) v).2 hv.1,
        (hF hg v).2 hv.2⟩
    · apply le_subspaceStabilizer
      intro g hg v hv
      exact ⟨(hRS hg.1 v).2 hv.1,(hg.2 v).2 hv.2⟩
end FactorData
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem Factor.not_irreducible_of_proper_subspace (F : Factor ρ)
    (B : Submodule (ZMod 2) V) (hne : B ≠ ⊥) (hB : B < F.space)
    (hinv : F.actor ≤ subspaceStabilizer ρ B) : ¬ IsIrreducible F.action := by
  intro hi
  let S : Subrepresentation F.action := {
    toSubmodule := B.comap F.embedding.spaceMap
    apply_mem_toSubmodule := fun g v hv => by
      change F.embedding.spaceMap (F.action g v) ∈ B
      rw [F.embedding.equivariant]
      exact (hinv (show F.embedding.groupMap g ∈ F.actor from ⟨g,rfl⟩)
        (F.embedding.spaceMap v)).2 hv }
  rcases hi.eq_bot_or_eq_top S with h | h
  · apply hne
    apply bot_unique
    intro v hv
    obtain ⟨w,rfl⟩ := hB.le hv
    have hw : w ∈ S := hv
    rw [h] at hw
    have hw0 : w = 0 := (Submodule.mem_bot (R := ZMod 2)).mp hw
    simpa only [hw0,map_zero] using (Submodule.zero_mem (⊥ : Submodule (ZMod 2) V))
  · apply hB.ne
    apply le_antisymm hB.le
    rintro v ⟨w,rfl⟩
    have hw : w ∈ S := by rw [h]; trivial
    exact hw
end CFSG.Quasithin.ChapterD.RatioDecomposition
