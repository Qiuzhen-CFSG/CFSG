module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ProperOrbitFactors
public import Theory.Representation.BinaryOffender.PermutedSupportSeed
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
/-!
# A proper fixed-seed span on a literal factor

The missing support selected by the original proper orbit span is retained.
Summing a stabilizer-fixed vector over the supplied Sylow orbit gives an
original seed vector modulo the other supports. Odd averaging on the marked
fully moved kernel recovers its component in the proper orbit span, proving
that the local fixed-seed actor span is proper as well.

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
theorem proper_orbit_factor_missing_seed [K.Normal] (hcore : pCore 2 G = ⊥)
    (hd : d.FittingFull) (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (S : Subgroup G) (hS : IsPGroup 2 S) (i : d.Index)
    (hproper : Homogeneous.orbitSpan ρ (c.orbitActor d π i)
      (fixedSpace ρ S ⊓ c.orbitSpace d π i) < c.orbitSpace d π i) :
    ∃ j : d.Index, (∃ g : G, π g i = j) ∧
      ¬ (c.ambientFactor d j).space ≤ Homogeneous.orbitSpan ρ (c.orbitActor d π i)
        (fixedSpace ρ S ⊓ c.orbitSpace d π i) ∧
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
  refine ⟨j,hjo,hjn,B,?_,?_,?_⟩
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

theorem factor_fixed_seed_span_proper
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (S : Subgroup G) (i j : d.Index) (hji : ∃ g : G, π g i = j)
    (l : CyclicSource.LocalGeneration (c.ambientFactor d j).action)
    (hmissing : ¬ (c.ambientFactor d j).space ≤
      Homogeneous.orbitSpan ρ (c.orbitActor d π i)
        (fixedSpace ρ S ⊓ c.orbitSpace d π i)) :
    Homogeneous.orbitSpan ρ (c.ambientFactor d j).actor
      (fixedSpace ρ (S ⊓ subspaceStabilizer ρ (c.ambientFactor d j).space) ⊓
        (c.ambientFactor d j).space) < (c.ambientFactor d j).space := by
  classical
  let F := c.ambientFactor d j
  let A := c.orbitActor d π i
  let R := Homogeneous.orbitSpan ρ A (fixedSpace ρ S ⊓ c.orbitSpace d π i)
  let N := l.kernel.map F.embedding.groupMap
  have hNA : N ≤ F.actor := map_le_range _ _
  have hFA : F.actor ≤ A := by
    obtain ⟨g,hg⟩ := hji
    change (c.ambientFactor d j).actor ≤ A
    rw [←hg]
    exact le_iSup (fun g : G => (c.ambientFactor d (π g i)).actor) g
  have hRA : A ≤ subspaceStabilizer ρ R := Homogeneous.orbitSpan_invariant ρ A _
  have hm : F.space ≤ subspaceCommutator ρ ⊤ N := by
    have he := subspaceCommutator_map_embedding (ρ.comp F.embedding.groupMap) F.action
      (MonoidHom.id F.Carrier) F.embedding.spaceMap
      (fun g w => (F.embedding.equivariant g w).symm) l.kernel ⊤
    have hlm : subspaceCommutator F.action ⊤ l.kernel = ⊤ := l.moved
    simp only [Subgroup.map_id,Submodule.map_top] at he
    rw [hlm,Submodule.map_top,subspaceCommutator_comp_map] at he
    change F.embedding.spaceMap.range ≤ subspaceCommutator ρ ⊤ N
    rw [←he]
    exact subspaceCommutator_mono_left ρ le_top _
  have ho : Odd (Nat.card N) := by
    let : Fact l.prime.Prime := ⟨l.prime_prime⟩
    obtain ⟨n,hn⟩ := l.pgroup.exists_card_eq
    have hncard : Nat.card N = Nat.card l.kernel :=
      Nat.card_congr (Subgroup.equivMapOfInjective l.kernel F.embedding.groupMap
        F.embedding.group_injective).toEquiv.symm
    rw [hncard,hn]
    exact l.prime_odd.pow
  have hseed : fixedSpace ρ S ⊓ (⨆ s : S, (c.ambientFactor d (π s j)).space) ≤ R := by
    apply le_trans (inf_le_inf_left _ ?_) (Homogeneous.le_orbitSpan ρ A _)
    apply iSup_le
    intro s
    obtain ⟨g,hg⟩ := hji
    rw [←hg]
    change (c.ambientFactor d (π s (π g i))).space ≤
      ⨆ g : G, (c.ambientFactor d (π g i)).space
    simpa only [map_mul,Equiv.Perm.mul_apply] using
      le_iSup (fun g : G => (c.ambientFactor d (π g i)).space) ((s:G)*g)
  have hf : fixedSpace ρ (S ⊓ subspaceStabilizer ρ F.space) ⊓ F.space ≤ R :=
    fixed_support_seed_le ρ S π (fun k => (c.ambientFactor d k).space)
      (fun k => (c.ambientFactor d k).actor)
      (fun k m hkm => c.ambient_cross d hkm.symm) hs j N ho hNA hm R
      (hNA.trans (hFA.trans hRA)) hseed
  have hspanR : Homogeneous.orbitSpan ρ F.actor
      (fixedSpace ρ (S ⊓ subspaceStabilizer ρ F.space) ⊓ F.space) ≤ R := by
    apply Homogeneous.orbitSpan_le
    · exact hf
    · exact hFA.trans hRA
  have hspanF : Homogeneous.orbitSpan ρ F.actor
      (fixedSpace ρ (S ⊓ subspaceStabilizer ρ F.space) ⊓ F.space) ≤ F.space := by
    apply Homogeneous.orbitSpan_le
    · exact inf_le_right
    · rw [F.space_eq_support]
      exact subspaceCommutator_invariant ρ ⊤ F.actor
  exact lt_of_le_of_ne hspanF (fun he => hmissing (he ▸ hspanR))
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
