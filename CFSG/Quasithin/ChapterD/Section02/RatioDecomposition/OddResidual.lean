module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeSeed
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.OddResidual
public import Theory.Representation.PermutedSupportOddResidual
/-!
# Odd residuals of the literal dihedral support images

The embedded factor maps faithfully and normally into its support action
image, with the same full moved module. Its marked D.2.17 endpoint therefore
gives an odd support residual. For two permuted factors spanning the whole
module, the faithful permuted-support theorem gives an odd ambient residual.
All group maps, supports, and marked kernels are the original ones.

Source: Aschbacher–Smith 15.1.2(3) and the two-nilpotence used in 15.1.6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (F : Factor ρ)
omit [Finite G] in
private theorem odd_actor_le_stabilizer : F.actor ≤ subspaceStabilizer ρ F.space := by
  apply le_subspaceStabilizer
  rintro g ⟨a,rfl⟩ w ⟨v,rfl⟩
  exact ⟨F.action a v,F.embedding.equivariant a v⟩

omit [Finite G] in
theorem faithful_normal_support_image_data
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set G)) :
    ∃ (k : F.Carrier →* subspaceActionImage ρ F.space)
      (J : F.Space ≃ₗ[ZMod 2] F.space),
      Function.Injective k ∧
      (∀ g w, J (F.action g w) = subspaceImageRepresentation ρ F.space (k g) (J w)) ∧
      k.range = restrictedSubgroup ρ F.space F.actor ∧ k.range.Normal ∧
      subspaceCommutator (subspaceImageRepresentation ρ F.space) ⊤ k.range = ⊤ := by
  let W := F.space
  let L := subspaceStabilizer ρ W
  let A := subspaceActionImage ρ W
  let q := subspaceActionHom ρ W
  let σ := subspaceImageRepresentation ρ W
  let R := F.actor.subgroupOf L
  let H := R.map q
  let : R.Normal := normal_subgroupOf_of_le_normalizer hN
  let : H.Normal := (inferInstance : R.Normal).map q
    (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective
  let k : F.Carrier →* A := (subgroupActionHom ρ W F.actor F.odd_actor_le_stabilizer).comp
    F.embedding.groupMap.rangeRestrict
  have hkeq (g : F.Carrier) (w : F.Space) :
      (σ (k g) ⟨F.embedding.spaceMap w,⟨w,rfl⟩⟩ : V) = F.embedding.spaceMap (F.action g w) :=
    (F.embedding.equivariant g w).symm
  have hk : Function.Injective k := by
    intro a b hab
    apply F.faithful
    ext w
    apply F.embedding.space_injective
    exact (hkeq a w).symm.trans
      ((congrArg (fun g => (σ g ⟨F.embedding.spaceMap w,⟨w,rfl⟩⟩ : V)) hab).trans (hkeq b w))
  have hkr : k.range = H := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨⟨F.embedding.groupMap g,F.odd_actor_le_stabilizer ⟨g,rfl⟩⟩,⟨g,rfl⟩,rfl⟩
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨a,ha⟩ := hg
      refine ⟨a,?_⟩
      change q ⟨F.embedding.groupMap a,_⟩ = q g
      exact congrArg q (Subtype.ext ha)
  let J : F.Space ≃ₗ[ZMod 2] W := LinearEquiv.ofInjective F.embedding.spaceMap F.embedding.space_injective
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_surjective J.toLinearMap J.surjective
  have hJ (g : F.Carrier) (w : F.Space) : J (F.action g w) = σ (k g) (J w) := by
    apply Subtype.ext
    exact (hkeq g w).symm
  have hfull : subspaceCommutator σ ⊤ H = ⊤ := by
    have hh := subspaceCommutator_map_embedding F.action σ k J.symm.toLinearMap
      (fun g w => by
        apply J.injective
        rw [hJ]
        change (σ (k g)) (J (J.symm w)) = J (J.symm ((σ (k g)) w))
        rw [J.apply_symm_apply,J.apply_symm_apply]) ⊤ ⊤
    rw [Submodule.map_top,LinearEquiv.range,F.full,←MonoidHom.range_eq_map,hkr] at hh
    apply (Submodule.map_injective_of_injective J.symm.injective)
    rw [Submodule.map_top,LinearEquiv.range]
    exact hh.symm
  refine ⟨k,J,hk,hJ,hkr,?_,?_⟩
  · rw [hkr]
    infer_instance
  · rw [hkr]
    exact hfull


theorem odd_support_twoResidual_of_dihedral
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set G))
    {p m : ℕ} (hp : CyclicSource.PrimeDimensionOptions p m)
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l p m) :
    Odd (Nat.card (pResidual 2 (subspaceActionImage ρ F.space))) := by
  obtain ⟨k,J,hk,hJ,hkr,hn,hfull⟩ := F.faithful_normal_support_image_data hN
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let e : F.Carrier ≃* H := MonoidHom.ofInjective hk
  apply CyclicSource.odd_twoResidual_of_normal_dihedral
    (subspaceImageRepresentation ρ F.space) (subspaceImageRepresentation_injective ρ F.space)
    H hp (J.finrank_eq.symm.trans hm.dimension) (e.symm.trans hm.dihedral.some)
  · rw [←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    calc
      Nat.card ((pResidual 2 F.Carrier).map e.toMonoidHom) = Nat.card (pResidual 2 F.Carrier) :=
        card_map_of_injective (f := e.toMonoidHom) e.injective
      _ = p := by rw [←l.kernel_eq_twoResidual]; exact hm.card_kernel
  · rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,H.range_subtype]
    exact hfull
end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor

namespace CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)

theorem odd_twoResidual_of_two_dihedral_factors
    (hf : Function.Injective ρ) (hU : U = ⊤) (hcount : Nat.card d.Index = 2)
    (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    {p m : ℕ} (hpm : CyclicSource.PrimeDimensionOptions p m)
    (hm : ∀ i, ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
      CyclicSource.DihedralMarking l p m) :
    Odd (Nat.card (pResidual 2 G)) := by
  classical
  let := Fintype.ofFinite d.Index
  have hπ : IsPGroup 2 (Equiv.Perm d.Index) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_perm,hcount]
    rfl
  apply odd_twoResidual_of_permuted_supports ρ hf
    (fun i => (c.ambientFactor d i).space) ((c.ambient_spaces_generate d).trans hU) π hπ hs
  intro i
  obtain ⟨l,hl⟩ := hm i
  exact (c.ambientFactor d i).odd_support_twoResidual_of_dihedral
    (c.support_stabilizer_normalizes_actor d π hp hs i) hpm l hl
end CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
