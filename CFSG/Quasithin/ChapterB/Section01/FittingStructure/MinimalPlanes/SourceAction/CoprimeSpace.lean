module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.SourceAction.LocalGroup
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.FixedQuotientKernel

/-!
# Coprime splitting on the centralizer-fixed space

Both C_V(B) and W=[C_V(B),F_A] are invariant under H=F_A A.
Averaging over the odd group F_A splits C_V(B) into its F_A-fixed
part and W. It follows that [W,F_A]=W, and that an element of F_A
fixing W fixes all of C_V(B). Thompson's fixed-kernel calculation
therefore makes the action of F_A on W faithful.

The spaces and subgroup inclusions are the original ones from B.1.9;
no dimension or order-three conclusion is used.
Source: Aschbacher–Smith, B.1.9, first proof paragraph,
printed p.71 (PDF p.82), combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem source_fixedSpace_stable {A : Subgroup G} (hA : IsElementaryTwo A) :
    localGroup A ≤ subspaceStabilizer ρ (fixedSpace ρ (kernelActor A)) :=
  ((localGroup_centralizes_kernelActor hA).trans (centralizer_le_normalizer _)).trans
    (normalizer_le_stabilizer_fixedSpace ρ _)

theorem source_testSpace_stable {A : Subgroup G} (hA : IsElementaryTwo A) :
    localGroup A ≤ subspaceStabilizer ρ (testSpace ρ A) :=
  subspaceCommutator_invariant_normalizer ρ (source_fixedSpace_stable ρ hA)
    (localGroup_normalizes_oddPart A)

theorem source_local_stable {A : Subgroup G} (hA : IsElementaryTwo A) :
    (⊤ : Subgroup (localGroup A)) ≤
      subspaceStabilizer (localRepresentation ρ A) (testSpace ρ A) := by
  intro g _
  exact source_testSpace_stable ρ hA g.property

variable [Finite G]

theorem source_fixedSpace_split (hcore : pCore 2 G = ⊥) {A : Subgroup G}
    (hA : IsElementaryTwo A) :
    (fixedSpace ρ (kernelActor A) ⊓ fixedSpace ρ (oddPart A)) ⊔ testSpace ρ A =
      fixedSpace ρ (kernelActor A) := by
  classical
  let F := oddPart A
  let U := fixedSpace ρ (kernelActor A)
  let := Fintype.ofFinite F
  have hcard : (Fintype.card F : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := oddPart_odd hcore A
    rw [← Nat.card_eq_fintype_card, hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
  let N : V →ₗ[ZMod 2] V := ∑ f : F, ρ f
  have hN (v : V) : N v = ∑ f : F, ρ f v := LinearMap.sum_apply _ _ _
  have hleft (f : F) (v : V) : ρ f (N v) = N v := by
    simp only [hN, map_sum, ← Module.End.mul_apply, ← map_mul]
    change (∑ g : F, ρ ((f * g : F) : G) v) = ∑ g : F, ρ g v
    exact (Group.mulLeft_bijective f).sum_comp (fun g : F => ρ g v)
  have hsub (v : V) (hv : v ∈ U) : N v - v ∈ testSpace ρ A := by
    have hm : (∑ f : F, (ρ f v - v)) ∈ testSpace ρ A :=
      Submodule.sum_mem _ fun f _ => Submodule.subset_span ⟨f, f.property, v, hv, rfl⟩
    rw [Finset.sum_sub_distrib, ← hN, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul] at hm
    exact hm
  apply le_antisymm (sup_le inf_le_left (testSpace_le_fixed ρ A))
  intro v hv
  have hNv : N v ∈ U := by
    rw [hN]
    apply Submodule.sum_mem
    intro f _
    exact ((source_fixedSpace_stable ρ hA ((show F ≤ localGroup A from le_sup_left) f.property)) v).2 hv
  exact Submodule.mem_sup.mpr ⟨N v, ⟨hNv, fun f => hleft f v⟩, v - N v,
    by simpa only [neg_sub] using (testSpace ρ A).neg_mem (hsub v hv), by abel⟩

theorem source_testSpace_self_moved (hcore : pCore 2 G = ⊥) {A : Subgroup G}
    (hA : IsElementaryTwo A) :
    subspaceCommutator ρ (testSpace ρ A) (oddPart A) = testSpace ρ A := by
  apply le_antisymm
  · exact subspaceCommutator_le_of_invariant ρ
      (le_sup_left.trans (source_testSpace_stable ρ hA))
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, v, hv, rfl⟩
    rw [← source_fixedSpace_split ρ hcore hA] at hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have he : ρ f (u+w) - (u+w) = ρ f w - w := by
      rw [map_add, show ρ f u = u from hu.2 ⟨f, hf⟩]
      abel
    rw [he]
    exact Submodule.subset_span ⟨f, hf, w, hw, rfl⟩

variable [FiniteDimensional (ZMod 2) V]

theorem source_oddPart_faithful (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) :
    subspaceKernel ρ (testSpace ρ A) (oddPart A) = ⊥ := by
  apply (subspaceKernel_eq_bot_iff ρ _ _).mpr
  intro f hfF hfix
  apply (subspaceKernel_eq_bot_iff ρ _ _).mp (fitting_fixed_kernel_eq_bot ρ hf hcore hA) f hfF
  intro v hv
  rw [← source_fixedSpace_split ρ hcore hA] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, show ρ f u = u from hu.2 ⟨f, hfF⟩, hfix w hw]

end CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
