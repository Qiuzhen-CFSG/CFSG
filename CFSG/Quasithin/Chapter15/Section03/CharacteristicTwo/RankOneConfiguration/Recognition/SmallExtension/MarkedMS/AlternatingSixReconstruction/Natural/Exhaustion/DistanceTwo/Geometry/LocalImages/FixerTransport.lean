module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Transport of the literal six-letter displacement fixer

Five pair vectors test whether an actor fixes the moved natural subspace.
The test follows from the original subspace-kernel containment, and that
containment transports through conjugation. Both the four-image exclusion
and the transposition recognition use this same finite interface.

Source: MS93 (3.3)(ii), printed pp.866--867.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
@[expose] def pairTest (n : Fin 5) : Fin 6 → ZMod 2 :=
  Pi.single n.castSucc 1 + Pi.single 5 1
@[expose] def fixesTest (g a : (Equiv.Perm (Fin 6))) : Prop :=
  ∀ n : Fin 5, ∃ c : ZMod 2, ∀ k : Fin 6,
    (representation (Fin 6) g (representation (Fin 6) a (pairTest n) - pairTest n) -
      (representation (Fin 6) a (pairTest n) - pairTest n)) k = c
instance (g a : (Equiv.Perm (Fin 6))) : Decidable (fixesTest g a) := by
  unfold fixesTest
  infer_instance
theorem fixesTest_of_fixes_moved (A B : Subgroup (Equiv.Perm (Fin 6)))
    (hfix : B ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤)
    {a g : (Equiv.Perm (Fin 6))} (ha : a ∈ A) (hg : g ∈ B) : fixesTest g a := by
  intro n
  have hp : pairTest n ∈ core (Fin 6) := by
    simp [pairTest, mem_core, Finset.sum_add_distrib]
    decide
  let v : core (Fin 6) := ⟨pairTest n,hp⟩
  let w := coreRepresentation (Fin 6) a v - v
  have hh := (hfix hg).2
    (naturalRepresentation (Fin 6) a (coreToNatural (Fin 6) v) - coreToNatural (Fin 6) v)
    (Submodule.subset_span ⟨a,ha,_,Submodule.mem_top,rfl⟩)
  have he : coreToNatural (Fin 6) (coreRepresentation (Fin 6) g w) =
      coreToNatural (Fin 6) w := by
    simpa only [w,coreToNatural_equivariant,map_sub] using hh
  have hc := (Submodule.Quotient.eq (constants (Fin 6))).mp (congrArg Subtype.val he)
  exact (mem_constants_iff _).mp hc

theorem moved_fixer_conjugate (A B : Subgroup (Equiv.Perm (Fin 6))) (g : (Equiv.Perm (Fin 6)))
    (hfix : B ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤) :
    B.map (MulAut.conj g).toMonoidHom ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
        (A.map (MulAut.conj g).toMonoidHom)) ⊤ := by
  let ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (natural (Fin 6)) := naturalRepresentation (Fin 6)
  have hinv (v : natural (Fin 6)) : ρ g⁻¹ (ρ g v) = v := by
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hginv (v : natural (Fin 6)) : ρ g (ρ g⁻¹ v) = v := by
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rintro _ ⟨b,hb,rfl⟩
  refine ⟨mem_top _,?_⟩
  have hf : subspaceCommutator ρ ⊤ (A.map (MulAut.conj g).toMonoidHom) ≤
      LinearMap.ker (ρ ((MulAut.conj g) b) - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
    have hh := (hfix hb).2 (ρ a (ρ g⁻¹ v) - ρ g⁻¹ v)
      (Submodule.subset_span ⟨a,ha,_,Submodule.mem_top,rfl⟩)
    change ρ b (ρ a (ρ g⁻¹ v) - ρ g⁻¹ v) = ρ a (ρ g⁻¹ v) - ρ g⁻¹ v at hh
    have he : ρ (g*a*g⁻¹) v-v = ρ g (ρ a (ρ g⁻¹ v)-ρ g⁻¹ v) := by
      simp only [map_sub,map_mul,Module.End.mul_apply,hginv]
    change ρ (g*b*g⁻¹) (ρ (g*a*g⁻¹) v-v) - (ρ (g*a*g⁻¹) v-v)=0
    rw [he]
    simp only [map_mul,Module.End.mul_apply,hinv,hh,sub_self]
  intro v hv
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero,ρ,MulEquiv.coe_toMonoidHom] using hf hv


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
