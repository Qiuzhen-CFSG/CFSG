module
public import Theory.Representation.SmallBinaryOddResidual
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralResidual
/-!
# Odd ambient residual for a normal marked dihedral actor

The D.2.17 prime and dimension markings reduce to the faithful binary
plane, normal symmetric-three, and normal five-group bounds. Full movement
belongs to the marked actor; the ambient two-residual is proved odd without
an assumed odd residual supplement.

Source: Aschbacher–Smith 15.1.2(1), used in 15.1.6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem odd_twoResidual_of_normal_dihedral
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] {p m : ℕ} (hp : PrimeDimensionOptions p m)
    (hdim : Module.finrank (ZMod 2) V = 2*m)
    (j : K ≃* DihedralGroup p) (hcard : Nat.card (pResidual 2 K) = p)
    (hfull : subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ = ⊤) :
    Odd (Nat.card (pResidual 2 G)) := by
  rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,hm⟩ | ⟨rfl,rfl⟩
  · apply SmallBinaryOddResidual.odd_twoResidual_of_normal_symmetricThree ρ hf _ K
      (j.trans nonempty_dihedralThreeEquivPerm.some) hfull
    rcases hm with rfl | rfl
    · exact Or.inl hdim
    · exact Or.inr hdim
  · let P := (pResidual 2 K).map K.subtype
    exact SmallBinaryOddResidual.odd_twoResidual_of_normal_five ρ hf hdim P
      ((card_map_of_injective K.subtype_injective).trans hcard)

theorem DihedralMarking.odd_ambient_twoResidual
    {ρ : Representation (ZMod 2) G V} (hf : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] {l : LocalGeneration (ρ.comp K.subtype)}
    {p m : ℕ} (hp : PrimeDimensionOptions p m) (h : DihedralMarking l p m) :
    Odd (Nat.card (pResidual 2 G)) := by
  apply odd_twoResidual_of_normal_dihedral ρ hf K hp h.dimension h.dihedral.some
  · rw [←l.kernel_eq_twoResidual]
    exact h.card_kernel
  · apply top_unique
    calc
      ⊤ = subspaceCommutator (ρ.comp K.subtype) ⊤ l.kernel := l.moved.symm
      _ ≤ subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ := by
        apply Submodule.span_mono
        rintro _ ⟨g,hg,v,hv,rfl⟩
        exact ⟨g,mem_top _,v,hv,rfl⟩
end CFSG.Quasithin.ChapterD.CyclicSource
