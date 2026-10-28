module
public import Theory.Representation.SmallBinaryTwoRank
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralResidual
/-!
# Two-rank above a normal marked dihedral actor

The marked source possibilities reduce to normal symmetric-three actors in
binary degree two or four, and normal five actors in degree four. The
literal faithful ambient action therefore has two-rank at most two.

Source: Aschbacher–Smith15.1.7(1),(2),(5) and15.1.13, pp.1087 and1091.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem twoRank_le_two_of_normal_dihedral
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] {p m : ℕ} (hp : PrimeDimensionOptions p m)
    (hdim : Module.finrank (ZMod 2) V = 2*m)
    (j : K ≃* DihedralGroup p) (hcard : Nat.card (pResidual 2 K) = p)
    (hfull : subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ = ⊤) :
    primeRank 2 G ≤ 2 := by
  rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,hm⟩ | ⟨rfl,rfl⟩
  · apply Representation.SmallBinaryTwoRank.rank_le_two_of_normal_symmetricThree ρ hf _ K
      (j.trans nonempty_dihedralThreeEquivPerm.some) hfull
    rcases hm with rfl | rfl
    · exact Or.inl hdim
    · exact Or.inr hdim
  · let P := (pResidual 2 K).map K.subtype
    exact (Representation.SmallBinaryTwoRank.rank_le_one_of_normal_five ρ hf hdim P
      ((card_map_of_injective K.subtype_injective).trans hcard)).trans (by decide)

theorem DihedralMarking.ambient_twoRank_le_two
    {ρ : Representation (ZMod 2) G V} (hf : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] {l : LocalGeneration (ρ.comp K.subtype)}
    {p m : ℕ} (hp : PrimeDimensionOptions p m) (h : DihedralMarking l p m) :
    primeRank 2 G ≤ 2 := by
  apply twoRank_le_two_of_normal_dihedral ρ hf K hp h.dimension h.dihedral.some
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
