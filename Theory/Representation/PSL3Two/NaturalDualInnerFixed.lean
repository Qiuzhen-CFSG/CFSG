module
public import Theory.Representation.PSL3Two.NaturalDualNormalizer
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Fixed vectors under inner normalizers of the natural--dual pair

An implementing inner operator preserves each of the two original summands.
A two-group therefore fixes a nonzero vector in each. Their disjoint supports
give a fixed space of dimension at least two. The actual Chapter10 consumer
compares this with the containing ten-dimensional module's Sylow fixed line.

Source: Aschbacher--Smith 10.2.9, printed p.752, natural--dual exclusion.
-/

public noncomputable section
namespace BinaryLinearThree.NaturalDual
open Subgroup Representation.BinaryOffender

/-- A compatible inner two-group action fixes a vector in each summand. -/
theorem two_le_fixed_finrank_of_inner
    {P : Type*} [_root_.Group P]
    (η : Representation (ZMod 2) P Space) (hP : IsPGroup 2 P)
    (a : P →* MulAut Group)
    (ha : ∀ p g x, η p (action g x) = action (a p g) (η p x))
    (hin : ∀ p, a p ∈ MulAut.innerSubgroup Group) :
    2 ≤ Module.finrank (ZMod 2) (fixedSpace η ⊤) := by
  have haxes (p : P) :
      (∀ v, (η p (v,0)).2 = 0) ∧ (∀ v, (η p (0,v)).1 = 0) := by
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom p)
    obtain ⟨g,hg⟩ := inner_operator (a p) f (ha p) (hin p)
    constructor
    · intro v
      change (f (v,0)).2 = 0
      rw [hg]
      exact map_zero (W.dual g)
    · intro v
      change (f (0,v)).1 = 0
      rw [hg]
      exact map_zero (W g)
  let X : Submodule (ZMod 2) Space := (⊤ : Submodule (ZMod 2) Vector).prod ⊥
  let Y : Submodule (ZMod 2) Space := (⊥ : Submodule (ZMod 2) Vector).prod ⊤
  have hX : X ≠ ⊥ := by
    obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
    exact (Submodule.ne_bot_iff _).mpr ⟨(v,0),by simp [X],fun h => hv (congrArg Prod.fst h)⟩
  have hY : Y ≠ ⊥ := by
    obtain ⟨v,hv⟩ := exists_ne (0 : Module.Dual (ZMod 2) Vector)
    exact (Submodule.ne_bot_iff _).mpr ⟨(0,v),by simp [Y],fun h => hv (congrArg Prod.snd h)⟩
  have hx : (⊤ : Subgroup P) ≤ subspaceStabilizer η X := by
    apply le_subspaceStabilizer
    rintro p _ ⟨v,w⟩ hvw
    have hw : w = 0 := hvw.2
    subst w
    exact ⟨Submodule.mem_top,(haxes p).1 v⟩
  have hy : (⊤ : Subgroup P) ≤ subspaceStabilizer η Y := by
    apply le_subspaceStabilizer
    rintro p _ ⟨v,w⟩ hvw
    have hv : v = 0 := hvw.1
    subst v
    exact ⟨(haxes p).2 w,Submodule.mem_top⟩
  have hp : IsPGroup 2 (⊤ : Subgroup P) := hP.of_injective _ (⊤ : Subgroup P).subtype_injective
  obtain ⟨x,hxX,hx0,hxf⟩ := PermutedSupports.exists_nonzero_fixed η ⊤ hp X hX hx
  obtain ⟨y,hyY,hy0,hyf⟩ := PermutedSupports.exists_nonzero_fixed η ⊤ hp Y hY hy
  have hdX : 0 < Module.finrank (ZMod 2) ↥(X ⊓ fixedSpace η ⊤) := by
    have : Nontrivial ↥(X ⊓ fixedSpace η ⊤) := Submodule.nontrivial_iff_ne_bot.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨x,⟨hxX,hxf⟩,hx0⟩)
    exact Module.finrank_pos
  have hdY : 0 < Module.finrank (ZMod 2) ↥(Y ⊓ fixedSpace η ⊤) := by
    have : Nontrivial ↥(Y ⊓ fixedSpace η ⊤) := Submodule.nontrivial_iff_ne_bot.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨y,⟨hyY,hyf⟩,hy0⟩)
    exact Module.finrank_pos
  have hz : (X ⊓ fixedSpace η ⊤) ⊓ (Y ⊓ fixedSpace η ⊤) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    exact Prod.ext hz.2.1.1 hz.1.1.2
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (X ⊓ fixedSpace η ⊤) (Y ⊓ fixedSpace η ⊤)
  rw [hz,finrank_bot,add_zero] at hd
  have hb := Submodule.finrank_mono
    (show (X ⊓ fixedSpace η ⊤) ⊔ (Y ⊓ fixedSpace η ⊤) ≤ fixedSpace η ⊤ from
      sup_le inf_le_right inf_le_right)
  omega
end BinaryLinearThree.NaturalDual
