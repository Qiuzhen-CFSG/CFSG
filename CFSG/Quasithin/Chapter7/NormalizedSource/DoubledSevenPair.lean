module

public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenAutomizer
public import Theory.Representation.BinaryAlternatingSevenControl.InnerIntertwiner
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair

/-!
# The genuine H.8 pair in compatible symmetric coordinates

An odd permutation cannot preserve a faithful binary A₇ four-space: an
invertible intertwiner would make its automorphism inner, contradicting
Aut(A₇) = S₇. Schur's lemma therefore kills both diagonal blocks of every
odd operator on the two inequivalent four-spaces. This proves the actual
exchange of their coordinate axes and constructs the Pair required by H.8.

The application to the original chosen module is in NonFFSourceDoubledSevenPair.
Source: Aschbacher--Smith D.3.10, H.8 and 7.5.5, printed pp.201,389,701.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Representation.BinaryAlternatingSevenControl Representation.AlternatingSevenConjugatePair
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

private theorem odd_block_zero
    (σ : Representation (ZMod 2) A7 U) (hσ : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) U = 4)
    (g : Equiv.Perm (Fin 7)) (hg : g ∉ alternatingGroup (Fin 7))
    (f : U →ₗ[ZMod 2] U)
    (hf : ∀ a v, f (σ a v) = σ (MulAut.conjNormal g a) (f v)) : f = 0 := by
  let α : MulAut A7 := MulAut.conjNormal g
  let τ := σ.comp α.toMonoidHom
  let := doubledSeven_four_irreducible σ hσ hd
  let := doubledSeven_four_irreducible τ (hσ.comp α.injective) hd
  let b : σ.IntertwiningMap τ := ⟨f,by
    intro a
    ext v
    exact hf a v⟩
  rcases IsIrreducible.bijective_or_eq_zero b with hb | hz
  · obtain ⟨a,ha⟩ := inner_of_intertwiner σ hσ hd α (b.ofBijective hb).toLinearEquiv hf
    have he : g = a.val :=
      (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by decide))
        (by change α = MulAut.conjNormal a.val; rw [ha,MulAut.conjNormal_val])
    exact (hg (he ▸ a.property)).elim
  · exact congrArg IntertwiningMap.toLinearMap hz

private theorem irreducible_of_equiv
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) A7 X} {σ : Representation (ZMod 2) A7 Y}
    (e : ρ.Equiv σ) (hσ : IsIrreducible σ) : IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule σ).mp hσ)

/-- A compatible full symmetric action supplies every structural hypothesis
of H.8, including the exchange of the two actual irreducible summands. -/
theorem doubledSeven_pair_of_symmetric_action
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4) (hne : ¬ Nonempty (σ.Equiv τ))
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) (U × U))
    (hρ : Function.Injective ρ)
    (hinner : ∀ a : A7, ρ a.val = (σ.prod τ) a) :
    ∃ P : Pair (U × U), P.representation = ρ ∧
      P.first.toSubmodule = LinearMap.ker (LinearMap.snd (ZMod 2) U U) ∧
      P.second.toSubmodule = LinearMap.ker (LinearMap.fst (ZMod 2) U U) := by
  let F : Subrepresentation (ρ.comp (alternatingGroup (Fin 7)).subtype) := {
    toSubmodule := LinearMap.ker (LinearMap.snd (ZMod 2) U U)
    apply_mem_toSubmodule := by
      intro a v hv
      change (ρ a.val v).2 = 0
      rw [hinner]
      change τ a v.2 = 0
      rw [show v.2 = 0 from hv,map_zero] }
  let S : Subrepresentation (ρ.comp (alternatingGroup (Fin 7)).subtype) := {
    toSubmodule := LinearMap.ker (LinearMap.fst (ZMod 2) U U)
    apply_mem_toSubmodule := by
      intro a v hv
      change (ρ a.val v).1 = 0
      rw [hinner]
      change σ a v.1 = 0
      rw [show v.1 = 0 from hv,map_zero] }
  let eF : F.toRepresentation.Equiv σ := {
    toFun v := v.val.1
    invFun v := ⟨(v,0),rfl⟩
    left_inv v := Subtype.ext (Prod.ext rfl v.property.symm)
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    isIntertwining' := by
      intro a
      ext v
      change (ρ a.val v.val).1 = σ a v.val.1
      rw [hinner]
      rfl }
  let eS : S.toRepresentation.Equiv τ := {
    toFun v := v.val.2
    invFun v := ⟨(0,v),rfl⟩
    left_inv v := Subtype.ext (Prod.ext v.property.symm rfl)
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    isIntertwining' := by
      intro a
      ext v
      change (ρ a.val v.val).2 = τ a v.val.2
      rw [hinner]
      rfl }
  have hcov (g : Equiv.Perm (Fin 7)) (a : A7) (v : U × U) :
      ρ g ((σ.prod τ) a v) = (σ.prod τ) (MulAut.conjNormal g a) (ρ g v) := by
    rw [← hinner,← hinner,← Module.End.mul_apply,← Module.End.mul_apply,← map_mul,← map_mul]
    congr 2
    change g * a.val = (g * a.val * g⁻¹) * g
    group
  have hswapF (g : Equiv.Perm (Fin 7)) (hg : g ∉ alternatingGroup (Fin 7))
      (v : U × U) (hv : v ∈ F.toSubmodule) : ρ g v ∈ S.toSubmodule := by
    let f := (LinearMap.fst (ZMod 2) U U).comp ((ρ g).comp (LinearMap.inl (ZMod 2) U U))
    have hf : f = 0 := odd_block_zero σ hσ hd g hg f (by
      intro a w
      simpa [f] using congrArg Prod.fst (hcov g a (w,0)))
    change (ρ g v).1 = 0
    have hv' : v = (v.1,0) := Prod.ext rfl hv
    rw [hv']
    exact congrArg (fun f : U →ₗ[ZMod 2] U => f v.1) hf
  have hswapS (g : Equiv.Perm (Fin 7)) (hg : g ∉ alternatingGroup (Fin 7))
      (v : U × U) (hv : v ∈ S.toSubmodule) : ρ g v ∈ F.toSubmodule := by
    let f := (LinearMap.snd (ZMod 2) U U).comp ((ρ g).comp (LinearMap.inr (ZMod 2) U U))
    have hf : f = 0 := odd_block_zero τ hτ hd g hg f (by
      intro a w
      simpa [f] using congrArg Prod.snd (hcov g a (0,w)))
    change (ρ g v).2 = 0
    have hv' : v = (0,v.2) := Prod.ext hv rfl
    rw [hv']
    exact congrArg (fun f : U →ₗ[ZMod 2] U => f v.2) hf
  refine ⟨{
    representation := ρ
    faithful := hρ
    first := F
    second := S
    complementary := ?_
    first_dim := eF.toLinearEquiv.finrank_eq.trans hd
    second_dim := eS.toLinearEquiv.finrank_eq.trans hd
    first_irreducible := irreducible_of_equiv eF (doubledSeven_four_irreducible σ hσ hd)
    second_irreducible := irreducible_of_equiv eS (doubledSeven_four_irreducible τ hτ hd)
    inequivalent := fun ⟨e⟩ => hne ⟨eF.symm.trans (e.trans eS)⟩
    swap_first := hswapF
    swap_second := hswapS },rfl,rfl,rfl⟩
  change IsCompl (LinearMap.ker (LinearMap.snd (ZMod 2) U U))
    (LinearMap.ker (LinearMap.fst (ZMod 2) U U))
  rw [LinearMap.ker_snd,LinearMap.ker_fst]
  exact LinearMap.isCompl_range_inl_inr

end CFSG.Quasithin.Chapter7.NormalizedSource
