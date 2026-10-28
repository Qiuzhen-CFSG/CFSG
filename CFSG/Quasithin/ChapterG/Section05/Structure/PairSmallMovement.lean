module
public import CFSG.Quasithin.ChapterG.Section05.Structure.PairQuotients
public import Theory.Representation.BinaryDuadModule.SmallDisplacement

/-!
# Whole pair-module quotients with small involution displacement

The even duad core has the proved six-step invariant-subspace flag. Every
quotient of dimension greater than five has kernel in the annihilator of the
line-complement nine-space. The explicit involution displacement theorem then
gives rank at least three. Thus one involution moving at most two dimensions
forces the whole quotient to be the natural four-space or its five-dimensional
augmentation cover. The supplied S₆ marking and its A₆ restriction are retained.

Source: Aschbacher--Smith, G.5.3, printed pp.344--345, as applied in the proof
of 13.8.33, printed p.967. OriginalSmallMovement supplies the literal U_L/V
application under its still-explicit endpoint-core image bound.
-/

public section
open Representation BinaryPermutation BinaryDuadModule BinaryDuadStructure
open Theory.SpecificGroups.SymmetricSix
open Representation.BinaryCoverSocle Representation.BinaryOffender.NaturalTensor
open BinaryDuadModule.SmallDisplacement
namespace CFSG.Quasithin.ChapterG.Section05.Structure

/-- Full movement and one small involution exclude all three larger
quotients in the actual duad-core flag. -/
theorem pair_small_involution_finrank
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    [Nontrivial X]
    (ρ : Representation (ZMod 2) S6 X)
    (f : SixPairsQuadratic.action.IntertwiningMap ρ) (hf : Function.Surjective f)
    (hgen : Coinvariants.ker ρ = ⊤)
    (g : S6) (hg : orderOf g = 2) (hsmall : operatorFixedCodim (ρ g) ≤ 2) :
    Module.finrank (ZMod 2) X = 4 ∨ Module.finrank (ZMod 2) X = 5 := by
  obtain ⟨q,hq⟩ := symmetric_pair_core_surjection ρ f hf hgen
  let qA : coreAction.IntertwiningMap (ρ.comp A6.subtype) :=
    q.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (fun a v => IntertwiningMap.isIntertwining _ _ q a.val v)
  have hdim := q.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq,finrank_top,core_finrank] at hdim
  have hcases := core_subrepresentation_cases middleCoverData qA.ker
  have hle : qA.ker ≤ perp coreSelfDual coreLines ∨
      Module.finrank (ZMod 2) X = 4 ∨ Module.finrank (ZMod 2) X = 5 := by
    have he : Module.finrank (ZMod 2) qA.ker.toSubmodule =
        Module.finrank (ZMod 2) q.toLinearMap.ker := rfl
    rcases hcases with h | h | h | h | h | h
    · exact Or.inl (h ▸ bot_le)
    · exact Or.inl (h ▸ (coreFlag_strictAnti middleCoverData
        (by decide : (3 : Fin 6) < 4)).le)
    · exact Or.inl h.le
    · rw [h,coreLines_finrank] at he
      exact Or.inr (Or.inr (by omega))
    · rw [h,coreNatural_perp_finrank] at he
      exact Or.inr (Or.inl (by omega))
    · have hpos : 0 < Module.finrank (ZMod 2) X := Module.finrank_pos
      rw [h,Representation.BinaryCoverSocle.finrank_whole,core_finrank] at he
      omega
  rcases hle with hk | hd
  · have hlo := involution_displacement_ge_three ρ q (fun v hv s => by
      have hm : v ∈ perp coreSelfDual coreLines := hk hv
      have hw : (⟨lineComplement s,lineComplement_mem_core s⟩ : core Duad) ∈ coreLines :=
        Submodule.subset_span (Set.mem_range_self s)
      have hh := (mem_perp coreSelfDual coreLines v).mp hm _ hw
      exact hh) g hg
    omega
  · exact hd

/-- The natural-or-cover comparison is an equivalence of the whole module
when one involution has displacement at most two. The six-letter marking
is retained, including its restriction to the original alternating actor. -/
theorem marked_pair_small_involution
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] [Nontrivial X]
    (ρ : Representation (ZMod 2) A X) (e : A ≃* S6)
    (f : Representation.IntertwiningMap (SixPairsQuadratic.action.comp e.toMonoidHom) ρ)
    (hf : Function.Surjective f) (hgen : Coinvariants.ker ρ = ⊤)
    (b : A) (hb : orderOf (e b) = 2) (hsmall : operatorFixedCodim (ρ b) ≤ 2) :
    let σ : Representation (ZMod 2) A6 X := ρ.comp (e.symm.toMonoidHom.comp A6.subtype)
    (Nonempty (Representation.Equiv (alternatingNaturalRepresentation (Fin 6)) σ) ∨
      Nonempty (Representation.Equiv (alternatingCoreRepresentation (Fin 6)) σ)) ∧
    (Module.finrank (ZMod 2) X = 4 ∨ Module.finrank (ZMod 2) X = 5) := by
  let τ : Representation (ZMod 2) S6 X := ρ.comp e.symm.toMonoidHom
  let f' : SixPairsQuadratic.action.IntertwiningMap τ := {
    toLinearMap := f.toLinearMap
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change f (SixPairsQuadratic.action g v) = ρ (e.symm g) (f v)
      have he := IntertwiningMap.isIntertwining _ _ f (e.symm g) v
      change f (SixPairsQuadratic.action (e (e.symm g)) v) = ρ (e.symm g) (f v) at he
      rwa [e.apply_symm_apply] at he }
  have hg : Coinvariants.ker τ = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    have he : τ (e g) v = ρ g v := by
      change ρ (e.symm (e g)) v = _
      rw [e.symm_apply_apply]
    change ρ g v - v ∈ Coinvariants.ker τ
    rw [← he]
    exact Coinvariants.sub_mem_ker _ _
  have hsmall' : operatorFixedCodim (τ (e b)) ≤ 2 := by
    change operatorFixedCodim (ρ (e.symm (e b))) ≤ 2
    rwa [e.symm_apply_apply]
  have hd := pair_small_involution_finrank τ f' hf hg (e b) hb hsmall'
  refine ⟨?_,hd⟩
  rcases (marked_pair_comparison ρ e f hf hgen).1 with hn | hq
  · exact Or.inl hn
  · obtain ⟨q,hq⟩ := hq
    have htarget : Module.finrank (ZMod 2) (core (Fin 6)) = 5 := by
      simpa using finrank_core (Fin 6)
    have hle := LinearMap.finrank_le_finrank_of_surjective hq
    rw [htarget] at hle
    have heq : Module.finrank (ZMod 2) X = Module.finrank (ZMod 2) (core (Fin 6)) := by
      rw [htarget]
      omega
    have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hq
    exact Or.inr ⟨(q.ofBijective ⟨hi,hq⟩).symm⟩

end CFSG.Quasithin.ChapterG.Section05.Structure
