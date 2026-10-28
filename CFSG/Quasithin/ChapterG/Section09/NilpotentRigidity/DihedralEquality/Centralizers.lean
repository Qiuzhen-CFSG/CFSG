module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.InductionContracts
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Centralizers.SmallDihedral
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Centralizers.Orthogonal

/-!
# Commuting-involution rigidity for a classified binary action

A commuting involution preserves every actual displacement summand of an
internal classified decomposition. Each factor acts faithfully there,
since it fixes all the other summands pointwise. The faithful S₃-plane,
faithful D₁₀-four-space, and genuine natural OmegaFour centralizer
calculations make the involution trivial on each summand, hence everywhere.

This proves the published conditional centralizer contract used in the
Aschbacher--Smith G.9.2 equality induction, printed pp.352--353. Only the
A.1.44 splitting remains an input. The equality classification itself is
not assumed or proved by this helper.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

open DihedralDegree

universe v

theorem classifiedInvolutionCentralizer_of_inputs (split : DihedralSplittingTheorem.{v}) :
    ClassifiedInvolutionCentralizerTheorem.{0,v} := by
  intro G _ W _ _ _ σ H exceptional D hf t ht hc
  apply linearMap_eq_of_internal_summands D.internal
  intro i w
  let K := D.internal.factor i
  let U := movedSpace σ K
  have hstable (g : K) : U ≤ U.comap (σ g) :=
    coinvariants_stable (σ.comp K.subtype) g
  let τ := Representation.subrepresentation (σ.comp K.subtype) U hstable
  have hτ : Function.Injective τ := internal_factor_faithful D.internal hf i
  have hcomm (g : K) : Commute t (σ g) :=
    hc ⟨g.val, D.internal.factor_le i g.property⟩
  let ti : Module.End (ZMod 2) U := t.restrict
    (fun _ hw => movedSpace_stable_of_commuting_end σ K t hcomm hw)
  have hti : ti*ti=1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun f : Module.End (ZMod 2) W => f w) ht
  have hci (g : K) : Commute ti (τ g) := by
    change ti * τ g = τ g * ti
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun f : Module.End (ZMod 2) W => f w) (hcomm g).eq
  have he : ti=1 := by
    by_cases hex : exceptional ∧ i.val = 0
    · obtain ⟨hpos, ⟨e⟩, hd⟩ := D.exceptional_factor hex.1
      have hi : i = ⟨0, hpos⟩ := Fin.ext hex.2
      have he : Nonempty (K ≃* DihedralGroup 5) := by
        change Nonempty (D.internal.factor i ≃* DihedralGroup 5)
        rw [hi]
        exact ⟨e⟩
      have hdim : Module.finrank (ZMod 2) U = 4 := by
        change Module.finrank (ZMod 2) (movedSpace σ (D.internal.factor i)) = 4
        rw [hi]
        exact hd
      exact dihedral_model_involution_centralizer split (Or.inr rfl) τ hτ he.some hdim ti hti hci
    · have hordinary : ¬exceptional ∨ 0 < i.val := by
        by_cases h : exceptional
        · exact Or.inr (Nat.pos_of_ne_zero (fun hzero => hex ⟨h, hzero⟩))
        · exact Or.inl h
      rcases D.ordinary_factor i hordinary with ⟨⟨e⟩, hd⟩ | ⟨⟨e, f, ha⟩, _⟩
      · exact symmetricThree_involution_centralizer split τ hτ e hd ti hti hci
      · apply natural_omegaFour_involution_centralizer τ e f _ ti hti hci
        intro g w
        apply f.symm.injective
        rw [LinearEquiv.symm_apply_apply]
        apply Subtype.ext
        exact ha g w
  exact congrArg Subtype.val (congrArg (fun a : Module.End (ZMod 2) U => a w) he)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
