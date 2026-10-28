module
public import Theory.GroupTheory.BaerSuzukiLocal
public import Theory.GroupTheory.ConjugateIntersectionCore
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Separation of the fixed seed in a non-p-group pair

Suppose every conjugate pair with intersection larger than Z is a p-group.
A subgroup of A centralized modulo Z by its conjugate is normalized by the
whole pair. If larger than Z, it belongs to every intersection inside that
pair. Relative Baer–Suzuki then places A in the pair's p-core, a contradiction.
This is the fixed-seed argument of Aschbacher–Smith F.9.5(5), printed p.319.
-/
public section
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The original seed centralizer modulo Z collapses to Z in a non-p-group pair. -/
theorem commutatorPreimage_eq_of_conjugate_pair_not_isPGroup
    (H A W Z : Subgroup G) (hAH : A ≤ H) (hWA : W ≤ A) (hZW : Z ≤ W)
    (hA : IsPGroup p A) (hAb : IsMulCommutative A)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hpairs : ∀ k ∈ H, Z < A ⊓ A.map (MulAut.conj k).toMonoidHom →
      IsPGroup p (A ⊔ A.map (MulAut.conj k).toMonoidHom : Subgroup G))
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup p (A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    commutatorPreimage W (A.map (MulAut.conj g).toMonoidHom) Z = Z := by
  let B := A.map (MulAut.conj g).toMonoidHom
  let I := A ⊔ B
  let F := commutatorPreimage W B Z
  have hBH : B ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact H.mul_mem (H.mul_mem hg (hAH ha)) (H.inv_mem hg)
  have hIH : I ≤ H := sup_le hAH hBH
  have hFA : F ≤ A := (commutatorPreimage_le W B Z).trans hWA
  have hZF : Z ≤ F := le_commutatorPreimage hZW <| by
    have hc : ⁅Z,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hBH.trans hHZ))
    exact hc.le.trans bot_le
  have hcomm : ⁅F,B⁆ ≤ Z := commutator_commutatorPreimage_le W B Z
    (hWA.trans (hAH.trans (hHZ.trans (centralizer_le_normalizer _))))
  have hAF : A ≤ normalizer (F : Set G) := by
    let := hAb
    have hc : A ≤ centralizer (A : Set G) := fun a ha b hb =>
      congrArg Subtype.val (mul_comm (⟨b,hb⟩ : A) ⟨a,ha⟩)
    exact (hc.trans (centralizer_le hFA)).trans (centralizer_le_normalizer _)
  have hBF : B ≤ normalizer (F : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hZF)
  have hIF : I ≤ normalizer (F : Set G) := sup_le hAF hBF
  apply le_antisymm _ hZF
  by_contra hle
  have hstrict : Z < F := lt_of_le_of_ne hZF (Ne.symm (fun he => hle he.le))
  have hcore : A ≤ I.pCoreIn p := by
    apply le_pCoreIn_of_conjugate_sup_isPGroup I A le_sup_left hA
    intro k hk
    apply hpairs k (hIH hk)
    apply lt_of_lt_of_le hstrict
    refine le_inf hFA ?_
    have he : F.map (MulAut.conj k).toMonoidHom = F :=
      mem_normalizer_iff_map_conj_eq.mp (hIF hk)
    exact he.symm.le.trans (map_mono hFA)
  exact hn (isPGroup_sup_of_le_pCoreIn hcore (show B ≤ I from le_sup_right) (hA.map _))
end Subgroup
