module

public import Theory.GroupTheory.GeneralizedFitting.CoprimeOuterSupplement
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!+# Elimination of the Suzuki outer two-extension

Let L = F*(G) be simple, let T be a Sylow two-subgroup, and suppose G = LT
and L is actually isomorphic to Sz(2^(2m+1)), with m > 0. Then L = G.
The concrete model is nonsolvable, so simplicity makes L centerless. The
proved inner-field decomposition of every model automorphism makes the full
outer group have odd order. Transport along the given isomorphism and the
centerless Sylow-supplement argument then eliminate G/L.

This discharges the ambient-extension step in the Suzuki branch of
Aschbacher--Smith E.1.14(1), printed p.214 (PDF p.225), citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.7. It does not yet
assert the generation parameter. The automorphism input is GLS III,
Theorem 2.5.12(b--f), and GLS IV, Chapter 4, Lemma 3.1(b), proved for the
literal matrix group by the imported inner-field coverage theorem.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- In the Suzuki case of E.1.14(1), the whole ambient group is its simple
generalized Fitting subgroup. No outer-order or innerness premise remains. -/
theorem generalizedFitting_eq_top [IsSimpleGroup (generalizedFitting G)]
    (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {m : ℕ} (hm : 0 < m) (e : generalizedFitting G ≃* SuzukiMatrixGroup m) :
    generalizedFitting G = ⊤ := by
  have hZ : center (generalizedFitting G) = ⊥ := by
    rcases (inferInstance : (center (generalizedFitting G)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · have hcomm : ∀ x y : generalizedFitting G, x * y = y * x := by
        intro x y
        have hx : x ∈ center (generalizedFitting G) := h ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm
      let : Group.IsSolvable (generalizedFitting G) := Group.isSolvable_of_comm hcomm
      exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)).elim
  have hodd : Odd (Nat.card (MulAut.Outer (generalizedFitting G))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact suzuki_odd_outer_index m hm
  exact generalizedFitting_eq_top_of_coprime_outer_supplement T hgen hZ
    hodd.coprime_two_right

end CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki
