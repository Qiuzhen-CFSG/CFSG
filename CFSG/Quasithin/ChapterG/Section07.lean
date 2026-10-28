module

public import CFSG.Quasithin.ChapterG.Section07.Setup
public import Theory.Representation.BinaryPrimeDegree

/-!
# Small-degree representations for some SQTK-groups

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.7, printed pp.346--349 (PDF pp.357--360).
The proof of the last assertion continues onto p.349.

G.7.1(1) follows from the general linear group order formula. The imported
setup records the genuine hypotheses for G.7.2 and G.7.3. Their remaining
degree bounds and group/module classifications are still to be established;
no conditional case list is asserted as the terminal source theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section07

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- G.7.1(1): a subgroup of odd prime order forces the corresponding
binary multiplicative-order lower bound on the faithful module degree. -/
theorem lemma_G_7_1_1 (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (P : Subgroup G) (hP : Nat.card P = p) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  exact Representation.BinaryPrimeDegree.orderOf_le_finrank_of_subgroup ρ hρ hp hp2 P hP

end CFSG.Quasithin.ChapterG.Section07
