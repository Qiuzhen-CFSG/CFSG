module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Inputs
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupTheory.PCoreQuotientEmbedding
public import Theory.SpecificGroups.GL2.PrimeCardinality

/-!
# The automorphism p-core quotient at odd prime rank at most two

Choose a supercritical subgroup X of P. Its Frattini quotient is elementary
abelian of order at most p², and the actual action of Aut(P) on it has
p-group kernel. Extending the linear action by identity coordinates gives
a homomorphism into GL₂(p) with that same kernel, including when P = 1.

To pass from this kernel to the full p-core, use that p² does not divide
the order of GL₂(p). The image's p-core is a normal Hall subgroup, so
Schur–Zassenhaus realizes the quotient as a complement inside the image.
The p-core lifting theorem identifies this quotient with Aut(P)/Oₚ(Aut(P)).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.25(2), printed p.25. The representation also supplies the independent
input needed in A.1.26.
-/

namespace CFSG.Quasithin.ChapterA

universe u

/-- The actual two-dimensional action with p-group kernel needed by A.1.26. -/
public theorem RankActions.smallRankAutomorphismRepresentation :
    RankActions.SmallRankAutomorphismRepresentation.{u} := by
  intro p _ hp P _ _ hP hr
  obtain ⟨X, hX⟩ := hP.exists_supercriticalPSubgroup
    (by rintro rfl; obtain ⟨k, hk⟩ := hp; omega)
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup p X) := ⟨hP.to_subgroup X⟩
  let : IsElementaryAbelian p (X ⧸ frattini X) :=
    isElementaryAbelian_quotient_frattini
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le (X ⧸ frattini X)
    (lemma_A_1_25_frattini_card hp hP hr X hX)
  let a := (Subgroup.quotientAut (frattini X)).comp (MulAut.characteristic X)
  refine ⟨f.comp a, ?_⟩
  rw [MonoidHom.ker_comp_of_injective a f hf]
  exact hX.isPGroup_frattini_action_kernel hP hp

/-- A.1.25(2): the automorphism group modulo its full p-core embeds in GL₂(p).
The trivial ambient p-group is included. -/
public theorem lemma_A_1_25_2
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hp : Odd p) (hP : IsPGroup p P) (hr : primeRank p P ≤ 2) :
    ∃ f : (MulAut P ⧸ pCore p (MulAut P)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod p), Function.Injective f := by
  obtain ⟨f, hf⟩ := RankActions.smallRankAutomorphismRepresentation p hp P hP hr
  exact f.exists_injective_pCore_quotient_of_not_sq_dvd hf
    Matrix.GeneralLinearGroup.prime_sq_not_dvd_card

end CFSG.Quasithin.ChapterA
