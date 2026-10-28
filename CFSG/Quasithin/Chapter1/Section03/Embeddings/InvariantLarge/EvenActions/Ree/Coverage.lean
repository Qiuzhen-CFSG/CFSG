module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Ree

/-!
# The Ree Cartan action with automorphism coverage discharged

The nonabelian simple component D is perfect. Its actual equivalence with
ReeF4.Model m and the proved comparison with the supplied fixed group transfer
both instances to that fixed group. The fixed Bruhat geometry, opposite-pair
normalization and rigidity therefore supply inner–field coverage there.
The raw Cartan theorem then proves the power action on the actual B/Φ(B).

All premises beyond the source field/Cartan configuration are discharged.
The parameter m ≥ 1 comes from that configuration; the Tits endpoint is not
identified with this full Ree fixed group. SQTK and BS = SB are unnecessary
for this stronger deduction once the raw configuration is supplied.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5), printed
pp.50–51, and Proposition 1.3.4, printed p.511 (`refs/quasithin.pdf`).
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Ree.Source

/-- The Ree action step in Proposition 1.3.4. Simplicity and perfectness for
the coverage theorem are inherited from D through the actual model equivalence. -/
theorem frattini_power_of_source
    {J : Type*} [Group J] [Finite J] (D : Subgroup J)
    [D.Normal] [IsSimpleGroup D] {m : ℕ}
    {d : ReeF4.LocalBlockInput m} {e : D ≃* ReeF4.Model m}
    {S : Sylow 2 J} {B : Subgroup J} {n f : ℕ} {F H I : Subgroup (MulAut D)}
    (hD : Theory.GroupTheory.generalizedFitting J = D) (hna : ¬ IsMulCommutative D)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hB : IsPGroup p B) (hBD : B ≤ D)
    (h : RawCartan D d e S B n f F H I) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  let e' := e.trans d.modelEquiv.symm
  let : Group.IsPerfect D := ⟨
    (inferInstance : (commutator D).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hna ((commutator_eq_bot_iff D).mp h))⟩
  let : IsSimpleGroup d.fixedGroup := e'.symm.isSimpleGroup
  let : Group.IsPerfect d.fixedGroup :=
    Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  exact frattini_power_of_raw_cartan D hD hp hB hBD h
    (ReeF4.LocalBlockInput.inner_field h.parameter_large d)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Ree.Source
