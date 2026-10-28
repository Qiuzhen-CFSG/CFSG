module

public import Theory.GroupTheory.Recognition.ReeTwo.TransferReduction
public import Theory.GroupTheory.Recognition.ReeTwo.RootOneFusion

/-!
# Ree two centralizer exclusion: proved reductions

The re-exported reductions identify the actual Sylow model and force root 1
to have an ambient conjugate in the parity kernel under nonsolvable
simplicity. They also identify the central involution with root 12 and
give the ordinary-transfer obstruction for any fusion-invariant binary
character.

The final nonexistence theorem combines these reductions with the ambient
fusion separation proved in `RootOneFusion`. Its source is the q = 2 case of
Shinoda (1975), p. 79 and (4.5), p. 85, referring to Parrott (1973),
pp. 341–357. The formal route uses the binary-character obstruction of van
Beek (2024), Proposition 3.1, with the centric fusion calculation proved in
the imported modules.
-/

namespace ReeTwo

/-- A nonsolvable simple group cannot have the verified Ree two centralizer as
the full centralizer of a Sylow-central involution.

The transfer reduction forces the transported root 1 to have an ambient
conjugate in the kernel of the concrete parity character. The ambient
fusion theorem rules out precisely such a conjugate, giving the contradiction.
-/
public theorem false_of_centralizer_equiv
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (z : G)
    (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) : False := by
  obtain ⟨t, hconj, ht⟩ :=
    exists_rootOne_conjugate_of_centralizer hns S z hcentral ec
  exact rootOne_fusion_character_ne_one hns S z hz hcentral ec t hconj ht

end ReeTwo
