module
public import Theory.GroupTheory.HomDeterminedByNormalSubgroup
public import GorensteinWalter.PGL2InnerAction

/-!
# The prescribed normal PSL core determines a PGL homomorphism

Two homomorphisms from any group into PGL2 over an odd finite field agree
if they agree on a normal subgroup whose image is the canonical PSL2 range.
The group and field may live in different universes. All odd fields,
including orders three and nine, are retained.

The canonical PSL2 range has trivial centralizer in PGL2. The general
normal-subgroup rigidity theorem therefore upgrades agreement on that
subgroup to agreement everywhere. No injectivity, surjectivity, exterior
image equality, or ambient finiteness is assumed for the homomorphisms.

This is the projective compatibility step for Alperin--Brauer--Gorenstein
II.3 Proposition 3, article pp26–28. It preserves the whole projective map
under an extension of the prescribed central-layer equivalence, and later
identifies the coefficient actions from their equations on the actual core.
-/

namespace GorensteinWalter
public theorem pgl2_hom_eq_of_agree_on_normal_psl2
    {G F : Type*} [Group G] [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (f g : G →* PGL2 F)
    (N : Subgroup G) [N.Normal] (agree : ∀ n : N, f n = g n)
    (image : N.map f = Matrix.ProjectiveSpecialLinearGroup.toPGL.range) : f = g := by
  apply MonoidHom.eq_of_agree_on_normal_of_centralizer_eq_bot f g N agree
  rw [image]
  exact pgl2_psl2Range_centralizer_eq_bot F hF
end GorensteinWalter
