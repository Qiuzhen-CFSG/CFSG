module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SymplecticCut
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups

/-!
# The actual holomorph-graph centralizer cut

The group-algebra and cover theorem apply at a literal adjacent pair of the
existing free-amalgam graph. Normalization of the residual and U, containment
of Q in the edge kernel, and the definition of D are discharged here. The
two substantive earlier source bounds on the enlarged seed remain explicit.

Source: MS93 (3.4), final paragraph, p.869.
-/

public section
open Subgroup Representation Representation.OneCohomology
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M K : Type*} [Group M] [Finite M] [Field K] [Finite K] [CharP K 2]
  [Algebra (ZMod 2) K] (R : Subgroup M)
open Representation.SymplecticFourOrthogonalCover

theorem graph_centralizer_cut
    (a t : Vertex R) (ht : color R t = true) (hat : Adjacent R a t)
    [Finite (U R a)] [IsElementaryAbelian 2 (U R a)]
    (π : (Ltilde R a) →* L (K := K)) (hπ : Function.Surjective π)
    (σ : Representation (ZMod 2) (L (K := K)) (Additive (U R a)))
    (hact : ∀ l : Ltilde R a, ∀ u : U R a,
      ((σ (π l) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (l:FreeAmalgam R)*u*(l:FreeAmalgam R)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (Zstar : Subgroup (FreeAmalgam R))
    (hZ : Zstar ≤ U R a ⊔ fixedCore R a)
    (hcomm : ⁅Zstar, (Ltilde R a ⊔ (Q R t ⊓ centralizer (Zstar : Set (FreeAmalgam R)))) ⊓ Q R a⁆ ≤
      fixedCore R a) :
    (Ltilde R a ⊔ (Q R t ⊓ centralizer (Zstar : Set (FreeAmalgam R)))) ⊓ Q R a ≤
      Q R t ⊓ centralizer (Zstar : Set (FreeAmalgam R)) := by
  have hLn : stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (Ltilde R a).map (MulAut.conj g).toMonoidHom = Ltilde R a
    have he := Ltilde_act R g⁻¹ a
    have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
    simpa only [hga,inv_inv] using he.symm
  have htG : Q R t ≤ stabilizer R a := by
    rw [Q_h_eq_edge R ht hat]
    exact inf_le_left
  exact centralizer_cut_of_symplectic_cover
    (Ltilde R a) (Q R t) (Q R a) (U R a) (fixedCore R a) Zstar
    π hπ σ hact p hp (htG.trans hLn) (Q_le_adjacent_h R ht hat)
    ((show fixedCore R a ≤ stabilizer R a from fun _ h => h.1.1).trans (U_normalized a))
    inf_le_right hZ hcomm

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
