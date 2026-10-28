module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ResidualAction

/-!
# The actual normalizer in the central-action branch

The actor is N_K(S), with S = Baum(T). Under the genuine 13.6.5
normalizer bound and M = N_G(L) from 13.3.2, it normalizes both V and
L_v = O²(C_L(v)). The latter follows by characteristic residual transport.
In particular its two-residual normalizes the literal [V,L_v].

The final theorem constructs the surjection to the model parabolic from
an equality of the actual action image, restricts the single chosen
module marking, and applies the residual obstruction. The source proof
must still supply the parabolic-image equality and the split-point
commutator formula; they are separate, explicit premises here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
13.3.2(2), printed p.885; 13.6.5 and 13.6.20, pp.926 and 931.
-/

@[expose] public section

open Subgroup Representation BinaryLinearThree BinaryLinearThree.DoubledParabolic
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
open ComponentSelection
variable {G : Type*} [_root_.Group G]

/-- The source actor is the relative normalizer N_K(S), where S = Baum(T). -/
def componentNormalizer (K T : Subgroup G) : Subgroup G :=
  K ⊓ normalizer (ChapterB.baumann T : Set G)

/-- Normalizing L and fixing v preserves its literal two-residual L_v. -/
theorem normalizes_Lv_of_normalizes_L (H L : Subgroup G) (v : G)
    (hHL : H ≤ normalizer (L : Set G)) (hHv : H ≤ Gv v) :
    H ≤ normalizer (Lv L v : Set G) := by
  have hn : H ≤ normalizer ((L ⊓ Gv v : Subgroup G) : Set G) :=
    (le_inf hHL (hHv.trans (Gv v).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (L ⊓ Gv v) (pResidual 2 (L ⊓ Gv v : Subgroup G)))

/-- Both normalization assertions follow from 13.6.5 and the source
identification M = N_G(L) in 13.3.2. No action of the residual on the full
S₄ parabolic is assumed. -/
theorem componentNormalizer_normalizes (K L V T : Subgroup G) (v : G)
    (hK : K ≤ Gv v)
    (h1365 : Gv v ⊓ normalizer (ChapterB.baumann T : Set G) ≤
      Mv (normalizer (L : Set G)) v)
    (hlocal : Mv (normalizer (L : Set G)) v = normalizer (V : Set G) ⊓ Gv v) :
    componentNormalizer K T ≤ normalizer (V : Set G) ∧
      componentNormalizer K T ≤ normalizer (Lv L v : Set G) := by
  have hc : componentNormalizer K T ≤ Mv (normalizer (L : Set G)) v :=
    (inf_le_inf_right _ hK).trans h1365
  exact ⟨hc.trans (hlocal.le.trans inf_le_left),
    normalizes_Lv_of_normalizes_L _ L v (hc.trans inf_le_left)
      (inf_le_left.trans hK)⟩

/-- The terminal obstruction for the actual normalizer and actual U_K.
The two unproved geometric inputs are displayed separately: the image of
N_K(S) in the chosen action, and the split-point description of [V,L_v]. -/
theorem false_of_componentNormalizer_geometry [Finite G]
    (K L V T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (d : DoubledCoordinates K L T z v hK hL hz)
    (h1365 : Gv v ⊓ normalizer (ChapterB.baumann T : Set G) ≤
      Mv (normalizer (L : Set G)) v)
    (hlocal : Mv (normalizer (L : Set G)) v = normalizer (V : Set G) ⊓ Gv v)
    (himage : (d.actionMap.comp
      (inclusion (show componentNormalizer K T ≤ K from inf_le_left))).range =
        Matrix.PSL3Two.lineParabolicSL)
    (x y : Vector) (hx : x 2 = 0) (hn : x ≠ 0)
    (hQ : ((⁅V, Lv L v⁆ : Subgroup G).subgroupOf (UK K L T z v)).map
      d.moduleEquiv.toMonoidHom = (splitPlane x y).toAddSubgroup.toSubgroup) : False := by
  let P := componentNormalizer K T
  let f := d.actionMap.comp (inclusion (show P ≤ K from inf_le_left))
  let π : P →* Matrix.PSL3Two.lineParabolicSL :=
    f.codRestrict _ (fun p => himage ▸ (show f p ∈ f.range from ⟨p, rfl⟩))
  have hπ : Function.Surjective π := by
    intro g
    have hg : (g : BinaryLinearThree.Group) ∈ f.range := himage.symm ▸ g.property
    obtain ⟨p, hp⟩ := hg
    exact ⟨p, Subtype.ext hp⟩
  have hc := componentNormalizer_normalizes K L V T v hK h1365 hlocal
  exact doubled_natural_residual_commutator_contradiction L V P (UK K L T z v) v
    (inf_le_left.trans (K_normalizes_UK K L T z v hL hz)) π hπ d.moduleEquiv
    (fun p u => d.equivariant_restrict P inf_le_left p u) x y hx hn hQ hc.1
    ((map_subtype_le _).trans hc.2)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
