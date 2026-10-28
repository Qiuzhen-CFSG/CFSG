module

public import CFSG.Quasithin.Chapter6.SourceDefs
public import CFSG.Quasithin.Chapter6.Section01.EscapeDefs

/-!
# Constructions for the final size argument in §6.1

`L0` and `F` are the actual subgroups constructed in Lemma 6.1.26:
`L0 = ⟨V_L^g,V_L^(gl)⟩` and `F = C_E(L0)`. Conjugation here is right
conjugation, as in `Escape.L1`. The centrality of `Z_S` in `U` follows
from its centrality in the generating layer and from `I = C_G(Z_S)`.
In particular, the terminal quotient is the group `U/Z_S` with its
relative normality proved, not a replacement vector space.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 6.1.26 and Theorem 6.1.27, printed pp.678–679.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter6.Source.Escape

open Subgroup
variable {G : Type*} [Group G]

/-- The two specified conjugates generating the source's `L₀`. -/
def L0 (L V : Subgroup G) (g l : G) : Subgroup G :=
  (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ⊔
    (layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom

/-- The centralizer inside the constructed intersection `E`. -/
def F (T L V : Subgroup G) (g l : G) : Subgroup G :=
  E T L V l ⊓ centralizer (L0 L V g l : Set G)

theorem ZS_le_U (T L V : Subgroup G) : ZS T L V ≤ U T L V :=
  inf_le_left.trans (layer_le_U T L V)

theorem U_centralizes_ZS {T L V : Subgroup G}
    (hV : layer L V ≤ centralizer (ZS T L V : Set G)) :
    U T L V ≤ centralizer (ZS T L V : Set G) := by
  apply iSup_le
  intro g x hx
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hx
  exact (I T L V).mul_mem ((I T L V).mul_mem g.property (hV hv))
    ((I T L V).inv_mem g.property)

theorem ZS_normal_in_U {T L V : Subgroup G}
    (hV : layer L V ≤ centralizer (ZS T L V : Set G)) :
    ((ZS T L V).subgroupOf (U T L V)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (ZS_le_U T L V)).mpr
    ((U_centralizes_ZS hV).trans (centralizer_le_normalizer _))

/-- The equality case in the conditional wording of Lemma 6.1.26 needs
no orbit argument: `F ≤ E = V_L` already gives the required splitting. -/
theorem split_of_E_eq_layer {T L V : Subgroup G} {g l : G}
    (hE : E T L V l = layer L V) :
    E T L V l = layer L V ⊔ F T L V g l := by
  rw [← hE]
  exact (sup_eq_left.mpr inf_le_left).symm

end CFSG.Quasithin.Chapter6.Source.Escape
