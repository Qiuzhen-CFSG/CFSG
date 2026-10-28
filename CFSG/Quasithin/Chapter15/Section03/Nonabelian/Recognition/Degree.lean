module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.ChapterG.Section09.Setup

/-!
# Degree restrictions for the G.9.3 application in 15.3.58

The degree `2(s+2)` excludes every odd-degree model. In particular the
corrected G.9.3(14) identification of the **component join's** action with
the nine-dimensional tensor action is already impossible. This does not
require identifying the whole actor with the direct product of components.
Positivity of `s`, proved separately from 15.3.54(4) and 15.3.9, also
excludes every model of degree at most four.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149;
G.9.3(14), pp.354,356, with the component-action correction recorded in
`docs/quasithin-proof-basis.md`.
-/

public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (s : ℕ) (hdim : Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2))

include hdim

/-- Every odd-degree alternative is incompatible with 15.3.56(2). -/
theorem degree_ne_odd (d : ℕ) (hd : Odd d) :
    Module.finrank (ZMod 2) (Space Z ZS) ≠ d := by
  obtain ⟨n, hn⟩ := hd
  omega

/-- In particular, the corrected two-component tensor branch has wrong parity. -/
theorem degree_ne_nine : Module.finrank (ZMod 2) (Space Z ZS) ≠ 9 := by
  omega

/-- The source's positive multiplicity excludes the small-degree branches. -/
theorem six_le_degree (hs : 0 < s) :
    6 ≤ Module.finrank (ZMod 2) (Space Z ZS) := by
  omega

/-- Exclude the corrected G.9.3(14) at the action of the actual component join,
without making any assertion about the full actor being a direct product. -/
theorem component_action_not_quasiequivalent_nine
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (K : Subgroup (ActorQuotient Z))
    {D M : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) D M) (hσ : Module.finrank (ZMod 2) M = 9) :
    ¬ CFSG.Quasithin.ChapterG.Section09.Quasiequivalent
      ((actorRepresentation Z ZS hkernel).comp K.subtype) σ := by
  rintro ⟨_, e, _⟩
  exact degree_ne_nine Z ZS s hdim (e.finrank_eq.trans hσ)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
