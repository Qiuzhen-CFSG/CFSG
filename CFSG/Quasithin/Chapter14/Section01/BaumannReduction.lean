module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The centralizing case of Lemma 14.1.2

An elementary abelian normal subgroup `V` of a local overgroup `M` lies
in its Sylow two-subgroup `T`. If `J(T)` centralizes `V`, the maximum
elementary abelian subgroup argument places `V` in `E = Ω₁(Z(J(T)))`.
Baumann heredity then identifies `Baum(T)` with `Baum(C_T(V))`.

These are precisely the two conclusions of 14.1.2(1). Only elementary
abelianness and relative normality from `V ∈ R₂(M)` are needed here;
the theorem therefore states those weaker inputs explicitly. It does not
use the legacy `LocalData` or require `L_f(G,T)` to be empty.
The maximal-overgroup assertions of 14.1.2(2) remain separate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp. 975–976, Lemma 14.1.2(1),
using B.2.3(5).
-/

namespace CFSG.Quasithin.Chapter14.Source

open Subgroup Stellmacher
open CFSG.Quasithin.ChapterB

variable {G : Type*} [Group G] [Finite G]

/-- Source 14.1.2(1), with only the elementary and relative-normality
properties of `R₂(M)` needed by the proof. Normality is inside `M`, not `G`. -/
public theorem lemma_14_1_2_1 (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      M ⊓ centralizer (V : Set G)) :
    V ≤ thompsonAlpha (T : Subgroup G) ∧
      baumann (T : Subgroup G) =
        baumann ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
  have hVT : V ≤ (T : Subgroup G) := by
    have hp : IsPGroup 2 (V.subgroupOf M) :=
      (IsElementaryAbelian.isPGroup 2 V).of_equiv (subgroupOfEquivOfLe hVM).symm
    have hle := hp.le_sylow_of_normal (T.subtype hTM)
    intro v hv
    exact hle (show (⟨v, hVM hv⟩ : M) ∈ V.subgroupOf M from hv)
  have hJC := hJ.trans inf_le_right
  exact ⟨elementary_centralizer_maxJ_le_omegaCenter _ V hVT
      (le_centralizer_iff.mp hJC),
    lemma_B_2_3_5 _ V hVT hJC⟩

end CFSG.Quasithin.Chapter14.Source
