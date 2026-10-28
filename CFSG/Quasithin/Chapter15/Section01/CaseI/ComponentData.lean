module

public import CFSG.Quasithin.Chapter15.Section01.CaseI.Control
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Literal component data for Case I of original 15.1.15

The remaining Case-I source argument works inside the centralizer of the
actual marked subgroup `Z₁`.  This interface records that subgroup and the
component supplied by the source 15.1.19 step.  All ambient groups and maps
are literal subgroups of `G`: no abstract replacement for the chosen module
or for `C_G(Z₁)` is introduced.  The later component/model leaves can extend
this record with the source alternatives from 15.1.20--29.

Source: Aschbacher--Smith 15.1.15--19, printed pp.1091--1094.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1 ChapterB Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The three source rows excluded by original 15.1.15. -/
inductive CaseIRow
  | four
  | six
  | seven

/-- The literal common component data in source 15.1.19. -/
structure CaseIComponentData (T : Sylow 2 G)
    (M Mc V : Subgroup G) where
  row : CaseIRow
  Z1 : Subgroup G
  Z1_le_fixed : Z1 ≤ thompsonFixed T V
  Z1_ne_bot : Z1 ≠ ⊥
  /-- `M = ⟨C_M(Z₁), T⟩`, with the generated subgroup written as a join. -/
  M_eq_centralizer_sup_sylow :
    M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G)
  L : Subgroup G
  L_component : L ∈ cComponentsIn (centralizer (Z1 : Set G))
  L_not_le_MZ : ¬ L ≤ (centralizer (Z1 : Set G)) ⊓ Mc

namespace CaseIComponentData

variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal `S = T ∩ C_G(Z₁)` in 15.1.17. -/
@[expose] def S (d : CaseIComponentData T M Mc V) : Subgroup G :=
  T ⊓ centralizer (d.Z1 : Set G)

/-- The literal `G₁ = C_G(Z₁)` in 15.1.19. -/
@[expose] def G1 (d : CaseIComponentData T M Mc V) : Subgroup G :=
  centralizer (d.Z1 : Set G)

/-- The literal `M_Z = G₁ ∩ M_c` in 15.1.18. -/
@[expose] def MZ (d : CaseIComponentData T M Mc V) : Subgroup G :=
  d.G1 ⊓ Mc

/-- The literal `Q₁ = O₂(M_Z)` in 15.1.18. -/
@[expose] def Q1 (d : CaseIComponentData T M Mc V) : Subgroup G :=
  pCoreIn 2 d.MZ

/-- The source intersection `S_L = S ∩ L`. -/
@[expose] def SL (d : CaseIComponentData T M Mc V) : Subgroup G :=
  d.S ⊓ d.L

/-- The source intersection `M_L = M_Z ∩ L`. -/
@[expose] def ML (d : CaseIComponentData T M Mc V) : Subgroup G :=
  d.MZ ⊓ d.L

theorem S_le_T (d : CaseIComponentData T M Mc V) : d.S ≤ T :=
  inf_le_left

theorem S_le_G1 (d : CaseIComponentData T M Mc V) : d.S ≤ d.G1 :=
  inf_le_right

theorem ML_le_MZ (d : CaseIComponentData T M Mc V) : d.ML ≤ d.MZ :=
  inf_le_left

theorem SL_le_S (d : CaseIComponentData T M Mc V) : d.SL ≤ d.S :=
  inf_le_left

theorem SL_le_L (d : CaseIComponentData T M Mc V) : d.SL ≤ d.L :=
  inf_le_right

theorem Q1_le_MZ (d : CaseIComponentData T M Mc V) : d.Q1 ≤ d.MZ :=
  pCoreIn_le 2 _

theorem L_not_le_Mc (d : CaseIComponentData T M Mc V) : ¬ d.L ≤ Mc := by
  intro hL
  apply d.L_not_le_MZ
  exact le_inf d.L_component.1 hL

theorem L_isCComponent_in_G1 (d : CaseIComponentData T M Mc V) :
    (d.L.subgroupOf d.G1).IsCComponent := d.L_component.2

end CaseIComponentData

end CFSG.Quasithin.Chapter15.Section01
