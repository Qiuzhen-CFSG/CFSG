module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionFacts
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerQuotient
public import Theory.GroupTheory.SpecificGroups.SymmetricFourProductResidualCore

/-!
# The literal residual-core join in F.5.5

Each endpoint contributes O₂(O²(Dᵢ)), with both subgroup inclusions retained.
The C₂ × S₄ endpoint comparisons identify these as four-groups and preserve
an explicit inverse model map. Their join lies in O²(C_G(f)); its image
under the actual quotient by the central graph involution lies in the
quotient's two-residual. The independent eight-matrix calculation identifies
that join and its quotient image as dihedral groups of order eight.

Source: Aschbacher–Smith F.5.5, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

/-- The literal O₂(O²(Dᵢ)) in the F.5.5 source. -/
def sourceEndpointResidualCore (b : Bool) : Subgroup G :=
  (pCore 2 (pResidual 2 (Dendpoint c i b))).map
    ((Dendpoint c i b).subtype.comp (pResidual 2 (Dendpoint c i b)).subtype)

/-- The source group U in the successive transfer argument. -/
def sourceResidualJoin : Subgroup G :=
  sourceEndpointResidualCore c i false ⊔ sourceEndpointResidualCore c i true

theorem sourceEndpointResidualCore_le_D (b : Bool) :
    sourceEndpointResidualCore c i b ≤ Dendpoint c i b := by
  rintro _ ⟨a,ha,rfl⟩
  exact a.val.property

theorem sourceResidualJoin_le_C : sourceResidualJoin c i ≤ C c i :=
  sup_le ((sourceEndpointResidualCore_le_D c i false).trans
    ((Dendpoint_le_E c i false).trans inf_le_right))
    ((sourceEndpointResidualCore_le_D c i true).trans
      ((Dendpoint_le_E c i true).trans inf_le_right))

/-- The source graph-quotient image uses the actual subgroup inclusion. -/
def sourceResidualJoinQuotient : Subgroup (graphCentralQuotient c i) :=
  ((sourceResidualJoin c i).subgroupOf (C c i)).map
    (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))

theorem sourceResidualJoin_le_twoResidual :
    sourceResidualJoin c i ≤ (pResidual 2 (C c i)).map (C c i).subtype := by
  have hb (b : Bool) : sourceEndpointResidualCore c i b ≤
      (pResidual 2 (C c i)).map (C c i).subtype := by
    rintro _ ⟨a,ha,rfl⟩
    let j : Dendpoint c i b →* C c i := inclusion ((Dendpoint_le_E c i b).trans inf_le_right)
    exact ⟨j a.val,map_pResidual_le 2 j (mem_map_of_mem j a.property),rfl⟩
  exact sup_le (hb false) (hb true)

theorem sourceResidualJoinQuotient_le_twoResidual :
    sourceResidualJoinQuotient c i ≤ pResidual 2 (graphCentralQuotient c i) := by
  apply le_trans (map_mono ?_) (map_pResidual_le 2 _)
  intro a ha
  have hh := sourceResidualJoin_le_twoResidual c i ha
  exact (mem_map_iff_mem (C c i).subtype_injective).mp hh

variable [Finite G]

def sourceEndpointCoreMap (hi : Function.Injective i) (b : Bool) : S4 →* G :=
  (Dendpoint c i b).subtype.comp
    ((source_Dendpoint_equiv c i hi b).symm.toMonoidHom.comp (MonoidHom.inr C2 S4))

omit [Finite G] in
theorem sourceEndpointCoreMap_injective (hi : Function.Injective i) (b : Bool) :
    Function.Injective (sourceEndpointCoreMap c i hi b) :=
  (Dendpoint c i b).subtype_injective.comp
    ((source_Dendpoint_equiv c i hi b).symm.injective.comp (by
      intro a b h; exact congrArg Prod.snd h))

theorem sourceEndpointResidualCore_eq_map (hi : Function.Injective i) (b : Bool) :
    sourceEndpointResidualCore c i b = core.map (sourceEndpointCoreMap c i hi b) := by
  rw [sourceEndpointResidualCore,←map_map,
    SymmetricFourResidualCore.residual_core_image (source_Dendpoint_equiv c i hi b),map_map]
  rfl

theorem sourceEndpointResidualCore_card (hi : Function.Injective i) (b : Bool) :
    Nat.card (sourceEndpointResidualCore c i b)=4 := by
  rw [sourceEndpointResidualCore_eq_map c i hi b,
    card_map_of_injective (sourceEndpointCoreMap_injective c i hi b),core_card]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
