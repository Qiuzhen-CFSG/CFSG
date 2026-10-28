module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Automorphisms of a marked block module

Automorphisms of L preserve both U(L)=[O₂(L),L] and its central fixed
subgroup. They therefore act on the actual quotient module and on L/O₂(L).
Transport through a BlockModuleModel gives compatible automorphisms of the
prescribed actor and natural module, without requiring a split extension.

This is the equivariance used for the two invariant parabolics in
Aschbacher–Smith, 15.3.20, printed p.1127.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {L A V : Type*} [Group L] [Group A] [Group V]

private theorem blockFixed_characteristic_map (a : MulAut L) :
    (blockFixed L).map (MulAut.characteristic (blockU L) a).toMonoidHom = blockFixed L := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.centerCongr a ⟨u, hu⟩).property
  · intro u hu
    refine ⟨MulAut.characteristic (blockU L) a.symm u, ?_, ?_⟩
    · exact (Subgroup.centerCongr a).symm ⟨u, hu⟩ |>.property
    · apply Subtype.ext
      exact a.apply_symm_apply u

/-- Automorphisms act on the actual quotient U(L)/C_U(L). -/
def blockModuleAut : MulAut L →* MulAut (BlockModule L) where
  toFun a := QuotientGroup.congr _ _ (MulAut.characteristic (blockU L) a)
    (blockFixed_characteristic_map a)
  map_one' := by
    ext u
    induction u using Quotient.inductionOn with
    | h u => rfl
  map_mul' a b := by
    ext u
    induction u using Quotient.inductionOn with
    | h u => rfl

@[simp] theorem blockModuleAut_apply_mk (a : MulAut L) (u : blockU L) :
    blockModuleAut a (QuotientGroup.mk' (blockFixed L) u) =
      QuotientGroup.mk' (blockFixed L) (MulAut.characteristic (blockU L) a u) := by rfl

namespace BlockModuleModel
variable {ρ : A →* MulAut V} (m : BlockModuleModel L ρ)

/-- The model quotient actor retains the literal quotient by O₂. -/
def actor : L →* A :=
  m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem actor_surjective : Function.Surjective m.actor :=
  m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The induced model automorphism of the core quotient. -/
def quotientAction : MulAut L →* MulAut A :=
  (MulAut.congr m.quotientIso).toMonoidHom.comp (quotientAut (pCore 2 L))

/-- The induced model automorphism of the natural module quotient. -/
def moduleAction : MulAut L →* MulAut V :=
  (MulAut.congr m.moduleIso).toMonoidHom.comp blockModuleAut

@[simp] theorem quotientAction_actor (a : MulAut L) (l : L) :
    m.quotientAction a (m.actor l) = m.actor (a l) := by
  change m.quotientIso (quotientAut (pCore 2 L) a
    (m.quotientIso.symm (m.quotientIso (QuotientGroup.mk' _ l)))) = _
  rw [m.quotientIso.symm_apply_apply, quotientAut_apply_mk]
  rfl

@[simp] theorem moduleAction_mk (a : MulAut L) (u : blockU L) :
    m.moduleAction a (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)) =
      m.moduleIso (QuotientGroup.mk' (blockFixed L) (MulAut.characteristic (blockU L) a u)) := by
  change m.moduleIso (blockModuleAut a
    (m.moduleIso.symm (m.moduleIso (QuotientGroup.mk' _ u)))) = _
  rw [m.moduleIso.symm_apply_apply, blockModuleAut_apply_mk]

/-- The two induced automorphisms intertwine the actual model action. -/
theorem actions_compatible (a : MulAut L) (g : A) (v : V) :
    m.moduleAction a (ρ g v) = ρ (m.quotientAction a g) (m.moduleAction a v) := by
  obtain ⟨l, rfl⟩ := m.actor_surjective g
  obtain ⟨u, rfl⟩ := m.moduleIso.surjective.comp
    (QuotientGroup.mk'_surjective (blockFixed L)) v
  dsimp only [Function.comp_apply]
  have hm (k : L) (w : blockU L) :
      m.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L k w)) =
        ρ (m.actor k) (m.moduleIso (QuotientGroup.mk' (blockFixed L) w)) :=
    m.intertwining k w
  rw [← hm, moduleAction_mk, quotientAction_actor, moduleAction_mk]
  have he : MulAut.characteristic (blockU L) a (blockConjugate L l u) =
      blockConjugate L (a l) (MulAut.characteristic (blockU L) a u) := by
    apply Subtype.ext
    change a (l * (u : L) * l⁻¹) = a l * a (u : L) * (a l)⁻¹
    simp only [map_mul, map_inv]
  rw [he]
  exact m.intertwining (a l) _
end BlockModuleModel
end CFSG.Quasithin.ChapterC
