module

public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Intersections
public import Stellmacher.ElementaryAbelianMaxNormalizerAction

/-!
# The ambient normalizer acts on the elementary square

Conjugation preserves intersection orders. The normalizer of the original
elementary Thompson subgroup therefore acts through the actual order-eight
intersection permutation group. If the stabilizer of the local two-core is
contained in the original Sylow, the kernel is a two-group, and hence so is
the entire normalizer. Sylow maximality then gives the source equality.

Source: Aschbacher–Smith, 13.9.2(2), printed p.969.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CFSG.Quasithin.Chapter13.Section09.Marking

open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

abbrev JNormalizer (_m : Marking d) : Subgroup G := normalizer (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) : Set G)

def squareAction : m.JNormalizer →* Equiv.Perm (Bool × Bool) :=
  m.maximumElementaryEquiv.symm.permCongrHom.toMonoidHom.comp
    (Stellmacher.maxJNormalizerAction (d.T : Subgroup G))

theorem squareAction_elementary (g : m.JNormalizer) (p : Bool × Bool) :
    m.elementaryGroup (m.squareAction g p).1 (m.squareAction g p).2 =
      (m.elementaryGroup p.1 p.2).map (MulAut.conj (g : G)).toMonoidHom := by
  have h := congrArg Subtype.val
    (m.maximumElementaryEquiv.apply_symm_apply
      (Stellmacher.maxJNormalizerAction (d.T : Subgroup G) g (m.maximumElementaryEquiv p)))
  exact h

theorem squareAction_mem_intersectionPerms (g : m.JNormalizer) :
    m.squareAction g ∈ SymmetricFourWreath.intersectionPerms := by
  apply SymmetricFourWreath.mem_intersectionPerms
  intro p q
  have hcard : Nat.card (m.elementaryGroup (m.squareAction g p).1 (m.squareAction g p).2 ⊓
      m.elementaryGroup (m.squareAction g q).1 (m.squareAction g q).2 : Subgroup G) =
      Nat.card (m.elementaryGroup p.1 p.2 ⊓ m.elementaryGroup q.1 q.2 : Subgroup G) := by
    rw [m.squareAction_elementary, m.squareAction_elementary,
      ← map_inf _ _ _ (MulAut.conj (g : G)).injective,
      card_map_of_injective (MulAut.conj (g : G)).injective]
  rw [SymmetricFourWreath.card_elementary_inf, SymmetricFourWreath.card_elementary_inf]
  rw [m.card_elementary_inf, m.card_elementary_inf] at hcard
  exact hcard

theorem squareAction_kernel_normalizes (g : m.JNormalizer) (hg : g ∈ m.squareAction.ker)
    (p : Bool × Bool) : (g : G) ∈ normalizer (m.elementaryGroup p.1 p.2 : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have heq : m.squareAction g = 1 := hg
  have h := m.squareAction_elementary g p
  rw [heq] at h
  exact h.symm

theorem sylow_le_JNormalizer : (d.T : Subgroup G) ≤ m.JNormalizer := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hT : (d.T : Subgroup G).map (MulAut.conj g).toMonoidHom = (d.T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((d.T : Subgroup G).le_normalizer hg)
  change (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G)).map
    (MulAut.conj g).toMonoidHom = _
  rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj g), hT]

/-- The actual square action reduces the normalizer equality to the local
stabilizer calculation, with no automorphism-group or classification premise. -/
theorem normalizer_eq_sylow_of_elementary_stabilizer
    (hstab : ∀ g : G, g ∈ m.JNormalizer →
      g ∈ normalizer (m.elementaryGroup true true : Set G) → g ∈ (d.T : Subgroup G)) :
    m.JNormalizer = (d.T : Subgroup G) := by
  have hker : IsPGroup 2 m.squareAction.ker := by
    let f : m.squareAction.ker →* d.T :=
      { toFun := fun g => ⟨g.1.1, hstab g.1.1 g.1.2
          (m.squareAction_kernel_normalizes g.1 g.2 (true, true))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply d.T.isPGroup'.of_injective f
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : d.T => (z : G)) h
  have hN : IsPGroup 2 m.JNormalizer := by
    intro g
    have hg := SymmetricFourWreath.intersectionPerms_isPGroup.comap_of_ker_isPGroup m.squareAction hker
    obtain ⟨n, hn⟩ := hg ⟨g, m.squareAction_mem_intersectionPerms g⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  exact d.T.is_maximal' hN m.sylow_le_JNormalizer

end CFSG.Quasithin.Chapter13.Section09.Marking
