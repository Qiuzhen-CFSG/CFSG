module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupSylow
public import CFSG.Quasithin.Chapter10.SourceBlockTerminalAction
/-!
# The actual Borel normalizer in the natural generation argument

A nontrivial two-core of the Borel A stays normal inside N_G(A), so that
normalizer has nontrivial two-core and lies in an actual two-local overgroup.
It inherits the full known-simple SQTK condition. If it contains the original
L and T₁ but an escaping K, the existing original half-Sylow promotion proves
that T₁ is Sylow in it. Applying this to the opposite Borel S₂D₂ avoids
changing the original fundamental setup.

The final source consumer derives SQTK internally and applies the special64
centralization and cubic-rank contradiction to the actual normalizer.
Source: Aschbacher–Smith 10.2.3(4), printed p.747, using 1.2.7 and 9.3.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem normalizer_core_ne_bot (A : Subgroup G) (hA : pCore 2 A ≠ ⊥) :
    pCore 2 (normalizer (A : Set G)) ≠ ⊥ := by
  have hQ : A.pCoreIn 2 ≠ ⊥ := fun he => hA
    ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp he)
  have hle : A.pCoreIn 2 ≤ (normalizer (A : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
      ((pCoreIn_le 2 A).trans A.le_normalizer)
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  intro he
  apply hQ
  apply bot_unique
  exact hle.trans (by change (pCore 2 (normalizer (A : Set G))).map _ ≤ ⊥; simp [he])

/-- The actual Borel normalizer inherits SQTK from its nontrivial two-core. -/
theorem source_natural_borel_normalizer_sqtk
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hA : pCore 2 A ≠ ⊥) :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (A : Set G)) := by
  obtain ⟨M,hM,hNM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (normalizer (A : Set G)) (normalizer_core_ne_bot A hA)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hNM)).mp
    ((D.simpleQTKE.twoLocal_sqtk hM.1).subgroup ((normalizer (A : Set G)).subgroupOf M))

/-- An opposite Borel normalizer containing the original component and an escaping
component has the prescribed half-Sylow subgroup. -/
theorem source_natural_borel_normalizer_sylow
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (A K : Subgroup G) (hA : pCore 2 A ≠ ⊥)
    (hL : L ≤ normalizer (A : Set G))
    (hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G))
    (hK : K ≤ normalizer (A : Set G)) (hout : ¬ K ≤ D.maximalLocal) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (normalizer (A : Set G)) ∧
      IsSQTK KnownSimple.IsKnownSimple (normalizer (A : Set G)) := by
  exact ⟨source_a5_local_outside_overgroup_sylow D e hn
    (normalizer_core_ne_bot A hA) hL hR (fun he => hout (hK.trans he)),
    source_natural_borel_normalizer_sqtk D A hA⟩

/-- The original simple QTKE hypotheses discharge the terminal normalizer's
SQTK premise; its actual special core and linear-three overcomponent contradict. -/
theorem source_natural_borel_terminal_contradiction
    (D₀ : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (D K S : Subgroup G)
    [IsElementaryAbelian 2 (center (pCore 2 (S ⊔ D : Subgroup G)))]
    (hfaithful : D ⊓ centralizer (S : Set G) = ⊥)
    (hD : Nat.card D = 3)
    (hS : Nat.card (pCore 2 (S ⊔ D : Subgroup G)) = 64)
    (hderived : commutator (pCore 2 (S ⊔ D : Subgroup G)) =
      center (pCore 2 (S ⊔ D : Subgroup G)))
    (hZ : Nat.card (center (pCore 2 (S ⊔ D : Subgroup G))) = 4)
    (hquot : Nat.card ((S ⊔ D : Subgroup G) ⧸ pCore 2 (S ⊔ D : Subgroup G)) = 3)
    (hm : Chapter1.Section02.LocalModels.IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4)
    (hn : K ≤ normalizer ((S ⊔ D : Subgroup G) : Set G)) : False := by
  have hcore : pCore 2 (S ⊔ D : Subgroup G) ≠ ⊥ := by
    intro he
    rw [he] at hS
    norm_num at hS
  exact source_block_borel_contradiction_of_special_core D K S
    (source_natural_borel_normalizer_sqtk D₀ (S ⊔ D) hcore)
    hfaithful hD hS hderived hZ hquot hm hn
end CFSG.Quasithin.Chapter10
