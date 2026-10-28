module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# A chief section escaping a prescribed subgroup

Inside a finite group, the normal core of `N ∩ M` is the largest normal
subgroup of N contained in M. A minimal normal extension above it is a chief
section whose upper group escapes M. If M contains a Sylow two-subgroup, this
section cannot be a two-group: its image would lie in the image of that Sylow.
Normality always refers to the supplied ambient group, which may itself be a
local subgroup of a larger group.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.11, printed pp.213--214.
-/

public section
open Subgroup

namespace ChiefFactor
variable {G : Type*} [Group G] [Finite G]

theorem exists_chief_not_le (N M : Subgroup G) [N.Normal] (hNM : ¬ N ≤ M) :
    ∃ X : Subgroup G, IsChief X (N ⊓ M).normalCore ∧ X ≤ N ∧ ¬ X ≤ M := by
  let Y := (N ⊓ M).normalCore
  have hYN : Y ≤ N := (N ⊓ M).normalCore_le.trans inf_le_left
  have hYM : Y ≤ M := (N ⊓ M).normalCore_le.trans inf_le_right
  have hlt : Y < N := lt_of_le_not_ge hYN (fun h => hNM (h.trans hYM))
  obtain ⟨X, ⟨hXn, hYX, hXN⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun X : Subgroup G => X.Normal ∧ Y < X ∧ X ≤ N) ⟨N, inferInstance, hlt, le_rfl⟩
  let _ := hXn
  refine ⟨X, ⟨hXn, inferInstance, hYX, ?_⟩, hXN, ?_⟩
  · intro Z hZn hYZ hZX
    by_cases he : Z = Y
    · exact Or.inl he
    · exact Or.inr (le_antisymm hZX (hmin ⟨hZn, lt_of_le_of_ne hYZ (Ne.symm he),
        hZX.trans hXN⟩ hZX))
  · intro hXM
    exact hYX.not_ge (normal_le_normalCore.mpr (le_inf hXN hXM))

theorem le_sup_sylow_of_quotient_isPGroup (T : Sylow 2 G)
    (X Y : Subgroup G) [X.Normal] [Y.Normal]
    (hp : IsPGroup 2 (X ⧸ Y.subgroupOf X)) : X ≤ Y ⊔ (T : Subgroup G) := by
  let q := QuotientGroup.mk' Y
  let _ : (X.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective Y)
  have hq : X.map q ≤ (T : Subgroup G).map q :=
    (hp.of_equiv (quotientImageEquiv X Y)).le_sylow_of_normal
      (T.mapSurjective (f := q) (QuotientGroup.mk'_surjective Y))
  have h := (le_comap_map q X).trans (comap_mono hq)
  rwa [comap_map_eq, QuotientGroup.ker_mk', sup_comm] at h

theorem not_isPGroup_of_not_le (T : Sylow 2 G) (X Y M : Subgroup G)
    [X.Normal] [Y.Normal] (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hXM : ¬ X ≤ M) : ¬ IsPGroup 2 (X ⧸ Y.subgroupOf X) :=
  fun hp => hXM ((le_sup_sylow_of_quotient_isPGroup T X Y hp).trans (sup_le hYM hTM))

/-- A chief section which is not a p-group is covered by the p-residual of
its upper group. The residual is intrinsic before it is mapped into G. -/
theorem IsChief.embedded_pResidual_sup_eq {p : ℕ} {X Y : Subgroup G} [Y.Normal]
    (h : IsChief X Y) (hp : ¬ IsPGroup p (X ⧸ Y.subgroupOf X)) :
    (pResidual p X).map X.subtype ⊔ Y = X := by
  let _ := h.normal_upper
  let R := (pResidual p X).map X.subtype
  have hRX : R ≤ X := map_subtype_le _
  rcases h.minimal (R ⊔ Y) inferInstance le_sup_right (sup_le hRX h.lt.le) with he | he
  · exfalso
    apply hp
    have hRY : pResidual p X ≤ Y.subgroupOf X :=
      map_le_iff_le_comap.mp ((show R ≤ R ⊔ Y from le_sup_left).trans he.le)
    let f := QuotientGroup.map (pResidual p X) (Y.subgroupOf X) (MonoidHom.id X) hRY
    exact (isPGroup_quotient_pResidual p).of_surjective f
      (QuotientGroup.map_surjective_of_surjective (pResidual p X) (Y.subgroupOf X)
        (MonoidHom.id X) (QuotientGroup.mk_surjective.comp Function.surjective_id) hRY)
  · exact he


end ChiefFactor
