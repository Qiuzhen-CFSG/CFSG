module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PGroup.Omega
public import Stellmacher.OmegaOneCenterMap

/-!
# Centers under a Sylow omega-center join

Let H contain an ambient Sylow two-subgroup T and have self-centralizing
two-core. If K centralizes Ω₁Z(T) and O₂(HK)=1, then Z(H)=1.
Indeed Z(H) is a two-group. Its first omega subgroup lies in Ω₁Z(T)
and is centralized by both H and K, hence is a normal two-subgroup of
their join. A nontrivial finite two-group has nontrivial first omega.

This is the center argument in Aschbacher–Smith 5.1.7(2iii), specialized
in the opening of 13.2.12, printed p.881. The join is a subgroup join;
no permutability of H and K is needed.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A core-free join with a centralizer of the Sylow omega-center forces
the characteristic-two factor to have trivial center. -/
theorem center_eq_bot_of_join_core_eq_bot
    (T : Sylow 2 G) (H K : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hKZ : K ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ K).pCoreIn 2 = ⊥) : center H = ⊥ := by
  by_contra hz
  have hZQ : center H ≤ pCore 2 H := (center_le_centralizer _).trans hc
  have hZp : IsPGroup 2 (center H) := pCore_isPGroup.to_le hZQ
  have hcard : 2 ∣ Nat.card (center H) := hZp.card_eq_or_dvd.resolve_left (by
    intro he
    exact hz (Subgroup.card_eq_one.mp he))
  let E₀ := (omega₁ (center H) (p := 2)).map (center H).subtype
  let E := E₀.map H.subtype
  have hEne : E ≠ ⊥ := by
    intro he
    exact omega₁_map_subtype_ne_bot (center H) 2 hcard
      ((E₀.map_eq_bot_iff_of_injective H.subtype_injective).mp he)
  have hEH : E ≤ H := map_subtype_le _
  have hEC : E ≤ centralizer (H : Set G) := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩ h hh
    exact congrArg H.subtype (mem_center_iff.mp z.property ⟨h, hh⟩)
  have hET : E ≤ (T : Subgroup G) := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) (hZQ z.property)
  have hEZ : E ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    intro x hx
    have hex : IsElementaryAbelian 2 E := by
      let : IsElementaryAbelian 2 (omega₁ (center H) (p := 2)) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative _
      exact (IsElementaryAbelian.map (p := 2) (center H).subtype).map H.subtype
    let := hex
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hET hx, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,
        fun t ht => hEC hx t (hTH ht)⟩
  have hgen : H ⊔ K ≤ centralizer (E : Set G) :=
    sup_le (le_centralizer_iff.mp hEC) (hKZ.trans (centralizer_le hEZ))
  have hpE : IsPGroup 2 E := T.isPGroup'.to_le hET
  have hEq : E ≤ (H ⊔ K).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hpE (hEH.trans le_sup_left)
      (hgen.trans (Subgroup.centralizer_le_normalizer _))
  exact hEne (bot_unique (hEq.trans_eq hcore))

end Theory.GroupTheory
