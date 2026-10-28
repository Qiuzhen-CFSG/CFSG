module
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Nontrivial cores in residuals of Sylow overgroups

In a finite group of characteristic p, the ambient p-core normalizes the
p-residual of each subgroup containing a Sylow p-subgroup. Characteristic-p
inheritance gives F*(R)=O_p(R). If the overgroup properly contains the
Sylow subgroup then R is nontrivial by the residual/Sylow supplement, so
self-centralization forces O_p(R) to be nontrivial as well.

Source application: Aschbacher--Smith, 10.2.9, printed p.753. This supplies
the actual two-local normalizer containing the terminal residual product.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

/-- A proper overgroup of a Sylow subgroup has nontrivial residual. -/
theorem embedded_pResidual_ne_bot_of_sylow_lt (S : Sylow p H) (P : Subgroup H)
    (hSP : (S : Subgroup H) < P) : (pResidual p P).map P.subtype ≠ ⊥ := by
  intro he
  have hs := congrArg (Subgroup.map P.subtype)
    (pResidual_sup_sylow_eq_top (S.subtype hSP.le))
  rw [Subgroup.map_sup,he,bot_sup_eq,←MonoidHom.range_eq_map,range_subtype] at hs
  have hm : ((S.subtype hSP.le : Sylow p P) : Subgroup P).map P.subtype = S := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hx
      exact ⟨⟨x,hSP.le hx⟩,hx,rfl⟩
  rw [hm] at hs
  exact hSP.ne hs

/-- In characteristic p, the residual of a proper Sylow overgroup has a
nontrivial intrinsic p-core, giving an actual local normalizer. -/
theorem pCore_embedded_pResidual_ne_bot_of_sylow_lt
    (hc : generalizedFitting H = pCore p H) (S : Sylow p H) (P : Subgroup H)
    (hSP : (S : Subgroup H) < P) :
    pCore p ((pResidual p P).map P.subtype) ≠ ⊥ := by
  let R := (pResidual p P).map P.subtype
  have hn : pCore p H ≤ normalizer (R : Set H) :=
    (pCore_isPGroup.le_sylow_of_normal S).trans (hSP.le.trans
      (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pResidual p P))))
  have hR := generalizedFitting_eq_pCore_of_normalized_by_pCore R hc hn
  intro he
  have hz : generalizedFitting R = ⊥ := hR.trans he
  have hh := centralizer_generalizedFitting_le R
  rw [hz] at hh
  have htop : (⊤ : Subgroup R) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x _
    apply hh
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  have heR : R = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : (⟨x,hx⟩ : R) ∈ (⊥ : Subgroup R) := htop ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hh)
  exact embedded_pResidual_ne_bot_of_sylow_lt S P hSP heR
end Theory.GroupTheory
