module
public import Theory.GroupTheory.NormalSylowQuotientAction.InvariantLift
import all Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The marked action on a core quotient and its invariant lifts

The normalizer of K acts on K/Oₚ(K). Transporting this action through a
fixed model isomorphism gives an actual marked action, with its quotient
intertwining equation. A Sylow subgroup normalizing K preserves its quotient
Sylow; any subgroup fixed by that actual action lifts to a normalized
subgroup. Solvability then passes to the lift together with the Sylow.

Source application: the diagram action in Aschbacher--Smith 14.6.20, p.1037.
-/

public section
open Subgroup
namespace Subgroup.NormalSylowQuotientAction
variable {G B : Type*} [Group G] [Group B]

/-- Conjugation on the characteristic core quotient, through this exact marking. -/
@[expose] noncomputable def markedCoreAction (p : ℕ) (K : Subgroup G)
    (eK : (K ⧸ pCore p K) ≃* B) : normalizer (K : Set G) →* MulAut B :=
  (MulAut.congr eK).toMonoidHom.comp ((pCore p K).quotientAut.comp K.normalizerMonoidHom)

theorem markedCoreAction_mk (p : ℕ) (K : Subgroup G)
    (eK : (K ⧸ pCore p K) ≃* B) (s : normalizer (K : Set G)) (k : K) :
    markedCoreAction p K eK s (eK (QuotientGroup.mk' (pCore p K) k)) =
      eK (QuotientGroup.mk' (pCore p K) (K.normalizerMonoidHom s k)) := by
  simp only [markedCoreAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, eK.symm_apply_apply, quotientAut_apply_mk]

/-- The actual marked action preserves the image of the Sylow intersection. -/
theorem markedCoreAction_preserves_sylow (p : ℕ) (T : Sylow p G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore p K) ≃* B)
    (P : Sylow p K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K) (s : T) :
    ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map
      (markedCoreAction p K eK ⟨s,hn s.property⟩).toMonoidHom =
      (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))
  let a := K.normalizerMonoidHom ⟨s,hn s.property⟩
  have he : (markedCoreAction p K eK ⟨s,hn s.property⟩).toMonoidHom.comp q =
      q.comp a.toMonoidHom := MonoidHom.ext (markedCoreAction_mk p K eK _)
  change ((P : Subgroup K).map q).map _ = (P : Subgroup K).map q
  rw [map_map,he,←map_map,hP,action_preserves_intersection K (T : Subgroup G) _ s.property]

/-- Invariance under the original Sylow action normalizes the actual lift. -/
theorem quotient_lift_normalized_of_marked_invariant (p : ℕ)
    (T : Sylow p G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore p K) ≃* B) (J : Subgroup B)
    (hinv : ∀ s : T, J.map (markedCoreAction p K eK ⟨s,hn s.property⟩).toMonoidHom = J) :
    (T : Subgroup G) ≤ normalizer
      ((J.comap (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map K.subtype : Set G) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))
  let Jpre := J.comap q
  intro t ht
  let a := K.normalizerMonoidHom ⟨t,hn ht⟩
  let b := markedCoreAction p K eK ⟨t,hn ht⟩
  have he (k : K) : b (q k) = q (a k) := markedCoreAction_mk p K eK _ k
  have hbJ : J.map b.toMonoidHom = J := hinv ⟨t,ht⟩
  have haJ : Jpre.map a.toMonoidHom = Jpre := by
    apply le_antisymm
    · rintro k ⟨l,hl,rfl⟩
      change q (a l) ∈ J
      rw [←he]
      exact hbJ ▸ mem_map_of_mem b.toMonoidHom hl
    · intro k hk
      refine ⟨a.symm k,?_,a.apply_symm_apply k⟩
      change q (a.symm k) ∈ J
      have hm : b (q (a.symm k)) ∈ J := by rwa [he,a.apply_symm_apply]
      have hcom : J.comap b.toMonoidHom = J := by
        have hh := congrArg (Subgroup.comap b.toMonoidHom) hbJ
        simpa only [comap_map_eq, (b.toMonoidHom.ker_eq_bot b.injective), sup_bot_eq] using hh.symm
      exact hcom ▸ hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (Jpre.map K.subtype).map (MulAut.conj t).toMonoidHom = Jpre.map K.subtype
  have hc : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro k
    exact (normalizerMonoidHom_apply_apply_coe K ⟨t,hn ht⟩ k).symm
  rw [map_map,hc,←map_map,haJ]

/-- An invariant solvable model subgroup gives a solvable overgroup of the
original Sylow, without replacing the marked quotient action. -/
theorem solvable_lift_sup_of_marked_invariant [Finite G] (p : ℕ) [Fact p.Prime]
    (T : Sylow p G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore p K) ≃* B) (J : Subgroup B) [Group.IsSolvable J]
    (hinv : ∀ s : T, J.map (markedCoreAction p K eK ⟨s,hn s.property⟩).toMonoidHom = J) :
    Group.IsSolvable ((J.comap (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map K.subtype ⊔
      (T : Subgroup G) : Subgroup G) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))
  have hker : q.ker = pCore p K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective, QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hker ▸ pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (J.comap q) := isSolvable_comap_of_solvable_ker q J
  let : Group.IsSolvable ((J.comap q).map K.subtype) :=
    Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective (J.comap q))
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  exact Group.isSolvable_sup_of_normalizes _ _
    (quotient_lift_normalized_of_marked_invariant p T K hn eK J hinv)
end Subgroup.NormalSylowQuotientAction
