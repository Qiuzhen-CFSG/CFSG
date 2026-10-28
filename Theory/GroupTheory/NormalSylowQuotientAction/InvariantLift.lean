module
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.PGroupCore
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
import all Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Lifting solvable subgroups from a normalized core quotient

Let an ambient Sylow subgroup T normalize K. A subgroup of K/Oₚ(K)
which is invariant under automorphisms preserving the image of T ∩ K
has an actual lift normalized by T. The proof retains the marked quotient
isomorphism and its induced conjugation action. If that subgroup is
solvable, its lift together with T is solvable as well, by two successive
solvable extensions.

This is the common Borel and parabolic lifting argument in
Aschbacher--Smith, 14.6.20, printed p.1037. It makes no classification
assumption about the quotient group.
-/

public section
open Subgroup
namespace Subgroup.NormalSylowQuotientAction
variable {G B : Type*} [Group G] [Finite G] [Group B]
variable {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
/-- A Sylow-invariant subgroup of a marked core quotient has a lift normalized
by the original ambient Sylow subgroup. -/
theorem quotient_lift_normalized_of_sylow_invariant
    (T : Sylow p G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore p K) ≃* B)
    (P : Sylow p K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B)
    (hinv : ∀ b : MulAut B,
      ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map b.toMonoidHom =
        (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))) →
      J.map b.toMonoidHom = J) :
    (T : Subgroup G) ≤ normalizer
      ((J.comap (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map K.subtype : Set G) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))
  let Jpre := J.comap q
  intro t ht
  let a := K.normalizerMonoidHom ⟨t,hn ht⟩
  let b := (MulAut.congr eK) ((pCore p K).quotientAut a)
  have he (k : K) : b (q k) = q (a k) := by
    dsimp only [b,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, eK.symm_apply_apply,quotientAut_apply_mk]
  have hehom : b.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext he
  have haP : (P : Subgroup K).map a.toMonoidHom = P := by
    rw [hP]
    exact action_preserves_intersection K (T : Subgroup G) _ ht
  have hbP : ((P : Subgroup K).map q).map b.toMonoidHom = (P : Subgroup K).map q := by
    rw [map_map,hehom,←map_map,haP]
  have hbJ := hinv b hbP
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

/-- Solvable subgroups invariant under Sylow-preserving automorphisms lift to
solvable overgroups of the original Sylow subgroup. -/
theorem solvable_lift_sup_of_sylow_invariant
    (T : Sylow p G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore p K) ≃* B)
    (P : Sylow p K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B) [Group.IsSolvable J]
    (hinv : ∀ b : MulAut B,
      ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map b.toMonoidHom =
        (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))) →
      J.map b.toMonoidHom = J) :
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
    (quotient_lift_normalized_of_sylow_invariant T K hn eK P hP J hinv)
end Subgroup.NormalSylowQuotientAction
