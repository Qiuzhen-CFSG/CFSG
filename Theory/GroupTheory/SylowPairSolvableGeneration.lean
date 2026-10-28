module
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Odd solvable supplements and two maximal Sylow overgroups

Let K be a simple normal subgroup, R a proper nonsolvable subgroup of K
normalized by a Sylow two-subgroup S, and D an odd subgroup with SD solvable.
If solvable Sylow overgroups of K normalize their Sylow, and K has two
maximal overgroups of that Sylow with solvable intersection, then R,S,D
cannot generate the ambient group. The odd group fixes both maximal
overgroups; S fixes the unique one containing R. Generation would make
this proper nontrivial subgroup normal in K.

This is the rank-two exclusion in Aschbacher--Smith 5.1.13 and 5.2.2,
printed pp.636 and 648. The intrinsic Sylow geometry is explicit here;
the symplectic consumer supplies it from the actual matrix parabolics.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An odd subgroup cannot move a member of an invariant pair of subgroups. -/
theorem odd_preserves_pair {A : Type*} [Group A] [Finite A]
    (a : A →* MulAut G) {R P Q : Subgroup G}
    (ho : Odd (Nat.card A)) (hR : R = P ∨ R = Q)
    (hi : ∀ d : A, ∀ Y : Subgroup G, Y = P ∨ Y = Q →
      Y.map (a d).toMonoidHom = P ∨ Y.map (a d).toMonoidHom = Q) :
    ∀ d : A, R.map (a d).toMonoidHom = R := by
  classical
  let : MulAction A (Subgroup G) :=
    MulAction.compHom (Subgroup G) a
  have hsub : MulAction.orbit A R ⊆ ({P,Q} : Set (Subgroup G)) := by
    rintro Y ⟨d,rfl⟩
    change R.map (a d).toMonoidHom = P ∨ R.map (a d).toMonoidHom = Q
    exact hi d R hR
  have hb : (MulAction.stabilizer A R).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard hsub).trans (by simpa using (Set.ncard_insert_le P ({Q} : Set (Subgroup G))))
  have hod : Odd (MulAction.stabilizer A R).index :=
    ho.of_dvd_nat (MulAction.stabilizer A R).index_dvd_card
  have hp := (MulAction.stabilizer A R).index_ne_zero_of_finite
  have hn := hod.not_two_dvd_nat
  have he : (MulAction.stabilizer A R).index = 1 := by omega
  have ht := Subgroup.index_eq_one.mp he
  intro d
  exact show d ∈ MulAction.stabilizer A R from ht ▸ mem_top _


omit [Finite G] in
private theorem action_preserves {K R : Subgroup G} (hRK : R ≤ K)
    {x : G} (hK : x ∈ normalizer (K : Set G))
    (hR : x ∈ normalizer (R : Set G)) :
    (R.subgroupOf K).map (K.normalizerMonoidHom ⟨x,hK⟩).toMonoidHom = R.subgroupOf K := by
  apply (map_injective K.subtype_injective)
  have he : K.subtype.comp (K.normalizerMonoidHom ⟨x,hK⟩).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp K.subtype := by
    ext y
    exact normalizerMonoidHom_apply_apply_coe K ⟨x,hK⟩ y
  rw [map_map, he, ←map_map, map_subgroupOf_eq_of_le hRK]
  exact mem_normalizer_iff_map_conj_eq.mp hR

/-- A simple normal component with two maximal Sylow overgroups cannot be
generated from a proper invariant nonsolvable subgroup and a solvable odd extension. -/
theorem no_solvable_odd_supplement_of_two_sylow_overgroups
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤)
    (hcontrol : SolvableSylowControl 2 K)
    (hgeometry : ∀ U : Sylow 2 K, ∃ P Q : Subgroup K,
      IsCoatom P ∧ IsCoatom Q ∧ (U : Subgroup K) ≤ P ∧ (U : Subgroup K) ≤ Q ∧ Group.IsSolvable (P ⊓ Q : Subgroup K) ∧
      ∀ J : Subgroup K, (U : Subgroup K) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q) : False := by
  let A := (S : Subgroup G) ⊔ D
  let : Group.IsSolvable A := hsol
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal K
  have hSU : (U : Subgroup K).map K.subtype ≤ (S : Subgroup G) := by
    rw [hU, subgroupOf_map_subtype]
    exact inf_le_left
  have hAN := hcontrol.normalizes_sylow K A U le_normalizer_of_normal
    (hSU.trans le_sup_left)
  let R' := R.subgroupOf K
  have hRns' : ¬ Group.IsSolvable R' := by
    intro hs
    let := hs
    exact hRns (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hRK.le).toMonoidHom) (subgroupOfEquivOfLe hRK.le).surjective)
  have hRne : R' ≠ ⊥ := by
    intro he
    apply hRns'
    rw [he]
    infer_instance
  have hRproper : R' ≠ ⊤ := fun he => hRK.not_ge (subgroupOf_eq_top.mp he)
  have hUR : (U : Subgroup K) ≤ normalizer (R' : Set K) := by
    rw [←subgroupOf_normalizer_eq hRK.le, hU]
    exact comap_mono hSR
  have hproper : R' ⊔ (U : Subgroup K) ≠ ⊤ := by
    intro he
    have hn : R'.Normal := normalizer_eq_top_iff.mp (by
      apply top_unique
      rw [←he]
      exact sup_le R'.le_normalizer hUR)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R' hn with hb | ht
    · exact hRne hb
    · exact hRproper ht
  obtain ⟨P,Q,hP,hQ,hUP,hUQ,hsolPQ,hcover⟩ := hgeometry U
  have perm (a : MulAut K) (ha : (U : Subgroup K).map a.toMonoidHom = U)
      (J : Subgroup K) (hJ : J = P ∨ J = Q) :
      J.map a.toMonoidHom = P ∨ J.map a.toMonoidHom = Q := by
    have hc : IsCoatom J := hJ.elim (fun he => he ▸ hP) (fun he => he ▸ hQ)
    have hUJ : (U : Subgroup K) ≤ J := hJ.elim (fun he => he ▸ hUP) (fun he => he ▸ hUQ)
    have hm : IsCoatom (J.map a.toMonoidHom) := (a.mapSubgroup.isCoatom_iff J).mpr hc
    rcases hcover _ (ha ▸ map_mono hUJ) hm.ne_top with hp | hq
    · exact Or.inl ((hm.le_iff_eq hP.ne_top).mp hp).symm
    · exact Or.inr ((hm.le_iff_eq hQ.ne_top).mp hq).symm
  obtain ⟨J,hJ,hRJ⟩ : ∃ J : Subgroup K, (J = P ∨ J = Q) ∧ R' ≤ J := by
    rcases hcover _ (show (U : Subgroup K) ≤ R' ⊔ U from le_sup_right) hproper with hp | hq
    · exact ⟨P,Or.inl rfl,le_sup_left.trans hp⟩
    · exact ⟨Q,Or.inr rfl,le_sup_left.trans hq⟩
  have unique (Y Z : Subgroup K) (hY : Y = P ∨ Y = Q) (hZ : Z = P ∨ Z = Q)
      (hRY : R' ≤ Y) (hRZ : R' ≤ Z) : Y = Z := by
    have bad : ¬ R' ≤ P ⊓ Q := by
      intro hh
      let := hsolPQ
      exact hRns' (Group.isSolvable_of_isSolvable_injective (inclusion_injective hh))
    rcases hY with rfl | rfl <;> rcases hZ with rfl | rfl
    · rfl
    · exact (bad (le_inf hRY hRZ)).elim
    · exact (bad (le_inf hRZ hRY)).elim
    · rfl
  have actU (x : G) (hx : x ∈ A) :
      (U : Subgroup K).map (K.normalizerMonoidHom ⟨x, le_normalizer_of_normal (mem_top x)⟩).toMonoidHom = U := by
    have hh := action_preserves (map_subtype_le (U : Subgroup K))
      (le_normalizer_of_normal (mem_top x)) (hAN hx)
    simpa only [subgroupOf, comap_map_eq_self_of_injective K.subtype_injective] using hh
  have lift_fixed (x : G)
      (hx : J.map (K.normalizerMonoidHom ⟨x,le_normalizer_of_normal (mem_top x)⟩).toMonoidHom = J) :
      x ∈ normalizer (J.map K.subtype : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (J.map K.subtype).map (MulAut.conj x).toMonoidHom = J.map K.subtype
    have he : (MulAut.conj x).toMonoidHom.comp K.subtype =
        K.subtype.comp (K.normalizerMonoidHom ⟨x,le_normalizer_of_normal (mem_top x)⟩).toMonoidHom := by
      ext y
      exact (normalizerMonoidHom_apply_apply_coe K ⟨x,le_normalizer_of_normal (mem_top x)⟩ y).symm
    rw [map_map,he,←map_map,hx]
  have hSfix : (S : Subgroup G) ≤ normalizer (J.map K.subtype : Set G) := by
    intro x hx
    apply lift_fixed
    let a := K.normalizerMonoidHom ⟨x,le_normalizer_of_normal (mem_top x)⟩
    have hRfix : R'.map a.toMonoidHom = R' := action_preserves hRK.le
      (le_normalizer_of_normal (mem_top x)) (hSR hx)
    exact unique _ J (perm a (actU x (mem_sup_left hx)) J hJ) hJ
      (hRfix ▸ map_mono hRJ) hRJ
  have hDfix : D ≤ normalizer (J.map K.subtype : Set G) := by
    let a : D →* MulAut K := K.normalizerMonoidHom.comp (inclusion (show D ≤ normalizer (K : Set G) from le_normalizer_of_normal))
    have hh := odd_preserves_pair a ho hJ (fun d Y hY =>
      perm (a d) (actU d (mem_sup_right d.property)) Y hY)
    intro d hd
    exact lift_fixed d (hh ⟨d,hd⟩)
  have hRJ' : R ≤ J.map K.subtype := by
    simpa only [R', map_subgroupOf_eq_of_le hRK.le] using map_mono (f := K.subtype) hRJ
  have hN : (⊤ : Subgroup G) ≤ normalizer (J.map K.subtype : Set G) := by
    rw [←hgen]
    exact sup_le (sup_le (hRJ'.trans (J.map K.subtype).le_normalizer) hSfix) hDfix
  have hJn : J.Normal := by
    have hh := (normal_subgroupOf_iff_le_normalizer (map_subtype_le J)).mpr (le_top.trans hN)
    simpa only [subgroupOf, comap_map_eq_self_of_injective K.subtype_injective] using hh
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J hJn with hb | ht
  · exact hRne (bot_unique (hb ▸ hRJ))
  · exact (hJ.elim (fun he => hP.ne_top (he ▸ ht)) (fun he => hQ.ne_top (he ▸ ht)))
end Theory.GroupTheory
