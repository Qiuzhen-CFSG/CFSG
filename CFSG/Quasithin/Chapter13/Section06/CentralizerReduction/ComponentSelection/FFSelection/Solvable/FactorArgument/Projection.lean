module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Stabilizer
public import Mathlib.Data.Fintype.Perm

/-!
# Identifying the moved cubic factor in 13.6.13

The compatible space product makes the actual supports U_i pairwise disjoint
and generating in U_H. Relative normality of H_i in H makes H preserve each
support, so different factors fix one another's supports. Consequently H_i
acts nontrivially on U_i: otherwise it would fix U_H and U_i = [U_H,H_i]
would be trivial, contradicting its order four.

An automorphism group of a four-element group embeds in S₃ by its action on
the three nonidentity elements. A two-perfect actor has even image there.
If it centralizes a nontrivial S₃-action, its image is trivial: a nonidentity
even permutation commutes with no nonidentity involution, and transpositions
generate the acting S₃. This suffices for L_v*, without needing to prove the
stronger assertion that every centralizing actor fixes U_H, or to split the
whole star group as an ambient direct product. Even the elementary-abelian
hypothesis on U_v is unnecessary for this particular implication.

The final theorem combines this action argument with the actual factor
normalizer/Sylow alternative. Its normalizer-index bounds are explicit:
the independent orbit argument must supply them in the assembly of 13.6.13.
The construction of NormalS3Decomposition and the genuine movement
hypothesis likewise remain inputs, not conclusions of this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.FactorArgument.Projection

private noncomputable def autThreeMap {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W = 4) : MulAut W →* Equiv.Perm (Fin 3) := by
  classical
  letI := Fintype.ofFinite W
  have hc : Fintype.card {w : W // w ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, hW]
  let e := Fintype.equivFinOfCardEq hc
  let f : MulAut W →* Equiv.Perm {w : W // w ≠ 1} :=
    { toFun := fun a => Equiv.Perm.subtypePerm a.toEquiv (fun w => by simp)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact e.permCongrHom.toMonoidHom.comp f

private theorem autThreeMap_injective {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W = 4) : Function.Injective (autThreeMap hW) := by
  classical
  intro a b h
  apply MulEquiv.ext
  intro w
  by_cases hw : w = 1
  · subst w; simp
  · have hh := (Equiv.permCongrHom _).injective h
    exact congrArg Subtype.val (Equiv.congr_fun hh ⟨w, hw⟩)

private theorem even_three_centralizer_involution :
    ∀ b a : Equiv.Perm (Fin 3), b ∈ alternatingGroup (Fin 3) → b ≠ 1 →
      a * b = b * a → a ^ 2 = 1 → a = 1 := by
  let : Fintype (Equiv.Perm (Fin 3)) := fintypePerm
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

private theorem commuting_actions_three {B : Type*} [Group B]
    (hp : IsPPerfect 2 B) (f : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3))
    (g : B →* Equiv.Perm (Fin 3)) (hf : f ≠ 1)
    (hc : ∀ a b, f a * g b = g b * f a) : g = 1 := by
  have hg : ∀ b, g b ∈ alternatingGroup (Fin 3) := by
    intro b
    have hh := map_pResidual_le 2 g
    rw [(pResidual_eq_top_iff 2 B).mpr hp,
      Equiv.Perm.twoResidual_eq_alternating] at hh
    exact hh (mem_map.mpr ⟨b, mem_top _, rfl⟩)
  apply MonoidHom.ext
  intro b
  change g b = 1
  by_contra hb
  apply hf
  apply MonoidHom.ext
  intro a
  change f a = 1
  induction a using Equiv.Perm.swap_induction_on with
  | one => exact map_one f
  | swap_mul a x y hxy ih =>
    have hs : f (Equiv.swap x y) = 1 :=
      even_three_centralizer_involution (g b) (f (Equiv.swap x y)) (hg b) hb
        (hc _ b) (by rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one])
    simp only [map_mul, hs, ih, one_mul]

/-- A nontrivial S₃ action on four points admits no commuting two-perfect action. -/
private theorem commuting_twoPerfect_action_eq_one {W A B : Type*}
    [Group W] [Finite W] [Group A] [Group B]
    (hW : Nat.card W = 4) (e : A ≃* Equiv.Perm (Fin 3))
    (f : A →* MulAut W) (g : B →* MulAut W) (hp : IsPPerfect 2 B)
    (hf : f ≠ 1) (hc : ∀ a b, f a * g b = g b * f a) : g = 1 := by
  let q := autThreeMap hW
  have hq := autThreeMap_injective hW
  have hn : (q.comp f).comp e.symm.toMonoidHom ≠ 1 := by
    intro he
    apply hf
    apply MonoidHom.ext
    intro a
    change f a = 1
    apply hq
    have hh := congrArg (fun F : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3) => F (e a)) he
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, MonoidHom.one_apply, map_one] using hh
  have he := commuting_actions_three hp _ (q.comp g) hn (fun a b => by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg q (hc (e.symm a) b))
  apply MonoidHom.ext
  intro b
  change g b = 1
  apply hq
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply, map_one] using
    congrArg (fun F : B →* Equiv.Perm (Fin 3) => F b) he

variable {G : Type*} [Group G] {z v : G} {X : Subgroup (Gstar z v)}

private theorem normalizes_commutator (A B C : Subgroup G)
    (hB : A ≤ normalizer (B : Set G)) (hC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer (⁅B, C⁆ : Subgroup G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hB ha),
    mem_normalizer_iff_map_conj_eq.mp (hC ha)]

private theorem preimage_normalizes (A B : Subgroup (Gstar z v))
    (h : A ≤ normalizer (B : Set _)) :
    starPreimage z v A ≤ normalizer (starPreimage z v B : Set G) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine mem_map.mpr ⟨a * b * a⁻¹, ?_, rfl⟩
  change starMk z v (a * b * a⁻¹) ∈ B
  simpa only [map_mul, map_inv] using
    (mem_normalizer_iff.mp (h ha) (starMk z v b)).mp hb

private theorem moved_normalized (d : NormalS3Decomposition z v X) :
    Gv v ≤ normalizer (movedSubgroup z v d.H : Set G) := by
  let := d.normal
  exact normalizes_commutator _ _ _ (Gv_normalizes_Uv z v)
    (starPreimage_normalized z v d.H)

private theorem support_le (d : NormalS3Decomposition z v X) (i : Fin d.count) :
    factorSupport z v d.H (d.factor i) ≤ movedSubgroup z v d.H :=
  le_normalizer_iff_commutator_le_left.mp
    ((starPreimage_le_Gv z v _).trans (moved_normalized d))

private theorem support_normalized (d : NormalS3Decomposition z v X)
    (A : Subgroup (Gstar z v)) (i : Fin d.count)
    (h : A ≤ normalizer (d.factor i : Set _)) :
    starPreimage z v A ≤ normalizer (factorSupport z v d.H (d.factor i) : Set G) :=
  normalizes_commutator _ _ _
    ((starPreimage_le_Gv z v A).trans (moved_normalized d))
    (preimage_normalizes A (d.factor i) h)

private noncomputable def supportProductMap (d : NormalS3Decomposition z v X) :
    (∀ i, factorSupport z v d.H (d.factor i)) →* G :=
  (movedSubgroup z v d.H).subtype.comp d.space.toMonoidHom

private theorem supportProductMap_single (d : NormalS3Decomposition z v X)
    (i : Fin d.count) (a : factorSupport z v d.H (d.factor i)) :
    supportProductMap d (Pi.mulSingle i a) = (a : G) := d.space_single i a

private theorem supportProductMap_injective (d : NormalS3Decomposition z v X) :
    Function.Injective (supportProductMap d) :=
  (movedSubgroup z v d.H).subtype_injective.comp d.space.injective

/-- The actual supports generate the moved subgroup, through the specified product map. -/
theorem iSup_support (d : NormalS3Decomposition z v X) :
    (⨆ i, factorSupport z v d.H (d.factor i)) = movedSubgroup z v d.H := by
  apply le_antisymm (iSup_le (support_le d))
  intro a ha
  let x := d.space.symm ⟨a, ha⟩
  have hc : Pairwise fun i j =>
      ∀ (a : factorSupport z v d.H (d.factor i)) (b : factorSupport z v d.H (d.factor j)),
        Commute ((factorSupport z v d.H (d.factor i)).subtype a)
          ((factorSupport z v d.H (d.factor j)).subtype b) := by
    intro i j hij a b
    simpa only [supportProductMap_single, Subgroup.subtype_apply] using
      (Pi.mulSingle_commute hij a b).map (supportProductMap d)
  let f := MonoidHom.noncommPiCoprod
    (fun i => (factorSupport z v d.H (d.factor i)).subtype) hc
  have hf : f = supportProductMap d := by
    apply MonoidHom.pi_ext
    intro i a
    change f (Pi.mulSingle i a) = supportProductMap d (Pi.mulSingle i a)
    rw [supportProductMap_single]
    simpa only [Subgroup.subtype_apply] using
      MonoidHom.noncommPiCoprod_mulSingle
        (fun j => (factorSupport z v d.H (d.factor j)).subtype) (hcomm := hc) i a
  have hr : f.range = ⨆ i, factorSupport z v d.H (d.factor i) := by
    change (MonoidHom.noncommPiCoprod
      (fun i => (factorSupport z v d.H (d.factor i)).subtype) hc).range = _
    rw [MonoidHom.noncommPiCoprod_range]
    simp only [Subgroup.range_subtype]
  rw [← hr]
  refine ⟨x, ?_⟩
  rw [hf]
  exact congrArg Subtype.val (d.space.apply_symm_apply ⟨a, ha⟩)

private theorem support_disjoint (d : NormalS3Decomposition z v X)
    {i j : Fin d.count} (hij : i ≠ j) :
    Disjoint (factorSupport z v d.H (d.factor i)) (factorSupport z v d.H (d.factor j)) := by
  rw [Subgroup.disjoint_def]
  intro a hai haj
  have he : Pi.mulSingle i (⟨a, hai⟩ : factorSupport z v d.H (d.factor i)) =
      Pi.mulSingle j (⟨a, haj⟩ : factorSupport z v d.H (d.factor j)) :=
    supportProductMap_injective d
      ((supportProductMap_single d i ⟨a, hai⟩).trans
        (supportProductMap_single d j ⟨a, haj⟩).symm)
  have hi := congrFun he i
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at hi
  exact congrArg Subtype.val hi

/-- Different factors fix each other's supports pointwise. -/
theorem cross_support_commutator (d : NormalS3Decomposition z v X)
    {i j : Fin d.count} (hij : i ≠ j) :
    ⁅factorSupport z v d.H (d.factor i), starPreimage z v (d.factor j)⁆ = ⊥ := by
  apply le_bot_iff.mp
  apply (le_inf ?_ ?_).trans (support_disjoint d hij).le_bot
  · apply le_normalizer_iff_commutator_le_left.mp
    apply support_normalized d _ i
    exact (d.factor_le j).trans
      ((normal_subgroupOf_iff_le_normalizer (d.factor_le i)).mp (d.factor_normal_in_H i))
  · exact commutator_mono (support_le d i) le_rfl

private theorem star_preserves (W : Subgroup G) (hW : W ≤ Uv z v)
    (A : Subgroup (Gstar z v)) (hn : starPreimage z v A ≤ normalizer (W : Set G))
    (a : A) (w : W) :
    (starAction z v a ⟨w, hW w.property⟩ : G) ∈ W := by
  obtain ⟨x, hx⟩ := starMk_surjective z v a
  have hxm : (x : G) ∈ starPreimage z v A :=
    mem_map.mpr ⟨x, (show starMk z v x ∈ A from hx ▸ a.property), rfl⟩
  rw [← hx, starAction_mk_apply]
  exact (mem_normalizer_iff.mp (hn hxm) w).mp w.property

private noncomputable def restrictedStarAction (W : Subgroup G) (hW : W ≤ Uv z v)
    (A : Subgroup (Gstar z v)) (hn : starPreimage z v A ≤ normalizer (W : Set G)) :
    A →* MulAut W where
  toFun a :=
    { toFun := fun w => ⟨starAction z v a ⟨w, hW w.property⟩, star_preserves W hW A hn a w⟩
      invFun := fun w => ⟨starAction z v a⁻¹ ⟨w, hW w.property⟩,
        star_preserves W hW A hn a⁻¹ w⟩
      left_inv := by
        intro w
        apply Subtype.ext
        change ((starAction z v (a : Gstar z v)⁻¹)
          (starAction z v a ⟨w, hW w.property⟩) : G) = w
        simp only [map_inv, MulAut.inv_apply_self]
      right_inv := by
        intro w
        apply Subtype.ext
        change ((starAction z v a)
          (starAction z v (a : Gstar z v)⁻¹ ⟨w, hW w.property⟩) : G) = w
        simp only [map_inv, MulAut.apply_inv_self]
      map_mul' := by
        intro w u
        apply Subtype.ext
        change (starAction z v a (⟨w, hW w.property⟩ * ⟨u, hW u.property⟩) : G) =
          (starAction z v a ⟨w, hW w.property⟩ : G) *
            (starAction z v a ⟨u, hW u.property⟩ : G)
        exact congrArg (fun y : Uv z v => (y : G)) ((starAction z v a).map_mul
          ⟨w, hW w.property⟩ ⟨u, hW u.property⟩) }
  map_one' := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (starAction z v 1 ⟨w, hW w.property⟩ : G) = w
    simp
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (starAction z v ((a : Gstar z v) * b) ⟨w, hW w.property⟩ : G) =
      ((starAction z v a) (starAction z v b ⟨w, hW w.property⟩) : G)
    rw [map_mul]; rfl

private theorem restrictedStarAction_mk (W : Subgroup G) (hW : W ≤ Uv z v)
    (A : Subgroup (Gstar z v)) (hn : starPreimage z v A ≤ normalizer (W : Set G))
    (x : Gv v) (hx : starMk z v x ∈ A) (w : W) :
    (restrictedStarAction W hW A hn ⟨starMk z v x, hx⟩ w : G) =
      (x : G) * w * (x : G)⁻¹ := starAction_mk_apply z v x _

private theorem restrictedStarAction_eq_one_iff (W : Subgroup G) (hW : W ≤ Uv z v)
    (A : Subgroup (Gstar z v)) (hn : starPreimage z v A ≤ normalizer (W : Set G)) :
    restrictedStarAction W hW A hn = 1 ↔ starPreimage z v A ≤ centralizer (W : Set G) := by
  constructor
  · intro he
    rintro _ ⟨x, hx, rfl⟩ w hw
    have hh := congrArg (fun f : A →* MulAut W =>
      (f ⟨starMk z v x, hx⟩ ⟨w, hw⟩ : G)) he
    change (x : G) * w * (x : G)⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hc
    apply MonoidHom.ext
    intro a
    obtain ⟨x, hx⟩ := starMk_surjective z v a
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    have hm : (x : G) ∈ starPreimage z v A :=
      mem_map.mpr ⟨x, (show starMk z v x ∈ A from hx ▸ a.property), rfl⟩
    have he : a = ⟨starMk z v x, hx ▸ a.property⟩ := Subtype.ext hx.symm
    rw [he, restrictedStarAction_mk]
    change (x : G) * (w : G) * (x : G)⁻¹ = w
    rw [← hc hm w w.property]
    simp [mul_assoc]

private theorem restrictedStarAction_commute (W : Subgroup G) (hW : W ≤ Uv z v)
    (A B : Subgroup (Gstar z v))
    (hA : starPreimage z v A ≤ normalizer (W : Set G))
    (hB : starPreimage z v B ≤ normalizer (W : Set G))
    (hc : B ≤ centralizer (A : Set _)) (a : A) (b : B) :
    restrictedStarAction W hW A hA a * restrictedStarAction W hW B hB b =
      restrictedStarAction W hW B hB b * restrictedStarAction W hW A hA a := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  have he := congrArg (fun f : MulAut (Uv z v) => (f ⟨w, hW w.property⟩ : G))
    (congrArg (starAction z v) (hc b.property a a.property))
  change (starAction z v a (starAction z v b ⟨w, hW w.property⟩) : G) =
    (starAction z v b (starAction z v a ⟨w, hW w.property⟩) : G)
  simpa only [map_mul, MulAut.mul_apply] using he

private theorem support_action_nontrivial [Finite G]
    (d : NormalS3Decomposition z v X) (i : Fin d.count) :
    restrictedStarAction (factorSupport z v d.H (d.factor i))
      ((support_le d i).trans (movedSubgroup_le_Uv z v d.H))
      (d.factor i) (support_normalized d _ i (d.factor i).le_normalizer) ≠ 1 := by
  intro he
  have hc := (restrictedStarAction_eq_one_iff _ _ _ _).mp he
  have hall : movedSubgroup z v d.H ≤ centralizer (starPreimage z v (d.factor i) : Set G) := by
    rw [← iSup_support d]
    apply iSup_le
    intro j
    by_cases hj : j = i
    · subst j
      exact le_centralizer_iff.mp hc
    · exact commutator_eq_bot_iff_le_centralizer.mp (cross_support_commutator d hj)
  have hb : factorSupport z v d.H (d.factor i) = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hall
  have hh := d.support_card i
  rw [hb, Subgroup.card_bot] at hh
  norm_num at hh

/-- A two-perfect actor centralizing every S₃ factor fixes the entire actual moved subgroup.
The proof uses each nontrivial action on its four-element support and the compatible space product. -/
theorem centralizes_moved_of_centralizes_factors [Finite G]
    (d : NormalS3Decomposition z v X) (B : Subgroup (Gstar z v))
    (hp : IsPPerfect 2 B) (hc : ∀ i, B ≤ centralizer (d.factor i : Set _)) :
    starPreimage z v B ≤ centralizer (movedSubgroup z v d.H : Set G) := by
  apply le_centralizer_iff.mpr
  rw [← iSup_support d]
  apply iSup_le
  intro i
  let W := factorSupport z v d.H (d.factor i)
  have hW : W ≤ Uv z v := (support_le d i).trans (movedSubgroup_le_Uv z v d.H)
  have hnA := support_normalized d (d.factor i) i (d.factor i).le_normalizer
  have hnB := support_normalized d B i ((hc i).trans (Subgroup.centralizer_le_normalizer _))
  have hfix := commuting_twoPerfect_action_eq_one (d.support_card i) (d.model i)
    (restrictedStarAction W hW (d.factor i) hnA) (restrictedStarAction W hW B hnB)
    hp (support_action_nontrivial d i)
    (restrictedStarAction_commute W hW (d.factor i) B hnA hnB (hc i))
  exact le_centralizer_iff.mp ((restrictedStarAction_eq_one_iff W hW B hnB).mp hfix)

/-- The conditional projection-identification step in 13.6.13. Normalizer-index bounds
are the independent orbit input; genuine movement excludes simultaneous centralization. -/
theorem exists_factorResidual_of_movement [Finite G]
    (L T : Subgroup G) (z v : G)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    {X : Subgroup (Gstar z v)} (d : NormalS3Decomposition z v X)
    (hmove : ⁅movedSubgroup z v d.H, Lv L v⁆ ≠ ⊥)
    (hindex : ∀ i, (normalizer (d.factor i : Set (Gstar z v))).index ≤ 2) :
    ∃ i, starImage z v (Lv L v) = d.factorResidual i := by
  by_contra hn
  have hc : ∀ i, starImage z v (Lv L v) ≤ centralizer (d.factor i : Set _) := by
    intro i
    exact (factor_alternative_of_small_normalizer_index L T z v S hS hL hcard d i
      (hindex i)).resolve_left (fun he => hn ⟨i, he⟩)
  have hall := centralizes_moved_of_centralizes_factors d
    (starImage z v (Lv L v)) (starLv_twoPerfect L z v) hc
  have hpre : Lv L v ≤ starPreimage z v (starImage z v (Lv L v)) := by
    intro a ha
    let a' : Gv v := ⟨a, Lv_le_Gv L v ha⟩
    exact mem_map.mpr ⟨a', mem_map.mpr ⟨a', ha, rfl⟩, rfl⟩
  apply hmove
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hpre.trans hall))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.FactorArgument.Projection
end
