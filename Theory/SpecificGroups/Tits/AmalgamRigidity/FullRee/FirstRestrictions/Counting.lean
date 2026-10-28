module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.FirstRestrictions.Generators
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.FirstRestrictions.Conjugacy
public import Theory.GroupTheory.Amalgam.RestrictionProduct

/-!
# Counting the actual first-endpoint restrictions

The inner automorphisms have order at least 2048 because the Sylow group has
order 4096 and its center has at most two elements. The first extra generator
fixes the core and moves root one, so it is not inner. Adjoining it still gives
only inner actions on the core; the second generator is excluded from that
subgroup by the conjugacy obstruction on core roots zero and two. The third
generator changes the binary core character, which the preceding subgroup fixes.
Each proper enlargement at least doubles the order, yielding 16384 restrictions.

All three generators have the actual compatible endpoint automorphisms built
in `Generators`. Thus this is a count in the restriction subgroup of the
literal embedding, rather than a count of abstract endpoint automorphisms.
Source context: Shinoda (1975), pp.81–83; Parrott (1972), p.683;
Aschbacher–Smith F.1.11–12, printed pp.262–263.
-/

@[expose] public section
open ReeTwo
namespace Tits.AmalgamRigidity.FullRee.FirstRestrictions
open Theory.GroupTheory.RankTwoAmalgam

noncomputable def inner : Subgroup (MulAut SylowModel) := MulAut.conj.range

instance inner_normal : inner.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ a
  refine ⟨a x, ?_⟩
  apply MulEquiv.ext
  intro y
  simp [MulAut.mul_apply, MulAut.conj_apply]

noncomputable def firstStage : Subgroup (MulAut SylowModel) := inner ⊔ Subgroup.zpowers (generator 0)
noncomputable def secondStage : Subgroup (MulAut SylowModel) := firstStage ⊔ Subgroup.zpowers (generator 1)

def coreFixer : Subgroup (MulAut SylowModel) where
  carrier := {f | ∀ i, f (SylowModel.root i) = SylowModel.root i}
  one_mem' _ := rfl
  mul_mem' hf hg i := by simp only [MulAut.mul_apply, hg i, hf i]
  inv_mem' {f} hf i := by
    apply f.injective
    simpa only [MulAut.apply_inv_self] using (hf i).symm

theorem generator_zero_fixes : generator 0 ∈ coreFixer := by
  intro i
  rw [generator_root]
  exact (by decide +kernel : ∀ i : CoreRoot, rootImage 0 i = SylowModel.root i) i

theorem generator_zero_not_inner : generator 0 ∉ inner := by
  rintro ⟨g, hg⟩
  have hc : g ∈ Subgroup.center SylowModel := by
    apply central_of_fixes_core
    intro i
    have he : MulAut.conj g (SylowModel.root i) = SylowModel.root i := by
      rw [hg]
      exact generator_zero_fixes i
    exact mul_inv_eq_iff_eq_mul.mp he
  have he := congrArg (fun f : MulAut SylowModel => f SylowModel.rootOne) hg
  have hg1 : MulAut.conj g SylowModel.rootOne = SylowModel.rootOne := by
    exact (show Commute g SylowModel.rootOne from
      (Subgroup.mem_center_iff.mp hc SylowModel.rootOne).symm).mul_inv_cancel
  rw [hg1, generator_rootOne] at he
  exact (by decide +kernel : rootOneImage 0 ≠ SylowModel.rootOne) he.symm

theorem generator_one_not_firstStage : generator 1 ∉ firstStage := by
  intro h
  obtain ⟨a, ⟨g, rfl⟩, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp h
  have hb' : b ∈ coreFixer := (Subgroup.zpowers_le.mpr generator_zero_fixes) hb
  have hi (i : CoreRoot) : MulAut.conj g (SylowModel.root i) = rootImage 1 i := by
    have he := congrArg (fun f : MulAut SylowModel => f (SylowModel.root i)) hab
    simpa only [MulAut.mul_apply, hb' i, generator_root] using he
  have h0 : g * SylowModel.root 0 = SylowModel.root 0 * g := by
    apply mul_inv_eq_iff_eq_mul.mp
    change MulAut.conj g (SylowModel.root 0) = SylowModel.root 0
    rw [hi]
    decide +kernel
  have h2 : g * SylowModel.root 2 = (SylowModel.root 2 * SylowModel.root 9) * g := by
    apply mul_inv_eq_iff_eq_mul.mp
    change MulAut.conj g (SylowModel.root 2) = SylowModel.root 2 * SylowModel.root 9
    rw [hi]
    decide +kernel
  exact rootTwo_twist_impossible g h0 h2

def characterFixer : Subgroup (MulAut SylowModel) where
  carrier := {f | ∀ g, SylowModel.coreCharacter (f g) = SylowModel.coreCharacter g}
  one_mem' _ := rfl
  mul_mem' hf hg x := (hf _).trans (hg x)
  inv_mem' {f} hf x := by
    simpa only [MulAut.apply_inv_self] using (hf (f⁻¹ x)).symm

theorem inner_le_characterFixer : inner ≤ characterFixer := by
  rintro _ ⟨g, rfl⟩ x
  simp [MulAut.conj_apply, mul_assoc]

private theorem sylow_hom_ext {H : Type*} [Group H] {f g : SylowModel →* H}
    (hx : ∀ i, f (SylowModel.root i) = g (SylowModel.root i))
    (hs : f SylowModel.rootOne = g SylowModel.rootOne) : f = g := by
  apply MonoidHom.ext
  intro x
  rw [← normal_form x]
  simp only [Core.normalWord, map_mul, map_pow, map_inv, hx, hs]

theorem generator_character (k : Fin 3) (hk : k.val < 2) :
    generator k ∈ characterFixer := by
  have he : SylowModel.coreCharacter.comp (generator k).toMonoidHom =
      SylowModel.coreCharacter := by
    apply sylow_hom_ext
    · intro i
      change SylowModel.coreCharacter (generator k (SylowModel.root i)) = _
      rw [generator_root]
      exact (by decide +kernel : ∀ (k : Fin 3), k.val < 2 → ∀ i : CoreRoot,
        SylowModel.coreCharacter (rootImage k i) = SylowModel.coreCharacter (SylowModel.root i)) k hk i
    · change SylowModel.coreCharacter (generator k SylowModel.rootOne) = _
      rw [generator_rootOne]
      exact (by decide +kernel : ∀ (k : Fin 3), k.val < 2 →
        SylowModel.coreCharacter (rootOneImage k) = SylowModel.coreCharacter SylowModel.rootOne) k hk
  exact fun x => DFunLike.congr_fun he x

theorem secondStage_le_characterFixer : secondStage ≤ characterFixer :=
  sup_le (sup_le inner_le_characterFixer (Subgroup.zpowers_le.mpr (generator_character 0 (by decide))))
    (Subgroup.zpowers_le.mpr (generator_character 1 (by decide)))

theorem generator_two_not_secondStage : generator 2 ∉ secondStage := by
  intro h
  have he := secondStage_le_characterFixer h SylowModel.rootOne
  rw [generator_rootOne] at he
  exact (by decide +kernel : SylowModel.coreCharacter (rootOneImage 2) ≠
    SylowModel.coreCharacter SylowModel.rootOne) he

theorem inner_card_ge : 2048 ≤ Nat.card inner := by
  let K := (MulAut.conj : SylowModel →* MulAut SylowModel).ker
  have hc (x : K) : (x : SylowModel) ∈ Subgroup.center SylowModel := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have he := DFunLike.congr_fun x.property y
    change (x : SylowModel) * y * (x : SylowModel)⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hk : Nat.card K ≤ 2 := by
    let f : K → Bool := fun x => decide ((x : SylowModel) = 1)
    have hf : Function.Injective f := by
      intro x y h
      have hh : ((x : SylowModel) = 1) ↔ ((y : SylowModel) = 1) := by
        simpa only [f, decide_eq_decide] using h
      apply Subtype.ext
      rcases SylowModel.eq_one_or_root_twelve_of_mem_center x (hc x) with hx | hx
      · exact hx.trans (hh.mp hx).symm
      · have hy : (y : SylowModel) = SylowModel.root 9 :=
          (SylowModel.eq_one_or_root_twelve_of_mem_center y (hc y)).resolve_left (by
            intro hy
            exact (by decide +kernel : SylowModel.root 9 ≠ 1) (hx.symm.trans (hh.mpr hy)))
        exact hx.trans hy.symm
    simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf
  have he := K.card_mul_index
  rw [Subgroup.index_ker, SylowModel.card] at he
  change Nat.card K * Nat.card inner = 4096 at he
  have hm := Nat.mul_le_mul_right (Nat.card inner) hk
  nlinarith

theorem generator_mem (k : Fin 3) : generator k ∈ extensionSubgroup SylowModel.embedding :=
  ⟨endpointAutomorphism k, generator_compatible k⟩

theorem inner_le_restrictions : inner ≤ extensionSubgroup SylowModel.embedding := by
  rintro _ ⟨g, rfl⟩
  exact ⟨MulAut.conj (SylowModel.embedding g), fun x => by simp [MulAut.conj_apply]⟩

private theorem twice_card_le {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hHK : H ≤ K) (g : G) (hg : g ∈ K) (hn : g ∉ H) :
    2 * Nat.card H ≤ Nat.card K := by
  have hne : Nat.card K ≠ Nat.card H := by
    intro he
    have hEq : H = K := Subgroup.eq_of_le_of_card_ge hHK (by omega)
    exact hn (hEq.symm ▸ hg)
  obtain ⟨n, he⟩ := Subgroup.card_dvd_of_le hHK
  have hp : 0 < Nat.card K := Nat.card_pos
  have hn : 2 ≤ n := by
    by_contra hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp_all
  nlinarith

/-- At least 16384 distinct overlap automorphisms extend to the actual first endpoint. -/
theorem restriction_card_ge : 16384 ≤ Nat.card (extensionSubgroup SylowModel.embedding) := by
  have hi := inner_card_ge
  have h1 : 4096 ≤ Nat.card firstStage := by
    have he := twice_card_le inner firstStage le_sup_left (generator 0)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) generator_zero_not_inner
    omega
  have h2 : 8192 ≤ Nat.card secondStage := by
    have he := twice_card_le firstStage secondStage le_sup_left (generator 1)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) generator_one_not_firstStage
    omega
  have hle : secondStage ≤ extensionSubgroup SylowModel.embedding :=
    sup_le (sup_le inner_le_restrictions (Subgroup.zpowers_le.mpr (generator_mem 0)))
      (Subgroup.zpowers_le.mpr (generator_mem 1))
  have he := twice_card_le secondStage (extensionSubgroup SylowModel.embedding) hle
    (generator 2) (generator_mem 2) generator_two_not_secondStage
  omega

end Tits.AmalgamRigidity.FullRee.FirstRestrictions
