module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.NormNum

/-!
# A dihedral factor detected by a commuting alternating four-group

In `D₁₀ × A₅`, any embedded A₄ has trivial first projection and its second
projection is self-centralizing in A₅. A commuting embedded D₁₀ must therefore
be the whole first factor. Its centralizer is the second factor.

The A₄ centralizer calculation uses its prime index five and the simplicity
of A₅. Triviality of the first projection uses generation by three-cycles.
No enumeration of homomorphisms or recognition by group order is needed.

This is the direct-product step in Aschbacher, *Sporadic Groups* (1994),
47.10, printed p.266, applied to the five-local normalizer from 47.2.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.Alternating.DihedralFiveCentralizer

local notation "A4" => alternatingGroup (Fin 4)
local notation "A5" => alternatingGroup (Fin 5)
local notation "D10" => DihedralGroup 5

private theorem four_centralizer (H : Subgroup (alternatingGroup (Fin 5)))
    (e : H ≃* alternatingGroup (Fin 4)) : centralizer (H : Set (alternatingGroup (Fin 5))) = ⊥ := by
  have hc : Nat.card H = 12 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hg : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi : H.index = 5 := by
    have h := H.card_mul_index
    rw [hc, hg] at h
    omega
  have hn : normalizer (H : Set (alternatingGroup (Fin 5))) = H := by
    have hm := H.relIndex_mul_index H.le_normalizer
    rw [hi] at hm
    have hd : (normalizer (H : Set (alternatingGroup (Fin 5)))).index ∣ 5 := ⟨H.relIndex (normalizer (H : Set (alternatingGroup (Fin 5)))), by simpa only [Nat.mul_comm] using hm.symm⟩
    rcases (show Nat.Prime 5 by decide).eq_one_or_self_of_dvd _ hd with h | h
    · have htop := Subgroup.index_eq_one.mp h
      have hn := normalizer_eq_top_iff.mp htop
      rcases hn.eq_bot_or_eq_top with hh | hh
      · rw [hh, card_bot] at hc
        omega
      · rw [hh, card_top, hg] at hc
        omega
    · have hrel : H.relIndex (normalizer (H : Set (alternatingGroup (Fin 5)))) = 1 := by rw [h] at hm; omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) H.le_normalizer
  apply eq_bot_iff.mpr
  intro x hx
  have hxH : x ∈ H := hn ▸ centralizer_le_normalizer _ hx
  have hxZ : (⟨x, hxH⟩ : H) ∈ center H := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.mp hx) y y.property)
  have heZ : e ⟨x, hxH⟩ ∈ center (alternatingGroup (Fin 4)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e ((mem_center_iff.mp hxZ) z)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at heZ
  have : (⟨x, hxH⟩ : H) = 1 := e.injective (heZ.trans e.map_one.symm)
  exact congrArg Subtype.val this


private theorem four_to_dihedral_trivial (f : A4 →* D10) (x : A4) : f x = 1 := by
  have hker : (⊤ : Subgroup A4) ≤ f.ker := by
    rw [← alternatingGroup.closure_isThreeCycles_eq_top]
    apply (Subgroup.closure_le _).2
    intro y hy
    have h₃ : orderOf (f y) ∣ 3 := by
      convert orderOf_map_dvd f y using 1
      exact ((Subgroup.orderOf_coe y).symm.trans hy.orderOf).symm
    have h₁₀ : orderOf (f y) ∣ 10 := by
      simpa only [DihedralGroup.nat_card] using orderOf_dvd_natCard (f y)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (show orderOf (f y) ∣ 1 from
      Nat.dvd_gcd h₃ h₁₀))
  exact hker (mem_top x)

private theorem dihedral_range (a : A4 →* D10 × A5) (ha : Function.Injective a)
    (b : D10 →* D10 × A5) (hb : Function.Injective b)
    (hc : ∀ x y, Commute (a x) (b y)) :
    b.range = (⊤ : Subgroup D10).prod (⊥ : Subgroup A5) := by
  let a₁ := (MonoidHom.fst D10 A5).comp a
  let a₂ := (MonoidHom.snd D10 A5).comp a
  let b₁ := (MonoidHom.fst D10 A5).comp b
  let b₂ := (MonoidHom.snd D10 A5).comp b
  have ha₁ (x : A4) : (a x).1 = 1 := four_to_dihedral_trivial a₁ x
  have ha₂ : Function.Injective a₂ := by
    intro x y h
    exact ha (Prod.ext ((ha₁ x).trans (ha₁ y).symm) h)
  have hCa : centralizer (a₂.range : Set A5) = ⊥ :=
    four_centralizer a₂.range (MonoidHom.ofInjective ha₂).symm
  have hb₂ (y : D10) : (b y).2 = 1 := by
    have hy : b₂ y ∈ centralizer (a₂.range : Set A5) := by
      rw [mem_centralizer_iff]
      rintro z ⟨x, rfl⟩
      exact congrArg Prod.snd (hc x y).eq
    exact (hCa ▸ hy : b₂ y ∈ (⊥ : Subgroup A5))
  have hb₁ : Function.Injective b₁ := by
    intro x y h
    exact hb (Prod.ext h ((hb₂ x).trans (hb₂ y).symm))
  have hs : Function.Surjective b₁ :=
    ((Nat.bijective_iff_injective_and_card b₁).mpr ⟨hb₁, rfl⟩).surjective
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨mem_top _, hb₂ y⟩
  · rintro ⟨_, hz⟩
    obtain ⟨y, hy⟩ := hs z.1
    exact ⟨y, Prod.ext hy ((hb₂ y).trans hz.symm)⟩

/-- An embedded dihedral group of order ten normalizes an actual subgroup of order five. -/
theorem exists_five_subgroup {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (eB : B ≃* D10) :
    ∃ E : Subgroup G, Nat.card E = 5 ∧ E ≤ B ∧ B ≤ normalizer (E : Set G) := by
  let x : B := eB.symm (.r 1)
  let P : Subgroup B := zpowers x
  have hP : Nat.card P = 5 := by
    rw [Nat.card_zpowers, show orderOf x = orderOf (DihedralGroup.r (1 : ZMod 5))
      from eB.symm.orderOf_eq _, DihedralGroup.orderOf_r_one]
  have hB : Nat.card B = 10 := by
    rw [Nat.card_congr eB.toEquiv, DihedralGroup.nat_card]
  have hi : P.index = 2 := by
    have h := P.card_mul_index
    rw [hP, hB] at h
    omega
  let : P.Normal := normal_of_index_eq_two hi
  refine ⟨P.map B.subtype, ?_, map_subtype_le P, ?_⟩
  · rw [card_map_of_injective B.subtype_injective, hP]
  · have h := P.le_normalizer_map B.subtype
    rw [P.normalizer_eq_top, ← MonoidHom.range_eq_map, B.range_subtype] at h
    exact h

/-- A dihedral ten-subgroup commuting with an A₄ is the first factor of a
`D₁₀ × A₅` overgroup. If that overgroup contains its whole ambient centralizer,
the latter is isomorphic to the actual alternating group on five letters. -/
theorem centralizer_equiv_of_commuting_four {G : Type*} [Group G]
    (A B M : Subgroup G) (hAM : A ≤ M) (hBM : B ≤ M)
    (hCM : centralizer (B : Set G) ≤ M)
    (eA : A ≃* A4) (eB : B ≃* D10) (eM : M ≃* D10 × A5)
    (hAB : A ≤ centralizer (B : Set G)) :
    Nonempty (centralizer (B : Set G) ≃* A5) := by
  let a : A4 →* D10 × A5 :=
    eM.toMonoidHom.comp ((inclusion hAM).comp eA.symm.toMonoidHom)
  let b : D10 →* D10 × A5 :=
    eM.toMonoidHom.comp ((inclusion hBM).comp eB.symm.toMonoidHom)
  have ha : Function.Injective a :=
    eM.injective.comp ((inclusion_injective hAM).comp eA.symm.injective)
  have hb : Function.Injective b :=
    eM.injective.comp ((inclusion_injective hBM).comp eB.symm.injective)
  have hc (x : A4) (y : D10) : Commute (a x) (b y) := by
    refine (show Commute (inclusion hAM (eA.symm x))
      (inclusion hBM (eB.symm y)) from ?_).map eM
    apply Subtype.ext
    exact ((mem_centralizer_iff.mp (hAB (eA.symm x).property))
      (eB.symm y) (eB.symm y).property).symm
  have hr := dihedral_range a ha b hb hc
  have hb₂ (y : B) : (eM (inclusion hBM y)).2 = 1 := by
    have hy : b (eB y) ∈ (⊤ : Subgroup D10).prod (⊥ : Subgroup A5) :=
      hr ▸ (show b (eB y) ∈ b.range from ⟨eB y, rfl⟩)
    have hy' : (b (eB y)).2 = 1 := hy.2
    simpa only [b, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hy'
  have hf₁ (k : centralizer (B : Set G)) : (eM (inclusion hCM k)).1 = 1 := by
    have hz : (eM (inclusion hCM k)).1 ∈ center D10 := by
      rw [mem_center_iff]
      intro d
      have hd : (d, (1 : A5)) ∈ b.range := hr ▸ (show
        (d, (1 : A5)) ∈ (⊤ : Subgroup D10).prod (⊥ : Subgroup A5) from
        ⟨mem_top _, rfl⟩)
      obtain ⟨y, hy⟩ := hd
      have he : Commute (b y) (eM (inclusion hCM k)) := by
        refine (show Commute (inclusion hBM (eB.symm y))
          (inclusion hCM k) from ?_).map eM
        apply Subtype.ext
        exact (mem_centralizer_iff.mp k.property) (eB.symm y) (eB.symm y).property
      rw [hy] at he
      exact congrArg Prod.fst he.eq
    rwa [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide), mem_bot] at hz
  let f : centralizer (B : Set G) →* A5 :=
    (MonoidHom.snd D10 A5).comp (eM.toMonoidHom.comp (inclusion hCM))
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro k l h
    apply (inclusion_injective hCM)
    apply eM.injective
    exact Prod.ext ((hf₁ k).trans (hf₁ l).symm) h
  · intro y
    let g : M := eM.symm (1, y)
    have hg : (g : G) ∈ centralizer (B : Set G) := by
      rw [mem_centralizer_iff]
      intro z hz
      have hzg : inclusion hBM ⟨z, hz⟩ * g = g * inclusion hBM ⟨z, hz⟩ := by
        apply eM.injective
        rw [map_mul, map_mul, show eM g = (1, y) from eM.apply_symm_apply _]
        apply Prod.ext
        · simp only [Prod.fst_mul, mul_one, one_mul]
        · simp only [Prod.snd_mul, hb₂ ⟨z, hz⟩, mul_one, one_mul]
      exact congrArg Subtype.val hzg
    refine ⟨⟨g, hg⟩, ?_⟩
    change (eM (⟨(g : G), _⟩ : M)).2 = y
    change (eM g).2 = y
    rw [show eM g = (1, y) from eM.apply_symm_apply _]

end Theory.SpecificGroups.Alternating.DihedralFiveCentralizer
