module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Source
public import Theory.GroupAction.InnerTorusDisplacement
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct

/-!
# The actual elementary subgroup acted on by a block torus

Transport the intrinsic regular torus action through the block inclusion.
Inner witnesses identify both the fixed space and the displacement of the
original elementary subgroup V. Coprime action then gives its direct
decomposition, retaining the regular action on the literal subgroup [V,X].

Source: Aschbacher–Smith E.6.7(3), printed p.246, and E.6.11, p.249.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

/-- Regular conjugation transports through an injective homomorphism. -/
theorem RegularConjugationOnNonidentity.map_injective
    {A G : Type*} [Group A] [Group G] {X D : Subgroup A}
    (h : RegularConjugationOnNonidentity X D) (f : A →* G)
    (hf : Function.Injective f) :
    RegularConjugationOnNonidentity (X.map f) (D.map f) := by
  refine ⟨(map_mono h.1).trans (le_normalizer_map f), ?_⟩
  intro a ha b hb
  obtain ⟨a₀, ha₀, hea⟩ := a.property
  obtain ⟨b₀, hb₀, heb⟩ := b.property
  have ha1 : (⟨a₀, ha₀⟩ : D) ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [← hea, show a₀ = 1 from congrArg Subtype.val he, map_one]
    rfl
  have hb1 : (⟨b₀, hb₀⟩ : D) ≠ 1 := by
    intro he
    apply hb
    apply Subtype.ext
    rw [← heb, show b₀ = 1 from congrArg Subtype.val he, map_one]
    rfl
  obtain ⟨x, hx, hu⟩ := h.2 ⟨a₀, ha₀⟩ ha1 ⟨b₀, hb₀⟩ hb1
  refine ⟨⟨f x, mem_map_of_mem f x.property⟩, ?_, ?_⟩
  · simpa only [← hea, ← heb, map_mul, map_inv] using congrArg f hx
  · intro y hy
    obtain ⟨y₀, hy₀, hey⟩ := y.property
    have he : y₀ * a₀ * y₀⁻¹ = b₀ := hf (by
      simpa only [map_mul, map_inv, hea, heb, hey] using hy)
    have hyx := hu ⟨y₀, hy₀⟩ he
    apply Subtype.ext
    rw [← hey, show y₀ = (x : A) from congrArg Subtype.val hyx]

variable {G : Type*} [Group G] {L V : Subgroup G}
variable {S : Sylow 2 L} {B : Subgroup L} {n : ℕ}

/-- The intrinsic torus fixes only elements centralizing the whole block,
after passage to the original ambient group. -/
theorem RankOneBlockTorus.ambient_fixed_le (d : RankOneBlockTorus L S B n)
    (hn : 1 < n) :
    (Stellmacher.omegaOneCenterAmbient (S : Subgroup L)).map L.subtype ⊓
      centralizer (d.torus.map L.subtype : Set G) ≤ centralizer (L : Set G) := by
  rintro z ⟨⟨z₀, hz₀, rfl⟩, hzX⟩
  have hz : z₀ ∈ center L := d.fixed_le_center hn ⟨hz₀, mem_centralizer_iff.mpr (by
    intro x hx
    apply Subtype.ext
    exact mem_centralizer_iff.mp hzX x (mem_map_of_mem L.subtype hx))⟩
  apply mem_centralizer_iff.mpr
  intro l hl
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)

/-- The actual displacement equals the intrinsic root line and the torus
acts regularly on it. No ambient block-action assertion is assumed here:
the explicit inner witnesses are exactly those supplied by the Sylow action theorem. -/
theorem RankOneBlockTorus.ambient_displacement (d : RankOneBlockTorus L S B n)
    (hn : 1 < n)
    (hinner : ∀ v ∈ V,
      ∃ z ∈ (Stellmacher.omegaOneCenterAmbient (S : Subgroup L)).map L.subtype,
        ∀ l ∈ L, z*l*z⁻¹ = v*l*v⁻¹)
    (hescape : ¬ V ≤ centralizer (L : Set G)) :
    ⁅V, d.torus.map L.subtype⁆ =
      ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆.map L.subtype ∧
    V ⊓ centralizer (d.torus.map L.subtype : Set G) = V ⊓ centralizer (L : Set G) ∧
    RegularConjugationOnNonidentity (d.torus.map L.subtype) ⁅V, d.torus.map L.subtype⁆ := by
  let Z := (Stellmacher.omegaOneCenterAmbient (S : Subgroup L)).map L.subtype
  let X := d.torus.map L.subtype
  have hr := d.regular.map_injective L.subtype L.subtype_injective
  rw [map_commutator] at hr
  have he := Theory.GroupAction.InnerTorusDisplacement.moved_eq L Z V X
    (map_subtype_le _) hinner (d.ambient_fixed_le hn) (by
      intro a ha ha1 b hb hb1
      obtain ⟨x, hx, _⟩ := hr.2 ⟨a, ha⟩
        (fun he => ha1 (congrArg Subtype.val he)) ⟨b, hb⟩
        (fun he => hb1 (congrArg Subtype.val he))
      exact ⟨x, x.property, hx⟩) hescape
  refine ⟨?_, Theory.GroupAction.InnerTorusDisplacement.fixed_eq L Z V X
    (map_subtype_le _) hinner (d.ambient_fixed_le hn), ?_⟩
  · rw [map_commutator]
    exact he
  · rw [he]
    exact hr

/-- Coprime splitting of the original elementary subgroup, with its exact
displacement cardinality and the regular action retained. -/
theorem RankOneBlockTorus.ambient_decomposition [Finite G] [IsElementaryAbelian 2 V]
    (d : RankOneBlockTorus L S B n) (hn : 1 < n)
    (hinner : ∀ v ∈ V,
      ∃ z ∈ (Stellmacher.omegaOneCenterAmbient (S : Subgroup L)).map L.subtype,
        ∀ l ∈ L, z*l*z⁻¹ = v*l*v⁻¹)
    (hescape : ¬ V ≤ centralizer (L : Set G))
    (hnorm : d.torus.map L.subtype ≤ normalizer (V : Set G)) :
    V = (V ⊓ centralizer (L : Set G)) ⊔ ⁅V, d.torus.map L.subtype⁆ ∧
    Disjoint (V ⊓ centralizer (L : Set G)) ⁅V, d.torus.map L.subtype⁆ ∧
    Nat.card ↥⁅V, d.torus.map L.subtype⁆ = 2 ^ n ∧
    RegularConjugationOnNonidentity (d.torus.map L.subtype) ⁅V, d.torus.map L.subtype⁆ := by
  obtain ⟨hm, hf, hr⟩ := d.ambient_displacement hn hinner hescape
  have hc : Nat.Coprime (Nat.card (d.torus.map L.subtype)) (Nat.card V) := by
    rw [card_map_of_injective L.subtype_injective, d.order]
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hk]
    apply Nat.Coprime.pow_right
    apply Nat.coprime_two_right.mpr
    exact Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
      ((show Even (2 : ℕ) by decide).pow_of_ne_zero (by omega)) (by decide)
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime V (d.torus.map L.subtype)
    hnorm (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
  have hdis := commutator_disjoint_centralizer_of_coprime V (d.torus.map L.subtype) hnorm hc
  rw [hf, sup_comm] at hd
  rw [hf] at hdis
  refine ⟨hd, hdis.symm, ?_, hr⟩
  rw [hm, card_map_of_injective L.subtype_injective]
  exact d.displacement_order

end CFSG.Quasithin.ChapterE.Section06
