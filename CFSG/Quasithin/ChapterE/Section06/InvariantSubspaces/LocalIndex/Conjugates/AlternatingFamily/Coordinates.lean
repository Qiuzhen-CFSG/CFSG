module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Reduction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs

/-!
# Permutation coordinates for the alternating-five family

The two commuting transpositions `(0 1)` and `(2 3)` form the actual
Baumann actor in the binary degree-five permutation module. The even
permutation `(0 2)(1 3)` lies outside that actor and interchanges its two
transposition lines. These finite calculations distinguish the two extra
maximum elementary subgroups from the core and its opposite candidate.

`ActionCoordinates` requires an equivariant embedding of the full even-weight
core onto the actual block module `U`, not merely an isomorphism of a quotient
or an unconnected group-family label. Its kernel is the actual centralizer.
The action and exhaustive-enumeration inputs below are explicit unproved
contracts. They contain no assertion of the final local index.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3),
printed p.155, and the proof of C.5.6(5), printed pp.157–158. The finite
actors use the conventions of B.3.2, printed pp.83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open Subgroup

abbrev Perm := Equiv.Perm (Fin 5)
abbrev Vector := BinaryPermutation.core (Fin 5)

def transposition (i : Fin 2) : Perm := ChapterB.Offenders.pairSwap 5 i

def exchange : Perm := ChapterB.Offenders.kleinSecond 5 (by decide)

def line (i : Fin 2) : Subgroup Perm := zpowers (transposition i)

private theorem transposition_order (i : Fin 2) : orderOf (transposition i) = 2 := by
  apply orderOf_eq_prime
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel

theorem mem_line (i : Fin 2) (g : Perm) :
    g ∈ line i ↔ g = 1 ∨ g = transposition i := by
  rw [line, mem_zpowers_iff_mem_range_orderOf, transposition_order]
  simp [Finset.range_add_one, or_comm]

private def word : Fin 4 → Perm :=
  ![1, transposition 0, transposition 1, transposition 0 * transposition 1]

private def four : Subgroup Perm where
  carrier := Set.range word
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have h : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, hj.symm⟩

private theorem actor_eq_four : ChapterB.Offenders.D 5 = four := by
  apply le_antisymm
  · apply (closure_le four).mpr
    rintro g ⟨i, _, rfl⟩
    fin_cases i
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro g ⟨i, rfl⟩
    have h0 : transposition 0 ∈ ChapterB.Offenders.D 5 :=
      ChapterB.Offenders.pairSwap_mem 0 (by decide)
    have h1 : transposition 1 ∈ ChapterB.Offenders.D 5 :=
      ChapterB.Offenders.pairSwap_mem 1 (by decide)
    fin_cases i
    · exact one_mem _
    · exact h0
    · exact h1
    · exact mul_mem h0 h1

theorem exchange_not_mem_actor : exchange ∉ ChapterB.Offenders.D 5 := by
  rw [actor_eq_four]
  change ¬ ∃ i, word i = exchange
  decide +kernel

theorem exchange_line_zero : (line 0).map (MulAut.conj exchange).toMonoidHom = line 1 := by
  rw [line, MonoidHom.map_zpowers]
  congr 1
  decide +kernel

theorem exchange_line_one : (line 1).map (MulAut.conj exchange).toMonoidHom = line 0 := by
  rw [line, MonoidHom.map_zpowers]
  congr 1
  decide +kernel

theorem line_zero_ne_one : line 0 ≠ line 1 := by
  intro h
  have hm : transposition 0 ∈ line 1 := h ▸ mem_zpowers _
  rw [mem_line] at hm
  rcases hm with hm | hm <;> revert hm <;> decide +kernel

theorem line_ne_bot (i : Fin 2) : line i ≠ ⊥ := by
  intro h
  have hm : transposition i ∈ (⊥ : Subgroup Perm) := h ▸ mem_zpowers _
  have hi : transposition i ≠ 1 := by fin_cases i <;> decide +kernel
  exact hi (mem_bot.mp hm)

theorem line_ne_actor (i : Fin 2) : line i ≠ ChapterB.Offenders.D 5 := by
  intro h
  have h0 : transposition 0 ∈ line i := h ▸ ChapterB.Offenders.pairSwap_mem 0 (by decide)
  have h1 : transposition 1 ∈ line i := h ▸ ChapterB.Offenders.pairSwap_mem 1 (by decide)
  rw [mem_line] at h0 h1
  fin_cases i
  · rcases h1 with h1 | h1 <;> revert h1 <;> decide +kernel
  · rcases h0 with h0 | h0 <;> revert h0 <;> decide +kernel

universe u
variable {G : Type u} [Group G]

/-- The action image of an ambient subgroup, restricted to the Sylow group. -/
def actionImage {R : Subgroup G} (σ : R →* Perm) (B : Subgroup G) : Subgroup Perm :=
  (B.subgroupOf R).map σ

/-- Coordinates for the actual four-dimensional permutation action. This does
not assert anything about the maximum elementary family. The kernel is the
actual centralizer, and the inner actor is the even permutation `(0 2)(1 3)`. -/
structure ActionCoordinates (R L : Subgroup G) where
  action : R →* Perm
  moduleMap : Multiplicative Vector →* G
  moduleMap_injective : Function.Injective moduleMap
  moduleMap_range : moduleMap.range = U L
  equivariant : ∀ (r : R) (v : Multiplicative Vector),
    (r : G) * moduleMap v * (r : G)⁻¹ =
      moduleMap (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5) (action r) v.toAdd))
  kernel : ∀ r : R, action r = 1 ↔ (r : G) ∈ centralizer (U L : Set G)
  baumann_image : actionImage action (S R) = ChapterB.Offenders.D 5
  inner_exchange : exchange ∈ actionImage action (R ⊓ L)

/-- The genuinely missing source action calculation. -/
def ActionInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ChapterC.IsAlternatingBlock L 5 →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x → F R L = ⊥ → Nonempty (ActionCoordinates R L)

/-- The two extra members are distinguished by their order-two permutation
images. Exhaustiveness and maximum order are both required here. The
conjugacy and nonnormality conclusions are proved by the assembly. -/
def EnumerationInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ChapterC.IsAlternatingBlock L 5 →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x → F R L = ⊥ →
      ∀ c : ActionCoordinates R L, ∃ E₀ E₁ : Subgroup G,
        Stellmacher.elementaryAbelianMaxSubgroups (S R) =
          {Q R L, opposite R L x, E₀, E₁} ∧
        actionImage c.action E₀ = line 0 ∧ actionImage c.action E₁ = line 1


variable {R L : Subgroup G}

theorem actionImage_mono (σ : R →* Perm) {B C : Subgroup G} (h : B ≤ C) :
    actionImage σ B ≤ actionImage σ C := map_mono (comap_mono h)

theorem actionImage_sup (σ : R →* Perm) {B C : Subgroup G} (hB : B ≤ R) (hC : C ≤ R) :
    actionImage σ (B ⊔ C) = actionImage σ B ⊔ actionImage σ C := by
  unfold actionImage
  rw [subgroupOf_sup hB hC, Subgroup.map_sup]

/-- Conjugation of subgroups agrees with conjugation of their actual action images. -/
theorem actionImage_conj (σ : R →* Perm) {B : Subgroup G} (hB : B ≤ R) (r : R) :
    actionImage σ (B.map (MulAut.conj (r : G)).toMonoidHom) =
      (actionImage σ B).map (MulAut.conj (σ r)).toMonoidHom := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : G) ∈ B.map (MulAut.conj (r : G)).toMonoidHom at hy
    obtain ⟨z, hz, hzy⟩ := hy
    let zR : R := ⟨z, hB hz⟩
    have he : r * zR * r⁻¹ = y := Subtype.ext hzy
    refine ⟨σ zR, mem_map_of_mem σ hz, ?_⟩
    change σ r * σ zR * (σ r)⁻¹ = σ y
    rw [← map_inv, ← map_mul, ← map_mul, he]
  · rintro ⟨p, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨r * z * r⁻¹, ?_, ?_⟩
    · exact ⟨(z : G), hz, rfl⟩
    · change σ (r * z * r⁻¹) = σ r * σ z * (σ r)⁻¹
      simp only [map_mul, map_inv]

/-- The core has trivial image in the genuine permutation action. -/
theorem ActionCoordinates.core_image {H : Subgroup G}
    (c : ActionCoordinates R L) (hb : BaumannStructure H R L) :
    actionImage c.action (Q R L) = ⊥ := by
  rw [actionImage, Subgroup.map_eq_bot_iff]
  intro q hq
  apply (c.kernel q).mpr
  exact (hb.core_eq ▸ hq).2

/-- The opposite candidate induces the whole commuting-transposition actor. -/
theorem ActionCoordinates.opposite_image {H : Subgroup G} {x : G}
    (c : ActionCoordinates R L) (hb : BaumannStructure H R L)
    (hp : Factorization R L x) :
    actionImage c.action (opposite R L x) = ChapterB.Offenders.D 5 := by
  have hSR : S R ≤ R := inf_le_left
  have hQR : Q R L ≤ R := (hb.core_eq ▸ inf_le_left).trans hSR
  have hVR : (U L).map (MulAut.conj x).toMonoidHom ≤ R :=
    (le_sup_left.trans hp.span.ge).trans hSR
  have hDR : D R L ≤ R := inf_le_left.trans hSR
  have hD : actionImage c.action (D R L) = ⊥ :=
    le_bot_iff.mp ((actionImage_mono c.action
      (hp.core ▸ (le_sup_right : D R L ≤ U L ⊔ D R L))).trans (c.core_image hb).le)
  have he := congrArg (actionImage c.action) hp.span
  rw [c.baumann_image, actionImage_sup _ hVR hQR, c.core_image hb, sup_bot_eq] at he
  rw [opposite, actionImage_sup _ hVR hDR, hD, sup_bot_eq]
  exact he.symm

/-- The even permutation exchanging the two transposition lines lifts to
an element of the block Sylow group outside the Baumann subgroup. -/
theorem ActionCoordinates.exists_exchange (c : ActionCoordinates R L) :
    ∃ r : R, (r : G) ∈ L ∧ (r : G) ∉ S R ∧ c.action r = exchange := by
  obtain ⟨r, hr, he⟩ := c.inner_exchange
  refine ⟨r, hr.2, ?_, he⟩
  intro hs
  apply exchange_not_mem_actor
  rw [← he, ← c.baumann_image]
  exact mem_map_of_mem c.action hs

/-- A subgroup with the first transposition image is moved by every lift
of the even exchange permutation. -/
theorem moved_of_line_zero (σ : R →* Perm) {B : Subgroup G} (hB : B ≤ R)
    (hline : actionImage σ B = line 0) (r : R) (hr : σ r = exchange) :
    B ≠ B.map (MulAut.conj (r : G)).toMonoidHom := by
  intro he
  have hm := congrArg (actionImage σ) he
  rw [actionImage_conj σ hB r, hline, hr, exchange_line_zero] at hm
  exact line_zero_ne_one hm

/-- The same exchange moves the second transposition image. -/
theorem moved_of_line_one (σ : R →* Perm) {B : Subgroup G} (hB : B ≤ R)
    (hline : actionImage σ B = line 1) (r : R) (hr : σ r = exchange) :
    B ≠ B.map (MulAut.conj (r : G)).toMonoidHom := by
  intro he
  have hm := congrArg (actionImage σ) he
  rw [actionImage_conj σ hB r, hline, hr, exchange_line_one] at hm
  exact line_zero_ne_one hm.symm

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
end
