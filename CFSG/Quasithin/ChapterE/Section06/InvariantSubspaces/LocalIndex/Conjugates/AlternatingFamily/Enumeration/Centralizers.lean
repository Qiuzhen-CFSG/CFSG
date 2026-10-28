module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Setup
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.Inputs

/-!
# Centralizers for the alternating-five elementary-family calculation

The given equivariant coordinates identify centralizers in the actual block
module `U` with fixed spaces in the binary degree-five permutation core.
Since `Q = UD` and `D` is central in `S`, the product cardinality formula
transports every fixed-space index to `Q`; the intersection `U ∩ D` cancels.
The double transposition detects the full actor's centralizer by containment
and equality of these finite orders.

For the opposite subgroup, every vector fixed by the full actor is a sum
of two transposition displacements. Normality of `Uˣ` in `R` places these
displacements in `Uˣ`, giving `C_U(Uˣ) ≤ Uˣ`. The factorization `S = UˣQ`
then gives `C_S(Uˣ) = UˣD`. Conjugating the defining centralizer of `Q`
identifies this with `Qˣ`, and hence gives the intrinsic order equality.
Neither argument assumes membership in the maximum elementary family.

The coordinates are explicit inputs: their construction and the final
`EnumerationInput` assembly belong to the calling development.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2,
printed pp.83–84, and the proof of C.5.6, printed pp.157–158
(PDF pp.168–169).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration

private theorem sup_inf_of_normalizes {T : Type*} [Group T]
    (V D C : Subgroup T) (hn : D ≤ normalizer (V : Set T)) (hd : D ≤ C) :
    (V ⊔ D) ⊓ C = (V ⊓ C) ⊔ D := by
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    have hp : g ∈ (V : Set T) * (D : Set T) := by
      rw [← coe_mul_of_right_le_normalizer_left V D hn]
      exact hg
    obtain ⟨v, hv, d, hd', rfl⟩ := hp
    have hvC : v ∈ C := by
      simpa using C.mul_mem hc (C.inv_mem (hd hd'))
    exact mul_mem_sup ⟨hv, hvC⟩ hd'
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right hd)

private theorem card_sup_fixed {T : Type*} [Group T] [Finite T]
    (V D C : Subgroup T) (hn : D ≤ centralizer (V : Set T)) (hd : D ≤ C)
    (n : ℕ) (hc : Nat.card (V ⊓ C : Subgroup T) * n = Nat.card V) :
    Nat.card ((V ⊔ D) ⊓ C : Subgroup T) * n = Nat.card (V ⊔ D : Subgroup T) := by
  have hnorm := hn.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm' : D ≤ normalizer ((V ⊓ C : Subgroup T) : Set T) :=
    (hn.trans (centralizer_le (show (V ⊓ C : Subgroup T) ≤ V from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hi : (V ⊓ C) ⊓ D = V ⊓ D := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans hd)) inf_le_right
  have h1 := card_mul_eq_card_inf_mul_card_sup_of_normalizes V D hnorm
  have h2 := card_mul_eq_card_inf_mul_card_sup_of_normalizes (V ⊓ C) D hnorm'
  rw [hi] at h2
  rw [sup_inf_of_normalizes V D C hnorm hd]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(V ⊓ D)))
  calc
    _ = (Nat.card (V ⊓ C : Subgroup T) * Nat.card D) * n := by rw [← mul_assoc, ← h2]
    _ = Nat.card V * Nat.card D := by rw [mul_right_comm, hc]
    _ = _ := h1

private theorem map_relative_centralizer {T : Type*} [Group T]
    (S V : Subgroup T) (hV : V ≤ S) (B : Subgroup S) :
    ((V.subgroupOf S) ⊓ centralizer (B : Set S)).map S.subtype =
      V ⊓ centralizer (B.map S.subtype : Set T) := by
  ext g
  constructor
  · rintro ⟨s, ⟨hsV, hsC⟩, rfl⟩
    refine ⟨hsV, ?_⟩
    rintro y ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hsC b hb)
  · rintro ⟨hgV, hgC⟩
    refine ⟨⟨g, hV hgV⟩, ⟨hgV, ?_⟩, rfl⟩
    intro b hb
    exact Subtype.ext (hgC b.val (mem_map_of_mem S.subtype hb))

variable {G : Type*} [Group G] {R L : Subgroup G}

private theorem actionImage_subtype (c : ActionCoordinates R L) (B : Subgroup (S R)) :
    actionImage c.action (B.map (S R).subtype) = B.map (restrictedAction c) := by
  rw [← restrictedAction_image c (map_subtype_le B)]
  exact congrArg (fun E => E.map (restrictedAction c))
    (comap_map_eq_self_of_injective (S R).subtype_injective B)

private theorem fixed_card_mul_index (B : Subgroup Perm) (hB : B ≤ ChapterB.Offenders.D 5) :
    Nat.card (fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) B) * fixedIndex B =
      Nat.card Vector := by
  rcases subgroup_cases B hB with rfl | rfl | rfl | rfl | rfl
  · rw [fixedSpace_bot, fixedIndex_bot, mul_one]
    exact Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) Vector) ≃ₗ[ZMod 2] Vector).toEquiv
  · rw [fixed_line_card, fixedIndex_line, vector_card]
  · rw [fixed_line_card, fixedIndex_line, vector_card]
  · rw [fixed_diagonal_card, fixedIndex_diagonal, vector_card]
  · rw [fixed_actor_card, fixedIndex_actor, vector_card]

private theorem module_card (c : ActionCoordinates R L) : Nat.card (U L) = Nat.card Vector := by
  rw [← c.moduleMap_range]
  exact (Nat.card_congr (MonoidHom.ofInjective c.moduleMap_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

private theorem core_centralizer_card [Finite G] {K : GroupClass} {A H : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hp : Factorization R L x) (hf : F R L = ⊥) (c : ActionCoordinates R L)
    (B : Subgroup G) (hB : B ≤ S R) :
    Nat.card (Q R L ⊓ centralizer (B : Set G) : Subgroup G) *
      fixedIndex (actionImage c.action B) = Nat.card (Q R L) := by
  have hd := D_centralizes_S h hb hp hf
  have hdB := hd.trans (centralizer_le hB)
  have hdU := hd.trans (centralizer_le hb.module_le)
  rw [hp.core]
  apply card_sup_fixed (U L) (D R L) (centralizer (B : Set G)) hdU hdB
  rw [module_centralizer_card c (hB.trans inf_le_left), module_card c]
  exact fixed_card_mul_index _ ((actionImage_mono c.action hB).trans c.baumann_image.le)

private theorem intrinsic_card_fixed [Finite G] {K : GroupClass} {A H : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hp : Factorization R L x) (hf : F R L = ⊥) (c : ActionCoordinates R L)
    (B : Subgroup (S R)) :
    Nat.card (coreIn R L ⊓ centralizer (B : Set (S R)) : Subgroup (S R)) *
      fixedIndex (B.map (restrictedAction c)) = Nat.card (coreIn R L) := by
  have hc := core_centralizer_card h hb hp hf c (B.map (S R).subtype) (map_subtype_le B)
  rw [actionImage_subtype] at hc
  rw [← map_relative_centralizer (S R) (Q R L) (hb.core_eq ▸ inf_le_left) B,
    card_map_of_injective (S R).subtype_injective] at hc
  change _ = Nat.card ((Q R L).subgroupOf (S R))
  rw [Nat.card_congr (subgroupOfEquivOfLe (hb.core_eq ▸ inf_le_left)).toEquiv]
  exact hc

/-- Transport of every fixed-space index and the full-actor detection test. -/
theorem fixedProfile [Finite G] {K : GroupClass} {A H : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hp : Factorization R L x) (hf : F R L = ⊥) (c : ActionCoordinates R L) :
    FixedProfile (restrictedAction c) (coreIn R L) := by
  have hc := intrinsic_card_fixed h hb hp hf c
  refine ⟨hc, ?_⟩
  intro B b hbB hB hbb
  have h1 := hc B
  have h2 := hc (zpowers b)
  rw [hB, fixedIndex_actor] at h1
  rw [MonoidHom.map_zpowers, hbb, ← diagonal, fixedIndex_diagonal,
    zpowers_eq_closure, centralizer_closure] at h2
  apply eq_of_le_of_card_ge
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hbB))
  · exact (Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4) (h2.trans h1.symm)).le

private def seedZero (a : ZMod 2) : Vector :=
  ⟨![a, 0, 0, 0, a], by
    change (∑ i : Fin 5, (![a, 0, 0, 0, a] : Fin 5 → ZMod 2) i) = 0
    simp [Fin.sum_univ_succ, CharTwo.add_self_eq_zero]⟩

private def seedOne (a : ZMod 2) : Vector :=
  ⟨![0, 0, a, 0, a], by
    change (∑ i : Fin 5, (![0, 0, a, 0, a] : Fin 5 → ZMod 2) i) = 0
    simp [Fin.sum_univ_succ, CharTwo.add_self_eq_zero]⟩

private theorem fixed_displacements (v : Vector)
    (hv : v ∈ fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (ChapterB.Offenders.D 5)) :
    ∃ w₀ w₁ : Vector,
      v = (BinaryPermutation.coreRepresentation (Fin 5) (transposition 0) w₀ - w₀) +
        (BinaryPermutation.coreRepresentation (Fin 5) (transposition 1) w₁ - w₁) := by
  obtain ⟨h0, h1⟩ := (mem_fixed_actor v).mp hv
  refine ⟨seedZero (v.val 0), seedOne (v.val 2), ?_⟩
  have h4 : v.val 4 = 0 := by
    have hs := v.property
    change (∑ i : Fin 5, v.val i) = 0 at hs
    simpa [Fin.sum_univ_succ, ← h0, ← h1, CharTwo.add_self_eq_zero,
      ← add_assoc] using hs
  apply Subtype.ext
  funext i
  change v.val i =
    ((seedZero (v.val 0)).val ((transposition 0).symm i) - (seedZero (v.val 0)).val i) +
      ((seedOne (v.val 2)).val ((transposition 1).symm i) - (seedOne (v.val 2)).val i)
  fin_cases i <;>
    simp [seedZero, seedOne, transposition, ChapterB.Offenders.pairSwap, h0, h1, h4,
      CharTwo.neg_eq, Equiv.swap_apply_def]

private theorem displacement_mem (c : ActionCoordinates R L) (V : Subgroup G)
    (hN : U L ≤ normalizer (V : Set G)) {p : Perm} (hp : p ∈ actionImage c.action V)
    (w : Vector) :
    c.moduleMap (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) p w - w)) ∈ V := by
  obtain ⟨r, hr, rfl⟩ := hp
  let u := c.moduleMap (Multiplicative.ofAdd w)
  have hu : u ∈ U L := c.moduleMap_range ▸ (show u ∈ c.moduleMap.range from ⟨_, rfl⟩)
  have hn : u * (r.val)⁻¹ * u⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (hN hu) _).mp (V.inv_mem hr)
  have he : c.moduleMap (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (c.action r) w - w)) =
      r.val * (u * (r.val)⁻¹ * u⁻¹) := by
    have heq := c.equivariant r (Multiplicative.ofAdd w)
    simp only [toAdd_ofAdd] at heq
    rw [ofAdd_sub, map_div, ← heq]
    simp only [div_eq_mul_inv, mul_assoc, u]
  rw [he]
  exact V.mul_mem hr hn

private theorem module_centralizer_le_conjugate [Finite G] {K : GroupClass}
    {A H : Subgroup G} {x : G} (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (hx : x ∈ A) (hp : Factorization R L x)
    (c : ActionCoordinates R L) :
    U L ⊓ centralizer ((U L).map (MulAut.conj x).toMonoidHom : Set G) ≤
      (U L).map (MulAut.conj x).toMonoidHom := by
  let V := (U L).map (MulAut.conj x).toMonoidHom
  have hVS : V ≤ S R := le_sup_left.trans hp.span.ge
  have hVR : V ≤ R := hVS.trans inf_le_left
  have hQR : Q R L ≤ R := (hb.core_eq ▸ inf_le_left).trans inf_le_left
  have hact : actionImage c.action V = ChapterB.Offenders.D 5 := by
    have he := congrArg (actionImage c.action) hp.span
    rw [c.baumann_image, actionImage_sup _ hVR hQR, c.core_image hb, sup_bot_eq] at he
    exact he.symm
  have hn : U L ≤ normalizer (V : Set G) :=
    (hb.module_le.trans inf_le_left).trans (Factorizations.R_normalizes_conjugate h hx)
  rintro g ⟨hgU, hgC⟩
  rw [← c.moduleMap_range] at hgU
  obtain ⟨v, rfl⟩ := hgU
  have hv := (moduleMap_mem_centralizer_iff c hVR v).mp hgC
  rw [hact] at hv
  obtain ⟨w₀, w₁, he⟩ := fixed_displacements v.toAdd hv
  change c.moduleMap (Multiplicative.ofAdd v.toAdd) ∈ V
  rw [he, ofAdd_add, map_mul]
  apply V.mul_mem
  · exact displacement_mem c V hn (hact ▸ ChapterB.Offenders.pairSwap_mem 0 (by decide)) w₀
  · exact displacement_mem c V hn (hact ▸ ChapterB.Offenders.pairSwap_mem 1 (by decide)) w₁

/-- The opposite is the actual conjugate core, before any maximum-family argument. -/
theorem opposite_eq_conjugate_core [Finite G] {K : GroupClass} {A H : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A) (hp : Factorization R L x) (c : ActionCoordinates R L) :
    opposite R L x = (Q R L).map (MulAut.conj x).toMonoidHom := by
  let V := (U L).map (MulAut.conj x).toMonoidHom
  let C := centralizer (V : Set G)
  have hVS : V ≤ S R := le_sup_left.trans hp.span.ge
  have hnVQ : V ≤ normalizer (Q R L : Set G) := hVS.trans (S_normalizes_Q R L)
  let : IsElementaryAbelian 2 (U L) := elementary_U h
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hVC : V ≤ C := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hDU : D R L ≤ centralizer (U L : Set G) :=
    (hp.core ▸ (le_sup_right : D R L ≤ U L ⊔ D R L)).trans (hb.core_eq ▸ inf_le_right)
  have hDC : D R L ≤ C := hp.centralizes
  have hUV : U L ⊓ C ≤ V := module_centralizer_le_conjugate h hb hx hp c
  rw [conjugate_core_eq h hb hx]
  change V ⊔ D R L = S R ⊓ C
  calc
    V ⊔ D R L = ((U L ⊓ C) ⊔ D R L) ⊔ V := by
      apply le_antisymm
      · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
      · exact sup_le (sup_le (hUV.trans le_sup_left) le_sup_right) le_sup_left
    _ = (Q R L ⊓ C) ⊔ V := by
      rw [hp.core, sup_inf_of_normalizes (U L) (D R L) C
        (hDU.trans (Subgroup.centralizer_le_normalizer _)) hDC]
    _ = (Q R L ⊔ V) ⊓ C :=
      (sup_inf_of_normalizes (Q R L) V C hnVQ hVC).symm
    _ = S R ⊓ C := by rw [sup_comm, ← hp.span]

/-- Equality of the intrinsic orders follows by actual conjugation in `G`. -/
theorem oppositeIn_card [Finite G] {K : GroupClass} {A H : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A) (hp : Factorization R L x) (c : ActionCoordinates R L) :
    Nat.card (oppositeIn R L x) = Nat.card (coreIn R L) := by
  change Nat.card ((opposite R L x).subgroupOf (S R)) =
    Nat.card ((Q R L).subgroupOf (S R))
  rw [Nat.card_congr (subgroupOfEquivOfLe (opposite_le_S hp)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (hb.core_eq ▸ inf_le_left)).toEquiv,
    opposite_eq_conjugate_core h hb hx hp c,
    card_map_of_injective (MulAut.conj x).injective]

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration

end
