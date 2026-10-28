module
public import Stellmacher.Recognition.Parrott.CoreInvolutionGeometry
public import Theory.GroupTheory.CentralBinaryCentralizerCard
public import Theory.GroupAction.Order512FiveOrbit
public import Theory.GroupTheory.ClassThreeCentralizerBound

/-!
# Centralizer counts in Parrott's two-core

For H=C_G(z), J=O₂(H), and E the actual image of J′, every subgroup
⟨z⟩≤U≤E satisfies |U| |C_J(U)|=1024. Inside J, the commutator
pairing U×J→Z(J) has left kernel Z(J), of order two. Binary
pairing double-counting gives the formula, transported through the
literal inclusions J→H→G.

The supplied Sylow-five action also excludes commutator images of order
two for elements outside J′ in J/Z(J): their five-orbits generate J,
and the quotient action has trivial fixed subgroup. The commutator map
J→J/Z(J) has kernel containing C_J(b)J′, of order twice |C_J(b)|.
Its image has order at least four, giving |C_J(b)|≤64 for every b∉J′.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, properties (a)–(d).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition

/-- The central commutator pairing computes every core centralizer of a
subgroup of the derived group containing the original involution. -/
public theorem parrott_core_subgroup_centralizer_card
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ U : Subgroup G, zpowers z ≤ U → U ≤ E →
      Nat.card U * Nat.card ((centralizer (U : Set G)).subgroupOf (J.map H.subtype)) =
        1024 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let embed := H.subtype.comp J.subtype
  let E := D.map embed
  let K := J.map H.subtype
  have hinj : Function.Injective embed := H.subtype_injective.comp J.subtype_injective
  change ∀ U : Subgroup G, zpowers z ≤ U → U ≤ E → _
  intro U hzU hUE
  let A := U.comap embed
  obtain ⟨hZmap, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hAD : A ≤ D := by
    intro a ha
    obtain ⟨d, hd, hda⟩ := hUE ha
    exact hinj hda ▸ hd
  let : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext
    (setLike_mul_comm (s := D) (hAD a.property) (hAD b.property))⟩⟩
  have hZA : center J ≤ A := by
    intro a ha
    exact hzU (hZmap ▸ mem_map_of_mem embed ha)
  have hcomm : ⁅A, ⊤⁆ ≤ center J := by
    apply (commutator_mono hAD le_rfl).trans
    rw [show D = Subgroup.upperCentralSeries J 2 from hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le J 1
  have hZcard : Nat.card (center J) = 2 := by
    have hc := card_map_of_injective (K := center J) (f := embed) hinj
    rw [hZmap, Nat.card_zpowers, h.involution] at hc
    exact hc.symm
  have hmap : A.map embed = U := by
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      exact ha
    · intro x hx
      obtain ⟨a, _, rfl⟩ := hUE hx
      exact ⟨a, hx, rfl⟩
  have hAcard : Nat.card A = Nat.card U := by
    rw [← hmap, card_map_of_injective hinj]
  let C := (centralizer (U : Set G)).subgroupOf K
  let i : centralizer (A : Set J) → C := fun c =>
    ⟨⟨embed c, mem_map_of_mem H.subtype (c : J).property⟩, by
      intro u hu
      obtain ⟨a, ha, rfl⟩ := hmap.symm ▸ hu
      exact congrArg embed (c.property a ha)⟩
  have hi : Function.Bijective i := by
    constructor
    · intro c d hcd
      apply Subtype.ext
      apply hinj
      exact congrArg (fun x : C => ((x : K) : G)) hcd
    · intro c
      obtain ⟨aH, haJ, hac⟩ := (c : K).property
      let a : J := ⟨aH, haJ⟩
      have ha : a ∈ centralizer (A : Set J) := by
        intro b hb
        apply hinj
        change embed b * embed a = embed a * embed b
        have hea : embed a = ((c : K) : G) := hac
        rw [hea]
        exact c.property (embed b) hb
      refine ⟨⟨a, ha⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hac)
  have hCcard : Nat.card (centralizer (A : Set J)) = Nat.card C :=
    Nat.card_congr (Equiv.ofBijective i hi)
  have hc := card_mul_card_centralizer_of_center_two A hZA hcomm hZcard
  rw [hAcard, hCcard, h.core_card] at hc
  exact hc

/-- The Sylow-five action excludes a commutator line of order two in the
central quotient for every core element outside its derived subgroup. -/
public theorem parrott_core_quotient_commutator_card_ne_two
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ b : J, b ∉ commutator J →
      Nat.card ↥(⁅zpowers (QuotientGroup.mk' (center J) b),
        (⊤ : Subgroup (J ⧸ center J))⁆) ≠ 2 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  change ∀ b : J, b ∉ commutator J → _
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hHcard, _⟩ := ParrottCentralizerHypotheses.card_and_solvable z h
  change Nat.card H = 10240 at hHcard
  obtain ⟨P, hP⟩ := h.five_centralizer
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hHcard]
    decide +kernel
  let : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro x hx
    apply hP
    change (x : H) ∈ centralizer (P : Set H)
    intro a ha
    have heq := congrArg (fun y : J => (y : H)) (hx ⟨a, ha⟩)
    change a * (x : H) * a⁻¹ = x at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  intro b hb
  exact Theory.GroupAction.parrott_center_quotient_commutator_card_ne_two
    pCore_isPGroup h.core_card h.core_class hPcard hfixed b hb

/-- Every element of the core outside the derived subgroup has centralizer
of order at most 64 in the actual ambient image of the core. -/
public theorem parrott_core_element_centralizer_card_le_sixty_four
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let K := J.map H.subtype
    ∀ b : G, b ∈ K → b ∉ E →
      Nat.card ((centralizer ({b} : Set G)).subgroupOf K) ≤ 64 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let embed := H.subtype.comp J.subtype
  let E := D.map embed
  let K := J.map H.subtype
  have hinj : Function.Injective embed := H.subtype_injective.comp J.subtype_injective
  change ∀ b : G, b ∈ K → b ∉ E → _
  intro b hb hbE
  obtain ⟨bH, hbJ, rfl⟩ := hb
  let bJ : J := ⟨bH, hbJ⟩
  have hbD : bJ ∉ D := fun hd => hbE (mem_map_of_mem embed hd)
  let C := centralizer ({bJ} : Set J)
  have hfixed : Nat.card (D ⊓ C : Subgroup J) = 16 := by
    have hmap : (D ⊓ C).map embed = E ⊓ centralizer ({(bH : G)} : Set G) := by
      apply le_antisymm
      · rintro x ⟨d, hd, rfl⟩
        exact ⟨mem_map_of_mem embed hd.1, mem_centralizer_singleton_iff.mpr
          (congrArg embed (mem_centralizer_singleton_iff.mp hd.2))⟩
      · rintro x ⟨⟨d, hd, rfl⟩, hc⟩
        refine ⟨d, ⟨hd, ?_⟩, rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        apply hinj
        exact mem_centralizer_singleton_iff.mp hc
    have hc := parrott_core_element_fixed_card z h (bH : G) ⟨bH, hbJ, rfl⟩ hbE
    rw [← hmap, card_map_of_injective hinj] at hc
    exact hc
  obtain ⟨_, _, _, _, hUpper, _, hDcard, _⟩ := parrott_centralizer_structure z h
  have hbound : Nat.card C ≤ 64 :=
    centralizer_card_le_sixty_four_of_quotient_commutator_not_two
      h.core_card hDcard hUpper bJ hbD hfixed
      (parrott_core_quotient_commutator_card_ne_two z h bJ hbD)
  let C' := (centralizer ({(bH : G)} : Set G)).subgroupOf K
  let i : C → C' := fun c =>
    ⟨⟨embed c, mem_map_of_mem H.subtype (c : J).property⟩,
      mem_centralizer_singleton_iff.mpr
        (congrArg embed (mem_centralizer_singleton_iff.mp c.property))⟩
  have hi : Function.Bijective i := by
    constructor
    · intro c d hcd
      apply Subtype.ext
      exact hinj (congrArg (fun x : C' => ((x : K) : G)) hcd)
    · intro c
      obtain ⟨aH, haJ, hac⟩ := (c : K).property
      let a : J := ⟨aH, haJ⟩
      have ha : a ∈ C := by
        apply mem_centralizer_singleton_iff.mpr
        apply hinj
        change embed a * embed bJ = embed bJ * embed a
        have hea : embed a = ((c : K) : G) := hac
        rw [hea]
        exact mem_centralizer_singleton_iff.mp c.property
      exact ⟨⟨a, ha⟩, Subtype.ext (Subtype.ext hac)⟩
  exact (Nat.card_congr (Equiv.ofBijective i hi)) ▸ hbound

/-- In particular, an involution outside the derived core has centralizer
of order at most 64 in the core. -/
public theorem parrott_core_involution_centralizer_card_le_sixty_four
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let K := J.map H.subtype
    ∀ b : G, b ∈ K → b ∉ E → orderOf b = 2 →
      Nat.card ((centralizer ({b} : Set G)).subgroupOf K) ≤ 64 := by
  dsimp only
  intro b hb hbE _
  exact parrott_core_element_centralizer_card_le_sixty_four z h b hb hbE

end Stellmacher.Recognition
