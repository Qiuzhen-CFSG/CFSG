module

public import Theory.GroupTheory.Hall.TwoClosedNormal
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Two-closed abelian quotients under homomorphisms

A surjection with two-group kernel induces an isomorphism modulo the two-cores.
Consequently a normal Sylow two-subgroup and an abelian odd quotient lift through
such a surjection. A central kernel also preserves normality of the Sylow
two-subgroup, using the exact preimage of its normalizer. Alternatively, determinant characters with two-group kernel
and odd abelian target directly exhibit these properties.

Source application: the covered Borel in Aschbacher--Smith, 4.4.13,
`refs/quasithin.pdf`, printed pp.623--624.
-/

public section
open Subgroup
namespace Subgroup.OddHall
variable {G H A : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- Two-group kernels preserve the exact quotient by the two-core. -/
theorem TwoClosedAbelianQuotient.of_surjective_two_kernel
    {B : Subgroup G} {D : Subgroup H} (f : B →* D) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hd : TwoClosedAbelianQuotient D) :
    TwoClosedAbelianQuotient B := by
  let e := f.pCoreQuotientEquiv hf hk
  refine ⟨?_, ?_⟩
  · rw [index_eq_card, Nat.card_congr e.toEquiv, ← index_eq_card]
    exact hd.odd_index
  · let := hd.abelian
    apply IsMulCommutative.of_comm
    intro x y
    apply e.injective
    simp only [map_mul]
    exact mul_comm' _ _

omit [Finite H] in
/-- A central extension of a group with normal Sylow two-subgroup has normal Sylow two-subgroup. -/
theorem odd_pCore_index_of_surjective_central_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hi : Odd (pCore 2 H).index) :
    Odd (pCore 2 G).index := by
  let P : Sylow 2 G := default
  let Q : Sylow 2 H := (pCore_isPGroup (p := 2) (G := H)).toSylow
    (Nat.not_even_iff_odd.mpr hi ∘ even_iff_two_dvd.mpr)
  have he : Q = P.mapSurjective hf :=
    Sylow.ext (Q.is_maximal' (P.mapSurjective hf).isPGroup'
      (pCore_isPGroup.le_sylow_of_normal (P.mapSurjective hf))).symm
  have hnorm : normalizer (P.mapSurjective hf : Set H) = ⊤ := by
    rw [← he]
    exact normalizer_eq_top (pCore 2 H)
  have hn : (P : Subgroup G).Normal := normalizer_eq_top_iff.mp (by
    change normalizer (P : Set G) = ⊤
    rw [← P.normalizer_comap_of_central_kernel f hf hk, hnorm, comap_top])
  have hcore : pCore 2 G = (P : Subgroup G) := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨hn, P.isPGroup'⟩)
  rw [hcore]
  exact Nat.not_even_iff_odd.mp (P.not_dvd_index ∘ even_iff_two_dvd.mp)

omit [Finite H] in
/-- Normality of the Sylow two-subgroup lifts to the full preimage through a central cover. -/
theorem odd_pCore_index_comap_of_central_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (D : Subgroup H) (hi : Odd (pCore 2 D).index) :
    Odd (pCore 2 (D.comap f)).index := by
  let r : D.comap f →* D := (f.comp (D.comap f).subtype).codRestrict D (fun x => x.property)
  have hr : Function.Surjective r := by
    intro d
    obtain ⟨g, hg⟩ := hf d.val
    exact ⟨⟨g, show f g ∈ D from hg.symm ▸ d.property⟩, Subtype.ext hg⟩
  apply odd_pCore_index_of_surjective_central_kernel r hr _ hi
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp (hk (congrArg (fun d : D => d.val) hx)) y.val

variable [CommGroup A] [Finite A]
omit [Group H] [Finite H] [Finite G] [Finite A] in
/-- Odd abelian characters with two-group kernel identify the two-core. -/
theorem twoClosedAbelianQuotient_of_characters {B : Subgroup G}
    (f : B →* A) (hk : IsPGroup 2 f.ker) (ha : Odd (Nat.card A)) :
    TwoClosedAbelianQuotient B := by
  have he : f.ker = pCore 2 B := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hk⟩
    · have hbot : (pCore 2 B).map f = ⊥ := by
        apply card_eq_one.mp
        exact (pCore_isPGroup.map f : IsPGroup 2 ((pCore 2 B).map f)).card_eq_or_dvd.resolve_right
          (fun h => (Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr ha))
            (h.trans (card_subgroup_dvd_card _)))
      exact (map_eq_bot_iff _).mp hbot
  let e := (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  refine ⟨?_, ?_⟩
  · rw [index_eq_card, Nat.card_congr e.toEquiv]
    exact ha.of_dvd_nat (card_subgroup_dvd_card f.range)
  · exact IsMulCommutative.of_comm (fun x y => e.injective (by simp only [map_mul, mul_comm]))

end Subgroup.OddHall
