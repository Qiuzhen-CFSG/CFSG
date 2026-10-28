module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Centrality
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Maps
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The literal cubic local image in G.2.4(8)

The earlier starred core is a Sylow four-group of A₅. Its normalizer has
order twelve. The starred image of the two-residual L₁ normalizes that
four-group and contains it; two-perfection rules out order four. Thus
|L₁*|=12 and |L₁*/O₂(L₁*)|=3. The actual star map has two-group kernel,
so |L₁/O₂(L₁)|=3 as well.

Under O₂(L₁)≤Q_H, the kernel of L₁→H/Q_H is exactly O₂(L₁).
This proves that the source plus image is cyclic of order three.
A cubic starred element is also lifted back to the original L₁, for use
on the genuine natural upper action. No coordinate choice or additional
Borel hypothesis is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

private theorem a5_stabilizer_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
  let : DecidablePred (· ∈ MulAction.stabilizer (alternatingGroup (Fin 5)) i) :=
    fun x => inferInstanceAs (Decidable (x.val i = i))
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

private theorem a5_sylow_normalizer_card {A : Type*} [Group A] [Finite A]
    (e : A ≃* alternatingGroup (Fin 5)) (P : Sylow 2 A) :
    Nat.card (normalizer (P : Set A)) = 12 := by
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P'
  have hm : (normalizer (P : Set A)).map e.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    change (normalizer ((P : Subgroup A) : Set A)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hi
  rw [← a5_stabilizer_card i, ← hm]
  exact Nat.card_congr (e.subgroupMap (normalizer (P : Set A))).toEquiv

private theorem a5_twoPerfect_card {A : Type*} [Group A] [Finite A]
    (e : A ≃* alternatingGroup (Fin 5)) (J : Subgroup A)
    (hp : IsPPerfect 2 J) (P : Sylow 2 A)
    (hPJ : (P : Subgroup A) ≤ J) (hJP : J ≤ normalizer (P : Set A)) :
    Nat.card J = 12 := by
  have hcardA : Nat.card A = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcardP : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hcardA]
    rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
    rfl
  have hlow : 4 ∣ Nat.card J := hcardP ▸ card_dvd_of_le hPJ
  have hupp : Nat.card J ∣ 12 := a5_sylow_normalizer_card e P ▸ card_dvd_of_le hJP
  have hne : Nat.card J ≠ 4 := by
    intro hj
    have htwo : IsPGroup 2 J := IsPGroup.of_card (n := 2) hj
    have hh := hp.hom_eq_one_of_isPGroup htwo (MonoidHom.id J)
    have hsub : Subsingleton J := ⟨fun x y => by
      have hx : x = 1 := DFunLike.congr_fun hh x
      have hy : y = 1 := DFunLike.congr_fun hh y
      exact hx.trans hy.symm⟩
    let : Subsingleton J := hsub
    have : Nat.card J = 1 := Nat.card_unique
    omega
  have hpos := Nat.card_pos (α := J)
  have hle := Nat.le_of_dvd (by decide : 0 < 12) hupp
  have hd : Nat.card J = 4 ∨ Nat.card J = 12 := by
    interval_cases h : Nat.card J <;> norm_num [h] at *
  exact hd.resolve_left hne

/-- Restriction of the literal star quotient to L₁, with its actual image. -/
def terminalLocalStarProjection (D : Setup G) : D.L₁ →* D.star D.L₁ :=
  (D.binaryStarRestriction D.L₁ (((map_subtype_le _).trans inf_le_left).trans
    le_sup_left)).codRestrict _ (fun x =>
      ⟨⟨x, (((map_subtype_le _).trans inf_le_left).trans le_sup_left) x.property⟩,
        x.property, rfl⟩)

omit [Finite G] in
theorem terminalLocalStarProjection_surjective (D : Setup G) :
    Function.Surjective (terminalLocalStarProjection D) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem terminalLocalStarProjection_ker_isPGroup (D : Setup G) :
    IsPGroup 2 (terminalLocalStarProjection D).ker := by
  have he : (terminalLocalStarProjection D).ker =
      (D.binaryStarRestriction D.L₁ (((map_subtype_le _).trans inf_le_left).trans
        le_sup_left)).ker := by
    ext x
    change terminalLocalStarProjection D x = 1 ↔ _
    rw [Subtype.ext_iff]
    rfl
  rw [he]
  exact binaryStarRestriction_ker_isPGroup _ _

namespace Hypothesis
/-- The actual starred local residual has order twelve. -/
theorem terminal_star_local_card (d : Hypothesis D g) (c : EarlierStructure D g) :
    Nat.card (D.star D.L₁) = 12 := by
  have hloc : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  let J := (D.star D.L₁).subgroupOf (D.star D.L)
  let f : D.L₁ →* J :=
    ((starProjection D).comp (inclusion hloc)).codRestrict _ (fun x =>
      ⟨⟨x, (hloc.trans le_sup_left) x.property⟩, x.property, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨j, x, hx, he⟩
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext he)⟩
  have hp : IsPPerfect 2 J :=
    (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.G₁)).of_surjective f hf
  obtain ⟨P, hP⟩ := c.star_sylow
  have hPJ : (P : Subgroup (D.star D.L)) ≤ J := by
    intro x hx
    exact (c.star_core ▸ (hP ▸ mem_map_of_mem (D.star D.L).subtype hx) :
      (x : D.Star) ∈ (D.star D.L₁).pCoreIn 2) |> pCoreIn_le 2 (D.star D.L₁)
  have hUL : D.star D.U ≤ D.star D.L := hP ▸ map_subtype_le _
  have hPe : (P : Subgroup (D.star D.L)) =
      (D.star D.U).subgroupOf (D.star D.L) := by
    apply map_injective (D.star D.L).subtype_injective
    rw [hP, map_subgroupOf_eq_of_le hUL]
  have hJP : J ≤ normalizer (P : Set (D.star D.L)) := by
    change J ≤ normalizer ((P : Subgroup (D.star D.L)) : Set (D.star D.L))
    rw [hPe, ← subgroupOf_normalizer_eq hUL]
    apply comap_mono
    rw [c.star_core]
    exact (D.star D.L₁).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (D.star D.L₁)
        (pCore 2 (D.star D.L₁)))
  have hJ := a5_twoPerfect_card d.model J hp P hPJ hJP
  exact (Nat.card_congr (subgroupOfEquivOfLe (binary_star_mono hloc)).toEquiv).symm.trans hJ

/-- The marked Sylow image has order four. -/
theorem terminal_star_closure_card (d : Hypothesis D g) (c : EarlierStructure D g) :
    Nat.card (D.star D.U) = 4 := by
  obtain ⟨P, hP⟩ := c.star_sylow
  rw [← hP, card_map_of_injective (D.star D.L).subtype_injective,
    P.card_eq_multiplicity, Nat.card_congr d.model.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl

/-- The original local group has cyclic-three core quotient. -/
theorem terminal_local_core_quotient_card (d : Hypothesis D g) (c : EarlierStructure D g) :
    Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 := by
  have hc : Nat.card (pCore 2 (D.star D.L₁)) = 4 := by
    have he := d.terminal_star_closure_card c
    rw [c.star_core, pCoreIn, card_map_of_injective (D.star D.L₁).subtype_injective] at he
    exact he
  have hind : (pCore 2 (D.star D.L₁)).index = 3 := by
    have he := (pCore 2 (D.star D.L₁)).card_mul_index
    rw [d.terminal_star_local_card c, hc] at he
    omega
  rw [← index_eq_card,
    ← (terminalLocalStarProjection D).comap_pCore_of_ker_isPGroup
      (terminalLocalStarProjection_surjective D) (terminalLocalStarProjection_ker_isPGroup D),
    (pCore 2 (D.star D.L₁)).index_comap_of_surjective (terminalLocalStarProjection_surjective D)]
  exact hind

/-- The source plus image uses H/O₂(H), not the star or tilde quotient. -/
theorem terminal_local_plus_card (d : Hypothesis D g) (c : EarlierStructure D g)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) :
    Nat.card ((D.L₁.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) = 3 := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans d.setup.local_le
  let f : D.L₁ →* (D.H ⧸ pCore 2 D.H) :=
    (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion hLH)
  have hk : f.ker = pCore 2 D.L₁ := by
    have he : f.ker = (pCore 2 D.H).comap (inclusion hLH) := by
      ext x
      exact QuotientGroup.eq_one_iff _
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      rw [he]
      exact pCore_isPGroup.comap_of_injective (inclusion hLH) (inclusion_injective hLH)
    · intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨y, hy, heq⟩ := hcore (mem_map_of_mem D.L₁.subtype hx)
      exact (show y = inclusion hLH x from Subtype.ext heq) ▸ hy
  have hr : f.range = (D.L₁.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion hLH y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← hr, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    hk, d.terminal_local_core_quotient_card c]

/-- Cyclicity of the original image in H/O₂(H). -/
theorem terminal_local_plus_isCyclic (d : Hypothesis D g) (c : EarlierStructure D g)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) :
    IsCyclic ((D.L₁.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) :=
  isCyclic_of_prime_card (d.terminal_local_plus_card c hcore)

/-- Lift a cubic element of L₁* to L₁ with its original star marking. -/
theorem terminal_exists_local_cubic_star (d : Hypothesis D g) (c : EarlierStructure D g) :
    ∃ t : D.L, (t : G) ∈ D.L₁ ∧ orderOf (starProjection D t) = 3 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := D.star D.L₁) 3
    (by rw [d.terminal_star_local_card c]; decide)
  obtain ⟨t, ht⟩ := terminalLocalStarProjection_surjective D a
  have hloc : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  let tL : D.L := inclusion hloc t
  refine ⟨tL, t.property, ?_⟩
  have he : (starProjection D tL : D.Star) = (a : D.Star) := congrArg Subtype.val ht
  rw [← Subgroup.orderOf_coe (starProjection D tL), he, Subgroup.orderOf_coe, ha]

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
