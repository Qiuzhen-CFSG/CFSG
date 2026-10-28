module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.RankOne
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction

/-!
# The even-field quotient from the internal Baumann coordinates

Every Baumann parameter is represented in S ∩ L. Equality of parameters
therefore gives S ≤ LQ, with Q the actual two-core; hence LS = LQ. The
intersection Q ∩ L is O₂(L), so the second isomorphism theorem transports
the defining block isomorphism to LS/Q. The parameter order identifies the
image of S with a defining-characteristic Sylow subgroup of that actual SL₂.
The previously proved two-root-group calculation now gives the required pair.

Only the published natural-coordinate construction remains as an input;
no fixed-lifting or later factorization premise is used.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2)
and C.5.6, printed pp.155–157 (PDF pp.166–168).
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
open Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

omit [Finite G] in
private theorem normalizes_core (R L : Subgroup G) :
    L ⊔ S R ≤ normalizer (Q R L : Set G) :=
  (L ⊔ S R).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G)))

private theorem core_restrict_L (h : Configuration K A H R L) :
    (Q R L).subgroupOf L = pCore 2 L := by
  have hLQ : L ≤ normalizer (Q R L : Set G) := le_sup_left.trans (normalizes_core R L)
  let _ : ((Q R L).subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLQ
  have hle : (Q R L).subgroupOf L ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, (isPGroup_pCoreIn 2 (L ⊔ S R)).comap_subtype⟩
  apply le_antisymm hle
  have hp : pCoreIn 2 L ≤ Q R L := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 L) ((pCoreIn_le 2 L).trans le_sup_left)
    (((Baumann.block_baumann_join_le_H h).trans h.normalizes_L).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  intro l hl
  exact hp (mem_map_of_mem L.subtype hl)

omit [Finite G] in
private theorem internal_span {F : Type*} [Field F]
    (hb : BaumannStructure H R L) (c : NaturalIndices.ActionCoordinates R L F)
    (hi : c.IsInternal) : L ⊔ S R = L ⊔ Q R L := by
  apply le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left (pCoreIn_le 2 _))
  intro s hs
  obtain ⟨t, ht, he⟩ := hi ⟨s, hs⟩
  have hk : c.parameter (t⁻¹ * ⟨s, hs⟩) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hq : (t : G)⁻¹ * s ∈ Q R L := by
    rw [hb.core_eq]
    exact ⟨(S R).mul_mem ((S R).inv_mem t.property) hs, (c.parameter_kernel _).mp hk⟩
  have hh := (L ⊔ Q R L).mul_mem (mem_sup_left ht) (mem_sup_right hq)
  simpa only [Q, mul_inv_cancel_left] using hh

private theorem quotient_of_internal {F : Type*} [Field F]
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (c : NaturalIndices.ActionCoordinates R L F) (hi : c.IsInternal)
    {M : Type*} [Group M] (eL : (L ⧸ pCore 2 L) ≃* M) :
    ∃ f : (L ⊔ S R : Subgroup G) →* M, Function.Surjective f ∧
      f.ker = (Q R L).subgroupOf (L ⊔ S R) := by
  let T := L ⊔ S R
  let N := (Q R L).subgroupOf T
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer (normalizes_core R L)
  let q := QuotientGroup.mk' N
  let g := q.comp (inclusion (show L ≤ T from le_sup_left))
  have hk : g.ker = pCore 2 L := by
    rw [← core_restrict_L h]
    ext l
    change QuotientGroup.mk' N (inclusion le_sup_left l) = 1 ↔ (l : G) ∈ Q R L
    exact QuotientGroup.eq_one_iff _
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N z
    have ht : (t : G) ∈ L ⊔ Q R L := internal_span hb c hi ▸ t.property
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right L (Q R L)
      (le_sup_left.trans (normalizes_core R L))] at ht
    obtain ⟨l, hl, a, ha, he⟩ := ht
    let a' : T := ⟨a, pCoreIn_le 2 T ha⟩
    have ha' : q a' = 1 := (QuotientGroup.eq_one_iff a').mpr ha
    have ht' : inclusion (show L ≤ T from le_sup_left) ⟨l, hl⟩ * a' = t :=
      Subtype.ext he
    refine ⟨⟨l, hl⟩, ?_⟩
    change q (inclusion le_sup_left ⟨l, hl⟩) = q t
    rw [← ht', map_mul, ha', mul_one]
  let e := (QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans eL)
  let f := e.toMonoidHom.comp q
  refine ⟨f, e.surjective.comp (QuotientGroup.mk'_surjective N), ?_⟩
  ext t
  change e (q t) = 1 ↔ t ∈ N
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff t

omit [Finite G] in
private theorem image_card {F : Type*} [Field F]
    (hb : BaumannStructure H R L) (c : NaturalIndices.ActionCoordinates R L F)
    {M : Type*} [Group M] (f : (L ⊔ S R : Subgroup G) →* M)
    (hk : f.ker = (Q R L).subgroupOf (L ⊔ S R)) :
    Nat.card (((S R).subgroupOf (L ⊔ S R)).map f) = Nat.card F := by
  rw [← relIndex_ker, hk]
  change ((Q R L).comap (L ⊔ S R).subtype).relIndex _ = _
  rw [relIndex_comap, map_subgroupOf_eq_of_le le_sup_right, hb.core_eq]
  have hi : (S R ⊓ centralizer (U L : Set G)).subgroupOf (S R) =
      (centralizer (U L : Set G)).subgroupOf (S R) := by
    ext s
    exact and_iff_right s.property
  change ((S R ⊓ centralizer (U L : Set G)).subgroupOf (S R)).index = _
  rw [hi]
  exact NaturalIndices.actor_index c

private theorem sylow_of_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hB : IsPGroup 2 B) (hc : Nat.card B = Nat.card F) :
    ∃ T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), B = T := by
  obtain ⟨T, ht⟩ := hB.exists_le_sylow
  refine ⟨T, Subgroup.eq_of_le_of_card_ge ht ?_⟩
  have he : Nat.card (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      Nat.card (Matrix.SpecialLinearGroup.upperUnipotent F) := by
    rw [← Matrix.SpecialLinearGroup.coe_upperUnipotentSylow F 2,
      Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  rw [he, Matrix.SpecialLinearGroup.card_upperUnipotent, hc]

/-- The internal natural coordinates identify the actual core quotient and Sylow image. -/
theorem linear_model_of_coordinates {n : ℕ} (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (hL : ChapterC.IsL2EvenBlock L n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (c : NaturalIndices.ActionCoordinates R L F) (hi : c.IsInternal) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : CharP F' 2),
      Nonempty (RankOneQuotient R L F') := by
  obtain ⟨_, _, F', _, _, hF', _, hmodel⟩ := hL
  let _ : Fintype F' := Fintype.ofFinite F'
  let _ : CharP F' 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF')
  obtain ⟨eL⟩ := hmodel.quotient_iso
  obtain ⟨f, hf, hk⟩ := quotient_of_internal h hb c hi eL
  have hc : Nat.card (((S R).subgroupOf (L ⊔ S R)).map f) = Nat.card F' :=
    (image_card hb c f hk).trans (hF.trans hF'.symm)
  have hp : IsPGroup 2 (((S R).subgroupOf (L ⊔ S R)).map f) :=
    (((Chapter1.isSylowIn_iff.mp h.sylow).1.to_le
      (show S R ≤ R from inf_le_left)).comap_subtype).map f
  obtain ⟨T, hT⟩ := sylow_of_card _ hp hc
  exact ⟨F', inferInstance, inferInstance, inferInstance, ⟨⟨f, hf, hk, T, hT⟩⟩⟩

/-- The published natural-coordinate input supplies the even-field generating pair. -/
theorem linear_pair_of_input (hl : NaturalIndices.LinearCoordinatesInput (G := G) K)
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n) {x : G}
    (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L) :
    ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
      ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  obtain ⟨F, _, _, hF, c, hi⟩ := hl A H R L h hb n hL
  obtain ⟨F', _, _, _, ⟨m⟩⟩ := linear_model_of_coordinates h hb hL hF c hi
  exact rankOne_pair_of_model h m hspan

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
end
