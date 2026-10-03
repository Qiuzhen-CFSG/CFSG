module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.LaterDefs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# The elementary pair in a Sylow subgroup of C₂ × S₄

A Sylow two-subgroup `S` of a finite subgroup `P ≃ C₂ × S₄` is isomorphic
to `C₂ × DihedralGroup 4`. Given the elementary-abelianness and order eight
of `A = twoCoreIn P`, the theorem constructs the other maximal elementary
subgroup `B`: they generate `S`, intersect in order four, and contain between
them every elementary abelian subgroup of `S`, including smaller ones.
The image of `Z(P)` lies in their intersection. The two core hypotheses are
explicit inputs; this module does not recompute the model's two-core.

The proof embeds the square's dihedral symmetries into permutations of `Fin 4`.
Its product with `C₂` has order sixteen, hence is Sylow in the order-forty-eight
model; Sylow conjugacy transports this model to `S`. Kernel-checked finite
calculations give the two elementary subgroups in `C₂ × D₈`, their orders,
intersection, generation, and the restriction on commuting involutions.
That restriction proves the covering property for arbitrary elementary
subgroups. Transport and equal cardinalities then identify `A` with one member.
Finally, the model center has exponent two, so its normality puts it inside
the two-core and hence inside `S`; centrality in `S` puts it in both members.

This supplies the concrete geometry behind the final case (II) paragraph of
Stellmacher's Section 11, `refs/latex/stellmacher-n-group.tex`, lines 2089–2095,
for the conditional normalizer and Thompson calculation in
`Stellmacher.SectionEleven.C2S4NormalizerThompson`.
-/

namespace Stellmacher.SectionEleven

open scoped IsMulCommutative

private abbrev Model := Later.C2 × DihedralGroup 4

private def leftPair : Subgroup Model where
  carrier := {element | element.2 = .r 0 ∨ element.2 = .r 2 ∨
    element.2 = .sr 0 ∨ element.2 = .sr 2}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

private def rightPair : Subgroup Model where
  carrier := {element | element.2 = .r 0 ∨ element.2 = .r 2 ∨
    element.2 = .sr 1 ∨ element.2 = .sr 3}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

private instance : DecidablePred (· ∈ leftPair) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
private instance : DecidablePred (· ∈ rightPair) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
private instance : DecidablePred (· ∈ leftPair ⊓ rightPair) := fun element =>
  inferInstanceAs (Decidable (element ∈ leftPair ∧ element ∈ rightPair))

private instance : IsElementaryAbelian 2 leftPair where
  is_comm.comm := by decide
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide)

private instance : IsElementaryAbelian 2 rightPair where
  is_comm.comm := by decide
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide)

private theorem pair_cards : Nat.card leftPair = 8 ∧ Nat.card rightPair = 8 ∧
    Nat.card (leftPair ⊓ rightPair : Subgroup Model) = 4 := by
  simp only [Nat.card_eq_fintype_card]
  decide

private theorem pair_ne : leftPair ≠ rightPair := by
  intro heq
  have hmem : (1, DihedralGroup.sr 0) ∈ leftPair := by decide
  rw [heq] at hmem
  exact (by decide : (1, DihedralGroup.sr 0) ∉ rightPair) hmem

private theorem pair_join : leftPair ⊔ rightPair = ⊤ := by
  have hfactor : ∀ element : Model, ∃ left ∈ leftPair, ∃ right ∈ rightPair,
      left * right = element := by decide
  apply top_unique
  intro element _
  obtain ⟨left, hleft, right, hright, rfl⟩ := hfactor element
  exact (leftPair ⊔ rightPair).mul_mem
    ((show leftPair ≤ leftPair ⊔ rightPair from le_sup_left) hleft)
    ((show rightPair ≤ leftPair ⊔ rightPair from le_sup_right) hright)

set_option synthInstance.maxSize 256 in
private theorem pair_commuting : ∀ element other : Model,
      element ^ 2 = 1 → other ^ 2 = 1 → element * other = other * element →
      element ∉ leftPair → other ∈ rightPair := by decide

private theorem pair_cover (E : Subgroup Model) (hE : IsElementaryAbelian 2 E) :
    E ≤ leftPair ∨ E ≤ rightPair := by
  let _ := hE
  classical
  by_cases hleft : E ≤ leftPair
  · exact Or.inl hleft
  right
  obtain ⟨element, hmem, hout⟩ := SetLike.not_le_iff_exists.mp hleft
  intro other hother
  apply pair_commuting element other
    (elemPow_eq_one_of_isElementaryAbelian element hmem)
    (elemPow_eq_one_of_isElementaryAbelian other hother) _ hout
  exact congrArg Subtype.val (mul_comm
    (⟨element, hmem⟩ : E) ⟨other, hother⟩)

private theorem pair_center : Subgroup.center Model ≤ leftPair ⊓ rightPair := by
  have hfinite : ∀ element : Model, (∀ other, other * element = element * other) →
      element ∈ leftPair ∧ element ∈ rightPair := by decide
  intro element hmem
  exact hfinite element (Subgroup.mem_center_iff.mp hmem)

private def dihedralPermutation : DihedralGroup 4 → Later.S4
  | .r index => finRotate 4 ^ index.val
  | .sr index => Equiv.swap 1 3 * finRotate 4 ^ index.val

set_option maxRecDepth 10000 in
private def dihedralEmbedding : DihedralGroup 4 →* Later.S4 where
  toFun := dihedralPermutation
  map_one' := by decide
  map_mul' := by decide

set_option maxRecDepth 10000 in
private theorem dihedralEmbedding_injective : Function.Injective dihedralEmbedding := by
  decide

private def modelEmbedding : Model →* (Later.C2 × Later.S4) :=
  (MonoidHom.id Later.C2).prodMap dihedralEmbedding

private theorem modelEmbedding_injective : Function.Injective modelEmbedding := by
  intro left right heq
  exact Prod.ext (by simpa [modelEmbedding] using congrArg Prod.fst heq)
    (dihedralEmbedding_injective (by simpa [modelEmbedding] using congrArg Prod.snd heq))

private theorem sylow_model
    {H : Type*} [Group H] [Finite H] (S P : Subgroup H)
    (hSylow : SectionsFiveToSeven.IsSylowTwoIn S P)
    (hModel : Later.IsModel P (Later.C2 × Later.S4)) : Nonempty (S ≃* Model) := by
  obtain ⟨_, T, hT⟩ := hSylow
  obtain ⟨model⟩ := hModel
  let modelRange := MonoidHom.ofInjective modelEmbedding_injective
  have hcard : Nat.card modelEmbedding.range = 16 := by
    rw [← Nat.card_congr modelRange.toEquiv, Nat.card_prod]
    norm_num [Later.C2, DihedralGroup.card]
  have hfull : Nat.card (Later.C2 × Later.S4) = 48 := by
    norm_num [Later.C2, Later.S4, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_perm]
  let concrete : Sylow 2 (Later.C2 × Later.S4) := Sylow.ofCard modelEmbedding.range (by
    rw [hcard, hfull]
    rw [show 48 = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization])
  let image := T.mapSurjective (f := model.toMonoidHom) model.surjective
  let toImage : T ≃* image :=
    (T : Subgroup P).equivMapOfInjective model.toMonoidHom model.injective
  exact ⟨(MulEquiv.subgroupCongr hT.symm).trans
    (((T : Subgroup P).equivMapOfInjective P.subtype P.subtype_injective).symm.trans
      (toImage.trans ((image.equiv concrete).trans modelRange.symm)))⟩

private theorem transported_pair
    {H : Type*} [Group H] (S : Subgroup H) (model : S ≃* Model) :
    ∃ U V : Subgroup H, U ≤ S ∧ V ≤ S ∧ U ≠ V ∧
      IsElementaryAbelian 2 U ∧ IsElementaryAbelian 2 V ∧
      Nat.card U = 8 ∧ Nat.card V = 8 ∧ U ⊔ V = S ∧
      Nat.card (U ⊓ V : Subgroup H) = 4 ∧
      (∀ E : Subgroup H, E ≤ S → IsElementaryAbelian 2 E → E ≤ U ∨ E ≤ V) ∧
      (Subgroup.center S).map S.subtype ≤ U ⊓ V := by
  let embedding : Model →* H := S.subtype.comp model.symm.toMonoidHom
  have hinj : Function.Injective embedding := S.subtype_injective.comp model.symm.injective
  have hrange : embedding.range = S := by
    ext element
    constructor
    · rintro ⟨preimage, rfl⟩
      exact (model.symm preimage).property
    · intro hmem
      exact ⟨model ⟨element, hmem⟩, by simp [embedding]⟩
  let U := leftPair.map embedding
  let V := rightPair.map embedding
  refine ⟨U, V, ?_, ?_, ?_, IsElementaryAbelian.map embedding,
    IsElementaryAbelian.map embedding, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_range embedding leftPair).trans_eq hrange
  · exact (Subgroup.map_le_range embedding rightPair).trans_eq hrange
  · exact fun heq => pair_ne (Subgroup.map_injective hinj heq)
  · exact (Subgroup.card_map_of_injective hinj).trans pair_cards.1
  · exact (Subgroup.card_map_of_injective hinj).trans pair_cards.2.1
  · change leftPair.map embedding ⊔ rightPair.map embedding = S
    rw [← Subgroup.map_sup, pair_join, ← MonoidHom.range_eq_map, hrange]
  · change Nat.card (leftPair.map embedding ⊓ rightPair.map embedding : Subgroup H) = 4
    rw [← Subgroup.map_inf _ _ embedding hinj, Subgroup.card_map_of_injective hinj]
    exact pair_cards.2.2
  · intro E hES hE
    let _ := hE
    have hpre : IsElementaryAbelian 2 (E.comap embedding) := by
      refine { toIsMulCommutative := E.comap_injective_isMulCommutative hinj
               exponent_dvd_p := ?_ }
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro element
      apply Subtype.ext
      apply hinj
      change embedding ((element : Model) ^ 2) = embedding 1
      simpa only [map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (embedding element) element.property
    have hmap : (E.comap embedding).map embedding = E :=
      Subgroup.map_comap_eq_self (hES.trans_eq hrange.symm)
    rcases pair_cover (E.comap embedding) hpre with hleft | hright
    · exact Or.inl (hmap.symm ▸ Subgroup.map_mono hleft)
    · exact Or.inr (hmap.symm ▸ Subgroup.map_mono hright)
  · rintro element ⟨central, hcentral, rfl⟩
    have hmodel : model central ∈ Subgroup.center Model := by
      apply Subgroup.mem_center_iff.mpr
      intro other
      obtain ⟨other, rfl⟩ := model.surjective other
      simpa only [← map_mul] using congrArg model
        (Subgroup.mem_center_iff.mp hcentral other)
    have hp := pair_center hmodel
    have heq : embedding (model central) = (central : H) := by simp [embedding]
    exact ⟨⟨model central, hp.1, heq⟩, ⟨model central, hp.2, heq⟩⟩

set_option maxRecDepth 10000 in
private theorem model_center_square : ∀ element : Later.C2 × Later.S4,
    (∀ other, other * element = element * other) → element ^ 2 = 1 := by decide

private theorem center_le_core
    {H : Type*} [Group H] (P : Subgroup H)
    (hModel : Later.IsModel P (Later.C2 × Later.S4)) :
    (Subgroup.center P).map P.subtype ≤ SectionsFiveToSeven.twoCoreIn P := by
  obtain ⟨model⟩ := hModel
  have htwo : IsPGroup 2 (Subgroup.center P) := by
    intro element
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply model.injective
    change model ((element : P) ^ 2) = model 1
    rw [map_pow, map_one]
    apply model_center_square (model element)
    intro other
    obtain ⟨other, rfl⟩ := model.surjective other
    simpa only [← map_mul] using congrArg model
      (Subgroup.mem_center_iff.mp element.property other)
  exact Subgroup.map_mono (le_sSup ⟨inferInstance, htwo⟩)

/-- The two elementary subgroups in the case (II) Sylow model, with the
two-core chosen as one member and all elementary subgroups covered. -/
public theorem c2s4_sylow_elementary_pair
    {H : Type*} [Group H] [Finite H] (S P : Subgroup H)
    (hSylow : SectionsFiveToSeven.IsSylowTwoIn S P)
    (hModel : Later.IsModel P (Later.C2 × Later.S4))
    (hCore_elem : IsElementaryAbelian 2 (SectionsFiveToSeven.twoCoreIn P))
    (hCore_card : Nat.card (SectionsFiveToSeven.twoCoreIn P) = 8) :
    Nonempty (S ≃* (Later.C2 × DihedralGroup 4)) ∧
      ∃ B : Subgroup H,
        SectionsFiveToSeven.twoCoreIn P ≤ S ∧ B ≤ S ∧
        SectionsFiveToSeven.twoCoreIn P ≠ B ∧
        IsElementaryAbelian 2 B ∧ Nat.card B = 8 ∧
        SectionsFiveToSeven.twoCoreIn P ⊔ B = S ∧
        Nat.card (SectionsFiveToSeven.twoCoreIn P ⊓ B : Subgroup H) = 4 ∧
        (∀ E : Subgroup H, E ≤ S → IsElementaryAbelian 2 E →
          E ≤ SectionsFiveToSeven.twoCoreIn P ∨ E ≤ B) ∧
        (Subgroup.center P).map P.subtype ≤ SectionsFiveToSeven.twoCoreIn P ⊓ B := by
  obtain ⟨model⟩ := sylow_model S P hSylow hModel
  obtain ⟨U, V, hUS, hVS, hne, hUelem, hVelem, hUcard, hVcard, hjoin,
    hinter, hcover, hcenter⟩ := transported_pair S model
  have hCoreS : SectionsFiveToSeven.twoCoreIn P ≤ S := by
    obtain ⟨_, T, hT⟩ := hSylow
    exact (Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)).trans_eq hT
  have hcenterS : (Subgroup.center P).map P.subtype ≤
      (Subgroup.center S).map S.subtype := by
    rintro element ⟨central, hcentral, rfl⟩
    have hmem : (central : H) ∈ S :=
      hCoreS (center_le_core P hModel ⟨central, hcentral, rfl⟩)
    refine ⟨⟨central, hmem⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact congrArg (fun element : P => (element : H)) (Subgroup.mem_center_iff.mp hcentral
      ⟨other, hSylow.1 other.property⟩)
  refine ⟨⟨model⟩, ?_⟩
  rcases hcover _ hCoreS hCore_elem with hCoreU | hCoreV
  · have heq : SectionsFiveToSeven.twoCoreIn P = U :=
      Subgroup.eq_of_le_of_card_ge hCoreU (by omega)
    refine ⟨V, hCoreS, hVS, ?_⟩
    rw [heq]
    exact ⟨hne, hVelem, hVcard, hjoin, hinter, hcover, hcenterS.trans hcenter⟩
  · have heq : SectionsFiveToSeven.twoCoreIn P = V :=
      Subgroup.eq_of_le_of_card_ge hCoreV (by omega)
    refine ⟨U, hCoreS, hUS, ?_⟩
    rw [heq]
    exact ⟨hne.symm, hUelem, hUcard, by simpa only [sup_comm] using hjoin,
      by simpa only [inf_comm] using hinter,
      fun E hES hE => (hcover E hES hE).symm,
      by simpa only [inf_comm] using hcenterS.trans hcenter⟩

end Stellmacher.SectionEleven
