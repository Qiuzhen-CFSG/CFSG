module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Twists
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Sylow control of the chosen natural module type

Conjugation by a common normalizer of L and V induces an intertwiner on the
literal chosen central quotient. Model intertwiners transport through its
original full L/O₂(L) marking. The automorphisms admitting such intertwiners
form a subgroup. If its index is at most two, the original Sylow subgroup's
seed invariance forces the entire normalizer to preserve this binary type.
The Sp₄ and SL₃ consumers supply the index bound from their actual
parabolic-class action and linear-field-graph factorization, respectively.

Source: Aschbacher--Smith, 11.0.2 and 11.0.3(2), printed pp.759--760.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

omit [Finite G] in
/-- A common normalizer induces an actual intertwiner on V/C_V(L), using
the original quotient projection and without a splitting assumption. -/
theorem chosen_central_twist_of_normalizes (g : normalizer (L : Set G))
    (hgV : (g : G) ∈ normalizer (V : Set G)) :
    ∃ e : D.chosenCentralQuotient ≃ₗ[ZMod 2] D.chosenCentralQuotient,
      ∀ l v, e (D.chosenCentralAction l v) =
        D.chosenCentralAction (L.normalizerMonoidHom g l) (e v) := by
  let := D.elementary
  let P := normalizer (L : Set G) ⊓ normalizer (V : Set G)
  let C := centralizer (L : Set G)
  let hPV : P ≤ normalizer (V : Set G) := inf_le_right
  let hPC : P ≤ normalizer (C : Set G) :=
    inf_le_left.trans (normalizer_le_normalizer_centralizer L)
  obtain ⟨β, hβ⟩ := Subgroup.exists_quotient_conjugation_action
    P V C hPV hPC (inferInstance : (C.subgroupOf V).Normal)
  let E : D.chosenCentralQuotient ≃ₗ[ZMod 2] Additive (V ⧸ C.subgroupOf V) :=
    LinearEquiv.ofBijective (seedQuotientMap D V le_rfl)
      ⟨seedQuotientMap_injective D V le_rfl,
        seedQuotientMap_surjective D V le_rfl le_rfl⟩
  let g' : P := ⟨g, g.property, hgV⟩
  let b : Additive (V ⧸ C.subgroupOf V) ≃ₗ[ZMod 2] Additive (V ⧸ C.subgroupOf V) :=
    LinearEquiv.ofBijective ((β g').toMonoidHom.toAdditive.toZModLinearMap 2) (β g').bijective
  let e := E.trans (b.trans E.symm)
  have he (v : V) : e (D.toCentralQuotient v).toAdd =
      (D.toCentralQuotient (V.normalizerMonoidHom ⟨g, hgV⟩ v)).toAdd := by
    apply E.injective
    change E (E.symm (b (E (D.toCentralQuotient v).toAdd))) = _
    rw [E.apply_symm_apply]
    change b (seedQuotientMap D V le_rfl (D.toCentralQuotient v).toAdd) =
      seedQuotientMap D V le_rfl (D.toCentralQuotient _).toAdd
    rw [seedQuotientMap_projection, seedQuotientMap_projection]
    change Additive.ofMul (β g' (QuotientGroup.mk' (C.subgroupOf V) v)) = _
    rw [hβ]
    rfl
  refine ⟨e, ?_⟩
  intro l v
  obtain ⟨w, hw⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd v)
  have hw' : (D.toCentralQuotient w).toAdd = v := congrArg Multiplicative.toAdd hw
  rw [← hw', ← centralProjection_conjugation, he, he, ← centralProjection_conjugation]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
  change (g : G) * ((l : G) * (w : G) * (l : G)⁻¹) * (g : G)⁻¹ =
    ((g : G) * (l : G) * (g : G)⁻¹) * ((g : G) * (w : G) * (g : G)⁻¹) *
      ((g : G) * (l : G) * (g : G)⁻¹)⁻¹
  group

section Marking
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A W}
    (m : ActionEquiv D.centralQuotientAction ρ)

/-- The original normalizer action, transported through the full natural marking. -/
def markedNormalizerAut : normalizer (L : Set G) →* MulAut A :=
  ((MulAut.congr m.groupEquiv).toMonoidHom.comp (quotientAut (pCore 2 L))).comp
    L.normalizerMonoidHom

/-- A model intertwiner transports through the unchanged central quotient. -/
theorem chosen_central_twist_of_marked (g : normalizer (L : Set G))
    (b : W ≃ₗ[ZMod 2] W)
    (hb : ∀ a v, b (ρ a v) = ρ (markedNormalizerAut D m g a) (b v)) :
    ∃ e : D.chosenCentralQuotient ≃ₗ[ZMod 2] D.chosenCentralQuotient,
      ∀ l v, e (D.chosenCentralAction l v) =
        D.chosenCentralAction (L.normalizerMonoidHom g l) (e v) := by
  let e := m.linearEquiv.trans (b.trans m.linearEquiv.symm)
  refine ⟨e, ?_⟩
  intro l v
  apply m.linearEquiv.injective
  change m.linearEquiv (m.linearEquiv.symm (b (m.linearEquiv (D.chosenCentralAction l v)))) = _
  rw [m.linearEquiv.apply_symm_apply]
  change b (m.linearEquiv (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l) v)) = _
  rw [m.intertwines, hb]
  change _ = m.linearEquiv (D.centralQuotientAction
    (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom g l)) (e v))
  rw [m.intertwines]
  have he : m.linearEquiv (e v) = b (m.linearEquiv v) := m.linearEquiv.apply_symm_apply _
  rw [he]
  congr 2
  change m.groupEquiv (quotientAut (pCore 2 L) (L.normalizerMonoidHom g)
    (m.groupEquiv.symm (m.groupEquiv _))) = _
  rw [m.groupEquiv.symm_apply_apply, quotientAut_apply_mk]
end Marking

section Types
variable {H A W : Type*} [Group H] [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (α : H →* MulAut A)

private def twistStabilizer : Subgroup H where
  carrier := {g | ∃ e : W ≃ₗ[ZMod 2] W, ∀ a v, e (ρ a v) = ρ (α g a) (e v)}
  one_mem' := ⟨LinearEquiv.refl _ _, fun a v => by simp⟩
  mul_mem' := by
    rintro g h ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨f.trans e, ?_⟩
    intro a v
    change e (f (ρ a v)) = ρ (α (g*h) a) (e (f v))
    rw [hf, he, map_mul]
    rfl
  inv_mem' := by
    rintro g ⟨e, he⟩
    refine ⟨e.symm, ?_⟩
    intro a v
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
    simp

private theorem twistStabilizer_eq_top_of_sylow [Finite H]
    {B : Type*} [Group B] [Finite B] (π : H →* B) (hc : Nat.card B ∣ 2)
    (P : Sylow 2 H) (hP : (P : Subgroup H) ≤ twistStabilizer ρ α)
    (hk : π.ker ≤ twistStabilizer ρ α) : twistStabilizer ρ α = ⊤ := by
  have hd : (twistStabilizer ρ α).index ∣ 2 :=
    (index_dvd_of_le hk).trans (by
      rw [index_ker]
      exact (card_subgroup_dvd_card π.range).trans hc)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · exact index_eq_one.mp h
  · have hdiv := index_dvd_of_le hP
    rw [h] at hdiv
    exact False.elim (P.not_dvd_index hdiv)
end Types

/-- The seed's type is invariant under the whole normalizer when a quotient
of order at most two measures the only possible changes of type. The actual
Sylow subgroup stabilizes V, so it lies in the type stabilizer. Its odd index
forces that stabilizer to be the whole normalizer. -/
theorem fullModule_homogeneous_of_two_quotient
    {B : Type*} [Group B] [Finite B]
    (π : normalizer (L : Set G) →* B) (hc : Nat.card B ∣ 2)
    (hk : ∀ g : normalizer (L : Set G), π g = 1 →
      ∃ e : D.chosenCentralQuotient ≃ₗ[ZMod 2] D.chosenCentralQuotient,
        ∀ l v, e (D.chosenCentralAction l v) =
          D.chosenCentralAction (L.normalizerMonoidHom g l) (e v)) :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      (∃ I : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible I.toRepresentation ∧
          Representation.BinaryOffender.Homogeneous.homogeneousPart I ⊤ = ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  apply fullModule_homogeneous_of_normalizer_twists D S
  have htop := twistStabilizer_eq_top_of_sylow D.chosenCentralAction
    L.normalizerMonoidHom π hc (T.subtype D.sylow_normalizes_component)
    (fun g hg => chosen_central_twist_of_normalizes D g (S.sylow_normalizes hg))
    (fun g hg => hk g hg)
  intro g
  exact htop.ge (show g ∈ (⊤ : Subgroup (normalizer (L : Set G))) from trivial)

section TwoTypes
private theorem index_le_two_of_two_types {A : Type*} [Group A] [Finite A]
    (K : Subgroup A) (b : A) (ht : ∀ a : A, a ∈ K ∨ a * b⁻¹ ∈ K) : K.index ≤ 2 := by
  let f : Bool → A ⧸ K := fun t => QuotientGroup.mk (if t then b⁻¹ else 1)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    rcases ht a⁻¹ with h | h
    · refine ⟨false, ?_⟩
      apply QuotientGroup.eq.mpr
      change (1 : A)⁻¹ * a ∈ K
      simpa using K.inv_mem h
    · refine ⟨true, ?_⟩
      apply QuotientGroup.eq.mpr
      change (b⁻¹)⁻¹ * a ∈ K
      simpa using K.inv_mem h
  simpa [Subgroup.index] using Nat.card_le_card_of_surjective f hf

include S in
/-- If every model twist is natural or differs from a natural twist by one
fixed automorphism, the chosen Sylow-invariant seed has invariant binary type
under its entire normalizer. The SL₃ application supplies the two types from
the proved full linear-field-graph factorization, including its cubic center. -/
theorem normalizer_twists_of_two_model_types
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A W}
    (m : ActionEquiv D.centralQuotientAction ρ) (b : MulAut A)
    (ht : ∀ a : MulAut A,
      (∃ e : W ≃ₗ[ZMod 2] W, ∀ l v, e (ρ l v) = ρ (a l) (e v)) ∨
      (∃ e : W ≃ₗ[ZMod 2] W, ∀ l v, e (ρ l v) = ρ ((a * b⁻¹) l) (e v))) :
    ∀ g : normalizer (L : Set G),
      ∃ e : D.chosenCentralQuotient ≃ₗ[ZMod 2] D.chosenCentralQuotient,
        ∀ l v, e (D.chosenCentralAction l v) =
          D.chosenCentralAction (L.normalizerMonoidHom g l) (e v) := by
  let K₀ := twistStabilizer ρ (MonoidHom.id (MulAut A))
  have hc : K₀.index ≤ 2 := index_le_two_of_two_types K₀ b ht
  let K := K₀.comap (markedNormalizerAut D m)
  have hK : K.index ≤ 2 := by
    rw [show K.index = K₀.relIndex (markedNormalizerAut D m).range from
      index_comap K₀ (markedNormalizerAut D m)]
    apply le_trans (relIndex_le_of_le_right (show (markedNormalizerAut D m).range ≤ ⊤ from le_top) ?_) ?_
    · simpa only [relIndex_top_right] using (index_ne_zero_of_finite (H := K₀))
    · simpa only [relIndex_top_right] using hc
  let R := twistStabilizer D.chosenCentralAction L.normalizerMonoidHom
  have hKR : K ≤ R := by
    rintro g ⟨e, he⟩
    exact chosen_central_twist_of_marked D m g e he
  have hR : R.index ≤ 2 := (index_antitone hKR).trans hK
  let P := T.subtype D.sylow_normalizes_component
  have hPR : (P : Subgroup (normalizer (L : Set G))) ≤ R :=
    fun g hg => chosen_central_twist_of_normalizes D g (S.sylow_normalizes hg)
  have hn : ¬ 2 ∣ R.index := fun h => P.not_dvd_index (h.trans (index_dvd_of_le hPR))
  have hpos : 0 < R.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have htop : R = ⊤ := index_eq_one.mp (by omega)
  intro g
  exact htop.ge trivial
end TwoTypes

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
