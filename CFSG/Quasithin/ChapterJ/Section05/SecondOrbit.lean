module

public import CFSG.Quasithin.ChapterJ.Section05.DerivedNormalizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Normalizer

/-!
# The actual second orbit in J.5.4

The source Sylow-five normalizer supplies a point outside the first two
orbits. Its stabilizer contains a group of order25 and has order at least
15600. The derived-normalizer argument excludes the index-two Tits case;
the native finite coverage then gives equality. Orbit–stabilizer yields
2304 points, so this orbit exhausts the source remainder.

The stabilizer is transported to the normalizer of the literal embedded
ATLAS max4 candidate. Its identification as PSL₂(25)⁺ remains an independent
model theorem. The only earlier input to the final original-choice consumer
is the marked J.4.7 recognition of the same subgroup F.
Source: Aschbacher–Smith J.5.4, printed pp.445–446.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

/-- The actual intersection stabilizer excludes the index-two Tits overgroup. -/
theorem source_stabilizer_not_contains_derived (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) {g : G} (hg : g ∉ F) :
    ¬ commutator (ReeF4.Model 0) ≤
      (stabilizer F (g • basePoint F)).map e.toMonoidHom := by
  intro hD
  apply source_derived_not_le_conjugate d B5 F h5 hB e hg
  have hs : (stabilizer F (g • basePoint F)).map F.subtype ≤
      F.map (MulAut.conj g).toMonoidHom := by
    rintro x ⟨a,ha,rfl⟩
    change (a : G) ∈ stabilizer G (g • basePoint F) at ha
    rwa [stabilizer_smul_eq_stabilizer_map_conj,stabilizer_quotient] at ha
  rw [← F.map_subtype_commutator]
  refine (map_mono ?_).trans hs
  intro a ha
  have he := mem_map_of_mem e.toMonoidHom ha
  rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,
    ← _root_.commutator_def] at he
  obtain ⟨b,hb,hba⟩ := hD he
  have hba' : b = a := e.injective hba
  subst b
  exact hb

/-- Native finite coverage gives the exact actual second-stabilizer order. -/
theorem source_second_stabilizer_card (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    Nat.card (stabilizer F (g • basePoint F)) = 15600 := by
  have h25 := card_dvd_of_le hP
  rw [recognized_sylow_five_card F e P] at h25
  have hc := FiveOvergroups.card_le ((stabilizer F (g • basePoint F)).map e.toMonoidHom)
    (source_stabilizer_not_contains_derived d B5 F h5 hB e hg)
    (by rwa [card_map_of_injective e.injective])
  rw [card_map_of_injective e.injective] at hc
  exact Nat.le_antisymm hc hlarge

/-- The source stabilizer is conjugate to the fixed native full-Ree normalizer. -/
theorem source_second_stabilizer_marking (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    ∃ a : Tits.Atlas1600Group,
      ((stabilizer F (g • basePoint F)).map e.toMonoidHom).map
        (MulAut.conj (atlasEmbedding a)).toMonoidHom = FiveOvergroups.candidateNormalizer := by
  have h25 := card_dvd_of_le hP
  rw [recognized_sylow_five_card F e P] at h25
  obtain ⟨_,ha⟩ := FiveOvergroups.large_conjugate_normalizer
    ((stabilizer F (g • basePoint F)).map e.toMonoidHom)
    (source_stabilizer_not_contains_derived d B5 F h5 hB e hg)
    (by rwa [card_map_of_injective e.injective])
    (by rwa [card_map_of_injective e.injective])
  exact ha

/-- Literal subgroup transport to the normalizer needing the remaining PSL₂(25) identification. -/
theorem source_second_stabilizer_equiv (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    Nonempty (stabilizer F (g • basePoint F) ≃* FiveOvergroups.candidateNormalizer) := by
  obtain ⟨a,ha⟩ := source_second_stabilizer_marking d B5 F h5 hB e P hg hP hlarge
  exact ⟨(e.subgroupMap _).trans
    (((MulAut.conj (atlasEmbedding a)).subgroupMap _).trans (MulEquiv.subgroupCongr ha))⟩

/-- The literal second coset orbit has source length2304. -/
theorem source_second_orbit_card (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    Nat.card (orbit F (g • basePoint F)) = 2304 := by
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup F (g • basePoint F))
  rw [Nat.card_prod,source_second_stabilizer_card d B5 F h5 hB e P hg hP hlarge,
    (Nat.card_congr e.toEquiv).trans group_card] at hc
  omega

omit [Finite G] in
private theorem orbit_subset_remainder {F : Subgroup G} {δ γ : Cosets F}
    (hγ : γ ∈ (({basePoint F} : Set (Cosets F)) ∪ orbit F δ)ᶜ) :
    orbit F γ ⊆ (({basePoint F} : Set (Cosets F)) ∪ orbit F δ)ᶜ := by
  have hne : γ ≠ basePoint F := fun he => hγ (Or.inl he)
  have hn : γ ∉ orbit F δ := fun ho => hγ (Or.inr ho)
  rintro x ⟨a,rfl⟩ (hb | ho)
  · have ha : (a : G) • basePoint F = basePoint F :=
      (show (a : G) ∈ stabilizer G (basePoint F) from
        (stabilizer_quotient F).symm ▸ a.property)
    exact hne (smul_left_cancel a ((show a • γ = basePoint F from hb).trans ha.symm))
  · apply hn
    simpa only [inv_smul_smul] using mem_orbit_of_mem_orbit a⁻¹ ho

/-- The numerical and orbit assertions of J.5.4–5 on the original coset action. -/
theorem SourceChoice.source_second_orbit {d : LocalSetup G} (p : Plane d)
    (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5, s.v * a * s.v⁻¹ = a⁻¹)
    (X : Sylow 3 p.parabolic) (e : p.F B5 X ≃* ReeF4.Model 0)
    (hmark : ((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom = first)
    (P : Sylow 5 (p.F B5 X)) :
    ∃ q g : G, q ∈ d.toTypeRuSetup.Q ∧ q ∉ p.F B5 X ∧
      g ∈ normalizer (((P : Subgroup (p.F B5 X)).map (p.F B5 X).subtype) : Set G) ∧
      g ∉ p.F B5 X ∧ Nat.card (Cosets (p.F B5 X)) = 4060 ∧
      Nat.card (orbit (p.F B5 X) (q • basePoint (p.F B5 X))) = 1755 ∧
      Nat.card (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X))) = 15600 ∧
      Nat.card (orbit (p.F B5 X) (g • basePoint (p.F B5 X))) = 2304 ∧
      orbit (p.F B5 X) (g • basePoint (p.F B5 X)) =
        (({basePoint (p.F B5 X)} : Set (Cosets (p.F B5 X))) ∪
          orbit (p.F B5 X) (q • basePoint (p.F B5 X)))ᶜ ∧
      Nonempty (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X)) ≃*
        FiveOvergroups.candidateNormalizer) := by
  obtain ⟨q,hq,hqF,hcos,hstab,horbit,_,hrem⟩ :=
    SourceChoice.source_J_5_2_3 p s B5 hi X e hmark
  have hδ : Nat.card (stabilizer (p.F B5 X) (q • basePoint (p.F B5 X))) = 20480 := by
    rw [hstab,Nat.card_congr (subgroupOfEquivOfLe
      (show p.F₁ B5 ≤ p.F B5 X from le_sup_left)).toEquiv,s.card_F₁ p B5 hi]
  obtain ⟨g,hg,hgF,hP,hr,hlarge⟩ :=
    source_second_orbit_seed d (p.F B5 X) e P _ hδ hrem
  have h5 : Q₅ d B5 ≤ p.F B5 X := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hB : B5Image B5 ≤ p.F B5 X := le_sup_right.trans le_sup_left
  have hcard := source_second_stabilizer_card d B5 (p.F B5 X) h5 hB e P hgF hP hlarge
  have ho := source_second_orbit_card d B5 (p.F B5 X) h5 hB e P hgF hP hlarge
  refine ⟨q,g,hq,hqF,hg,hgF,hcos,horbit,hcard,ho,?_,
    source_second_stabilizer_equiv d B5 (p.F B5 X) h5 hB e P hgF hP hlarge⟩
  exact Set.eq_of_subset_of_ncard_le (orbit_subset_remainder hr) (by
    change _ ≤ Nat.card (orbit (p.F B5 X) (g • basePoint (p.F B5 X)))
    rw [hrem,ho])

end CFSG.Quasithin.ChapterJ.Section05
