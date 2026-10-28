module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Basic

/-!
# Marked second-centralizer models for the J₂ source argument

The model is an actual equivalence of the full centralizer with E₄ × A₅.
Its marking records which involutions fuse to z in the ambient group.
The intrinsic two-core is proved to be precisely the embedded E₄ factor.
The source recognition and ambient fusion assertions remain explicit inputs.

`SelectedGeometry` specifies the remaining geometric output of Aschbacher,
*Sporadic Groups* (1994), 47.1(1), pp.259–260. It retains the intrinsic layer,
the actual normalizer and both factor inclusions. Its z and X markings concern
one selected representative, never every conjugate representative.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry

abbrev E4 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev A5 := alternatingGroup (Fin 5)
abbrev A4 := alternatingGroup (Fin 4)

variable {G : Type*} [Group G] [Finite G]

/-- O₂(C_G(t)), embedded using the literal centralizer subtype. -/
def rootCore (t : G) : Subgroup G := (involutionCentralizer t).pCoreIn 2

/-- E(C_G(t)), embedded using the same literal centralizer subtype. -/
def rootComponent (t : G) : Subgroup G :=
  (componentLayer (involutionCentralizer t)).map (involutionCentralizer t).subtype

/-- A model and its ambient fusion marking, to be constructed by source recognition. -/
structure SecondCentralizer (D : Seed G) (t : G) where
  equiv : involutionCentralizer t ≃* (E4 × A5)
  fusion : ∀ u : involutionCentralizer t, orderOf u = 2 →
    (IsConj D.z (u : G) ↔ (equiv u).1 = 1)

theorem card_E4 : Nat.card E4 = 4 := by
  rw [Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card]

theorem card_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num

private theorem core_E4 : pCore 2 E4 = ⊤ := by
  have hp : IsPGroup 2 E4 := IsPGroup.of_card (n := 2) card_E4
  exact top_le_iff.mp (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)

private theorem core_A5 : pCore 2 A5 = ⊥ := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  rcases (pCore_normal (p := 2) (G := A5)).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 A5 := by
      have hp := pCore_isPGroup (p := 2) (G := A5)
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    rw [card_A5] at hn
    have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this

namespace SecondCentralizer
variable {D : Seed G} {t : G} (C : SecondCentralizer D t)

/-- The model map into the original group; its range is the full centralizer. -/
def embedding : (E4 × A5) →* G :=
  (involutionCentralizer t).subtype.comp C.equiv.symm.toMonoidHom

theorem embedding_injective : Function.Injective C.embedding :=
  (involutionCentralizer t).subtype_injective.comp C.equiv.symm.injective

def fourFactor : Subgroup G :=
  ((⊤ : Subgroup E4).prod (⊥ : Subgroup A5)).map C.embedding

def fiveFactor : Subgroup G :=
  ((⊥ : Subgroup E4).prod (⊤ : Subgroup A5)).map C.embedding

include C in
theorem centralizer_card : Nat.card (involutionCentralizer t) = 240 := by
  rw [Nat.card_congr C.equiv.toEquiv, Nat.card_prod, card_E4, card_A5]

/-- The product model identifies the intrinsic core, not merely some four-subgroup. -/
theorem rootCore_eq_fourFactor : rootCore t = C.fourFactor := by
  have he := pCore_map_iso 2 C.equiv.symm
  rw [pCore_prod, core_E4, core_A5] at he
  rw [rootCore, pCoreIn, ← he, map_map]
  rfl

include C in
theorem rootCore_card : Nat.card (rootCore t) = 4 := by
  rw [C.rootCore_eq_fourFactor, fourFactor,
    card_map_of_injective C.embedding_injective,
    Nat.card_congr (prodEquiv (⊤ : Subgroup E4) (⊥ : Subgroup A5)).toEquiv,
    Nat.card_prod]
  simp

/-- Recognition of the embedded core in the centralizer's coordinates. -/
theorem mem_rootCore_iff (u : involutionCentralizer t) :
    (u : G) ∈ rootCore t ↔ (C.equiv u).2 = 1 := by
  rw [C.rootCore_eq_fourFactor]
  change (u : G) ∈ ((⊤ : Subgroup E4).prod (⊥ : Subgroup A5)).map C.embedding ↔ _
  constructor
  · rintro ⟨a, ha, he⟩
    have hsub : C.equiv.symm a = u := Subtype.ext he
    have hau : a = C.equiv u := by
      simpa only [C.equiv.apply_symm_apply] using congrArg C.equiv hsub
    have ha2 : a.2 = 1 := ha.2
    exact hau ▸ ha2
  · intro hu
    exact ⟨C.equiv u, ⟨mem_top _, hu⟩, by simp [embedding]⟩

end SecondCentralizer

/-- The still-to-be-constructed geometric input, with every group and factor literal.
The source pair counts and the TI property are not fields of this record. -/
structure SelectedGeometry (D : Seed G) where
  t : G
  other : OtherInvolution D t
  model : SecondCentralizer D t
  component_eq : rootComponent t = model.fiveFactor
  z_mem_component : D.z ∈ rootComponent t
  X_centralizes_component : D.X ≤ centralizer (rootComponent t : Set G)
  X_sylow : ∃ P : Sylow 3 (centralizer (rootComponent t : Set G)),
    (P : Subgroup (centralizer (rootComponent t : Set G))).map
      (centralizer (rootComponent t : Set G)).subtype = D.X
  normalizerEquiv : normalizer (rootCore t : Set G) ≃* (A4 × A5)
  normalizer_component :
    ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map
      ((normalizer (rootCore t : Set G)).subtype.comp normalizerEquiv.symm.toMonoidHom) =
      rootComponent t
  normalizer_core :
    ((pCore 2 A4).prod (⊥ : Subgroup A5)).map
      ((normalizer (rootCore t : Set G)).subtype.comp normalizerEquiv.symm.toMonoidHom) =
      rootCore t

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
