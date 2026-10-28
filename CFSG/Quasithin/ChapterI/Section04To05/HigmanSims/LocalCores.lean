module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Type
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The two characteristic-two local subgroups in type HS

The embedded quaternion product and cyclic factor give order 64 for the
first generalized Fitting subgroup. The homocyclic coordinates give the
same order for the second. Normality and the defining maximality of O₂
therefore identify both generalized Fitting subgroups with their two-cores.
Self-centralization then gives the characteristic-two conditions.

The literal quotient models yield |C_G(z)| = 7680 and |N_G(V)| = 10752;
in particular neither local subgroup contains the other. Normality of V
inside its own normalizer also places V in the second core. These are
consequences of HS1--HS2, without ambient simplicity or recognition.

Source: Aschbacher--Smith, I.4.8 and the preceding definition, printed
p.418. The recognition assembly and its remaining source construction
are owned by qt-i48-hs-recognition.
-/

public section
namespace CFSG.Quasithin.HigmanSims
open Subgroup Theory.GroupTheory

/-- The central product (Q₈ * Q₈) * C₄ has order 64. -/
theorem CoreShape.card {Q : Type*} [Group Q] [Finite Q] (h : CoreShape Q) :
    Nat.card Q = 64 := by
  obtain ⟨B, D, ⟨hB⟩, ⟨eD⟩, hi, hc, hs⟩ := h
  have hD : Nat.card D = 4 := by
    rw [Nat.card_congr eD.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hn : D ≤ normalizer (B : Set Q) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro d hd b hb
    exact hc b hb d hd
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn
  rw [hB.card, hD, hi, hs,
    Nat.card_congr (topEquiv : (⊤ : Subgroup Q) ≃* Q).toEquiv] at he
  omega

private theorem fitting_eq_twoCore_of_card {X : Type*} [Group X] [Finite X]
    (h : Nat.card (generalizedFitting X) = 64) : generalizedFitting X = pCore 2 X := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 6) h⟩
  · exact (pCore_le_fitting X 2).trans (fitting_le_generalizedFitting X)

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The involution-centralizer core has order 64. -/
theorem TypeAt.centralizer_core_card (h : TypeAt z V) : Nat.card (localCore z) = 64 :=
  h.centralizer_core.card

/-- HS1 makes the intrinsic generalized Fitting subgroup the two-core. -/
theorem TypeAt.centralizer_fitting (h : TypeAt z V) :
    localCore z = pCore 2 (involutionCentralizer z) :=
  fitting_eq_twoCore_of_card h.centralizer_core_card

/-- The full involution centralizer has order 64 · 120. -/
theorem TypeAt.centralizer_card (h : TypeAt z V) :
    Nat.card (involutionCentralizer z) = 7680 := by
  obtain ⟨e⟩ := h.centralizer_quotient
  have hquot : Nat.card (involutionCentralizer z ⧸ localCore z) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num
  have he := (localCore z).card_mul_index
  rw [h.centralizer_core_card, index_eq_card, hquot] at he
  omega

/-- The seed-normalizer core has order 4³. -/
theorem TypeAt.normalizer_core_card (h : TypeAt z V) :
    Nat.card (generalizedFitting (normalizer (V : Set G))) = 64 := by
  obtain ⟨e⟩ := h.normalizer_core
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- HS2 makes the intrinsic generalized Fitting subgroup the two-core. -/
theorem TypeAt.normalizer_fitting (h : TypeAt z V) :
    generalizedFitting (normalizer (V : Set G)) = pCore 2 (normalizer (V : Set G)) :=
  fitting_eq_twoCore_of_card h.normalizer_core_card

/-- The actual PSL₃(2) quotient has order 168, for every field marking. -/
theorem TypeAt.normalizer_quotient_card (h : TypeAt z V) :
    Nat.card (normalizer (V : Set G) ⧸ generalizedFitting (normalizer (V : Set G))) = 168 := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h.normalizer_quotient
  let := Fintype.ofFinite F
  let s : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  exact (Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 s)).toEquiv).trans
    Matrix.PSL3Two.card_PSL

/-- The full seed normalizer has order 64 · 168. -/
theorem TypeAt.normalizer_card (h : TypeAt z V) :
    Nat.card (normalizer (V : Set G)) = 10752 := by
  have he := (generalizedFitting (normalizer (V : Set G))).card_mul_index
  rw [h.normalizer_core_card, index_eq_card, h.normalizer_quotient_card] at he
  omega

/-- The involution centralizer has characteristic two. -/
theorem TypeAt.centralizer_twoCore_selfCentralizing (h : TypeAt z V) :
    centralizer (pCore 2 (involutionCentralizer z) : Set (involutionCentralizer z)) ≤
      pCore 2 (involutionCentralizer z) := by
  rw [← h.centralizer_fitting]
  exact centralizer_generalizedFitting_le _

/-- The seed normalizer has characteristic two. -/
theorem TypeAt.normalizer_twoCore_selfCentralizing (h : TypeAt z V) :
    centralizer (pCore 2 (normalizer (V : Set G)) : Set (normalizer (V : Set G))) ≤
      pCore 2 (normalizer (V : Set G)) := by
  rw [← h.normalizer_fitting]
  exact centralizer_generalizedFitting_le _

/-- Relative normality puts the elementary seed in the second actual core. -/
theorem TypeAt.seed_le_normalizer_core (h : TypeAt z V) :
    V ≤ (generalizedFitting (normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype := by
  let W := V.subgroupOf (normalizer (V : Set G))
  have hcard : Nat.card W = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv).trans h.seed_card
  have hW : W ≤ pCore 2 (normalizer (V : Set G)) :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 3) hcard⟩
  intro v hv
  exact ⟨⟨v, V.le_normalizer hv⟩, h.normalizer_fitting ▸ hW hv, rfl⟩

/-- The seed normalizer is not contained in the involution centralizer. -/
theorem TypeAt.normalizer_not_le_centralizer (h : TypeAt z V) :
    ¬ normalizer (V : Set G) ≤ involutionCentralizer z := by
  intro hle
  have hc := card_dvd_of_le hle
  rw [h.normalizer_card, h.centralizer_card] at hc
  norm_num at hc

/-- The involution centralizer is not contained in the seed normalizer. -/
theorem TypeAt.centralizer_not_le_normalizer (h : TypeAt z V) :
    ¬ involutionCentralizer z ≤ normalizer (V : Set G) := by
  intro hle
  have hc := card_dvd_of_le hle
  rw [h.normalizer_card, h.centralizer_card] at hc
  norm_num at hc

end CFSG.Quasithin.HigmanSims
