module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Irreducible


/-!
# The centerless cases of the star-action obstruction

The genuine 13.6.11 commutator on U_K shows that L_v has a nontrivial
image in the faithful action on W_K. Once L_v ≤ K, a vanishing plus
commutator puts this image in Z(K⁺). Thus every centerless reduced model
has a nonzero plus commutator. The model alternatives retain actual
isomorphisms, including the literal derived symplectic and G₂ groups.

This proves the centerless branches only. The covered A₆ alternative has
a center of order three and requires a separate source argument. None of
the lemmas below assumes that its cubic image is noncentral.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.11 and 13.6.14, printed pp.928–930; the reduced list and 13.6.20–21,
printed pp.931–932. The shared basic action reductions use the actual
star-to-plus map and the source component family Y_z.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction
open ComponentSelection
variable {G : Type*} [Group G]

private theorem le_center_of_commutator_eq_bot {D : Type*} [Group D]
    (A B : Subgroup D) (hc : ⁅A, B⁆ = ⊥) :
    B.subgroupOf A ≤ center A := by
  intro b hb
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  exact mem_centralizer_iff.mp
    ((commutator_eq_bot_iff_le_centralizer.mp hc) a.property) b hb |>.symm

/-- Containment and a vanishing commutator put the entire literal L_v⁺
inside the ambient image of Z(K⁺). The covered case retains this center. -/
theorem plusImage_Lv_le_center_of_commutator_eq_bot
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K)
    (hc : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ = ⊥) :
    plusImage K L T z v hL hz (Lv L v) ≤
      (center (plusImage K L T z v hL hz K)).map
        (plusImage K L T z v hL hz K).subtype := by
  have hi : plusImage K L T z v hL hz (Lv L v) ≤ plusImage K L T z v hL hz K :=
    map_mono (comap_mono hLK)
  intro x hx
  exact mem_map.mpr ⟨⟨x, hi hx⟩, le_center_of_commutator_eq_bot _ _ hc hx, rfl⟩

/-- The earlier marked 13.6.11 deduction rules out a trivial plus image;
no noncentrality premise is added. Invariance is the earlier 13.6.14 input. -/
theorem plusImage_Lv_ne_bot [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (K T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G)) :
    plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz
      (Lv L (A5Module.markedV s)) ≠ ⊥ := by
  intro hb
  have hc := (plusImage_eq_bot_iff K L T _ _ hL hz _
    (show Lv L _ ≤ plusActor K L T _ from le_sup_right.trans le_sup_left)).mp hb
  have hUK : UK K L T (A5Module.markedZ s) (A5Module.markedV s) ≤
      WK K L T (A5Module.markedZ s) (A5Module.markedV s) :=
    le_normalizer_iff_commutator_le_left.mp
      ((K_le_plusActor K L T _).trans (plusActor_normalizes_WK K L T _ _ hL hz))
  exact UK_commutator_ne_bot s K T S hS hz hK hn
    (commutator_eq_bot_iff_le_centralizer.mpr
      (hUK.trans (le_centralizer_iff.mp hc)))

/-- Derive the required nonzero commutator from 13.6.20 containment in the
centerless case. The preceding theorem supplies nontriviality internally. -/
theorem plus_commutator_ne_bot_of_centerless [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (K T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G))
    (hLK : Lv L (A5Module.markedV s) ≤ K)
    (hcenter : center (plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K) = ⊥) :
    ⁅plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K,
      plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz
        (Lv L (A5Module.markedV s))⁆ ≠ ⊥ := by
  intro hc
  have hle := plusImage_Lv_le_center_of_commutator_eq_bot K L T _ _ hL hz hLK hc
  rw [hcenter, Subgroup.map_bot] at hle
  exact plusImage_Lv_ne_bot s K T S hS hL hz hK hn (bot_unique hle)

private theorem binary_linear_center (n : ℕ) (hn : 0 < n) :
    center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  have hc := hbits a
  rcases hc with rfl | rfl
  · simp [Fintype.card_fin, zero_pow (by omega : n ≠ 0)] at ha
  · change g = 1
    apply Subtype.ext
    simpa [Matrix.scalar_apply] using he.symm

private theorem center_transport {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (he : center E = ⊥) : center D = ⊥ := by
  apply eq_bot_iff.mpr
  intro d hd
  have h : e d ∈ center E := ((centerCongr e) ⟨d, hd⟩).property
  rw [he, mem_bot] at h
  exact mem_bot.mpr (e.injective (by simpa using h))

private theorem centerless_of_simple_perfect (D : Type*) [Group D]
    [IsSimpleGroup D] [Group.IsPerfect D] : center D = ⊥ := by
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · let : IsMulCommutative D := (center_eq_top_iff.mp ht)
    let : Subsingleton D := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton D)
      (inferInstance : Nontrivial D)).elim

/-- The centerless entries of the reduced list on p.931. Each branch
identifies the actual actor with the displayed carrier; the ordinary A₆
entry and the literal Sp₄(2)′ entry are both supported. -/
inductive CenterlessModel (D : Type*) [Group D] : Prop
  | linear (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
      (model : Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
  | alternating (n : ℕ) (hn : n = 6 ∨ n = 7)
      (model : Nonempty (D ≃* alternatingGroup (Fin n)))
  | symplecticTwo (model : Nonempty
      (D ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
  | binaryG2 (model : Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2))))

/-- Centerlessness is proved from the concrete model. The binary scalar
calculation handles all three linear degrees, the alternating center theorem
handles A₆ and A₇, and the existing literal G₂(2)′ simplicity theorem
combines with the inherited quasisimplicity of the actual actor. -/
theorem CenterlessModel.center_eq_bot {D : Type*} [Group D] [IsQuasisimple D]
    (h : CenterlessModel D) : center D = ⊥ := by
  cases h with
  | linear n hn model =>
    obtain ⟨e⟩ := model
    exact center_transport e (binary_linear_center n (by rcases hn with rfl | rfl | rfl <;> decide))
  | alternating n hn model =>
    obtain ⟨e⟩ := model
    exact center_transport e (alternatingGroup.center_eq_bot (by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rcases hn with rfl | rfl <;> decide))
  | symplecticTwo model =>
    obtain ⟨e⟩ := model
    exact center_transport (e.trans
      CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.binarySymplecticDerivedEquiv)
      (alternatingGroup.center_eq_bot (by simp))
  | binaryG2 model =>
    obtain ⟨e⟩ := model
    let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup D := e.isSimpleGroup
    exact centerless_of_simple_perfect D

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction
