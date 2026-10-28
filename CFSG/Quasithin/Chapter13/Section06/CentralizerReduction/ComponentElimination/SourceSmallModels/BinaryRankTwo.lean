module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CubicActions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CenterPreimage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.MovingPlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.AlternatingGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.SourcePlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.SourceActors

/-!
# Binary rank-two action calculations for Lemma 13.6.22

The source Sp₄(2)′ case is the A₆ block, with its genuine binary permutation
quotient; it is separate from the legacy Sp₄(4) predicate. The G₂ case uses
the actual derived octonion group and its natural scalar quotient.
Both block predicates construct honest ambient conjugation quotient models.
A marked conjugate of the specified cubic gives C_U(Lᵥ)=C_U(K), and this
is transported to the literal checked quotient C_G(v)/⟨v⟩.
The source Z₀ commutator identity is also proved without an extra premise.

The source four-group now constructs the moving plane through the literal
module quotient. Sylow restriction, the actual two-core actor kernel, and
the concrete geometry construct both parabolic markings and cubic actors.
Thus both source action branches give the ambient and checked centralizer
equalities, together with [Z₀,K]=U. The full 13.6.22 owner retains the earlier
local data, source block selection, and the common B.2.14 supplement.
Source: Aschbacher–Smith, combined manuscript, printed pp.932–933.
-/

@[expose] public section
open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo

/-- The two source-correct block alternatives; the old case type is preserved. -/
inductive SourceBlock (K : Type*) [Group K] : Prop
  | alternating (model : IsAlternatingBlock K 6)
  | g2 (model : IsG2TwoBlock K)

/-- The source definition U=[Z(O₂(K)),K], in the ambient group. -/
noncomputable def sourceU {G : Type*} [Group G] (K : Subgroup G) : Subgroup G :=
  ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆

/-- The source commutator layer equals the actual block module layer. -/
theorem sourceU_eq {G : Type*} [Group G] (K : Subgroup G) (h : IsShort K) :
    sourceU K = Models.ambientU K := by
  have hc := congrArg (Subgroup.map K.subtype) (CenterPreimage.core_center_commutator h)
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hc
  exact hc

/-- The precise Z₀ of the source has commutator equal to the source U. -/
theorem sourceZ0_commutator {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1) (h : IsShort K) :
    ⁅CenterPreimage.sourceZ0 K v hK, K⁆ = sourceU K := by
  rw [sourceU_eq K h]
  exact CenterPreimage.sourceZ0_commutator K v hK hv h

/-- Construct the A₆ model, including its actual core quotient map. -/
theorem alternating_model {G : Type*} [Group G] (K : Subgroup G)
    (h : IsAlternatingBlock K 6) :
    ∃ m : ConjugationQuotientModel K (sourceU K)
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)),
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K := by
  rw [sourceU_eq K h.2.1]
  obtain ⟨σ, ⟨b⟩, hσ⟩ := h.2.2
  exact ⟨Models.blockQuotientModel K _ σ b hσ,
    Models.blockQuotientModel_actor_surjective K _ σ b hσ,
    Models.blockQuotientModel_actor_kernel K _ σ b hσ⟩

/-- Construct the genuine G₂(2)′ action from the source octonion projection. -/
theorem g2_model {G : Type*} [Group G] (K : Subgroup G)
    (h : IsG2TwoBlock K) :
    ∃ m : ConjugationQuotientModel K (sourceU K)
      (Atlas.G2.Natural.derivedAction (ZMod 2)),
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K := by
  rw [sourceU_eq K h.1]
  obtain ⟨σ, ⟨b⟩, hσ⟩ := G2Models.g2_linearBlock h
  exact ⟨Models.blockQuotientModel K _ σ b hσ,
    Models.blockQuotientModel_actor_surjective K _ σ b hσ,
    Models.blockQuotientModel_actor_kernel K _ σ b hσ⟩


variable {G : Type*} [Group G] {L K U : Subgroup G} {v : G}

/-- The A₆ cubic marking implies the ambient fixed-space comparison. -/
theorem alternating_centralizer_eq
    (m : ConjugationQuotientModel K U
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)))
    (hLK : Lv L v ≤ K) (g : alternatingGroup (Fin 6))
    (hmark : g * AlternatingAction.actor * g⁻¹ ∈ ((Lv L v).subgroupOf K).map m.actor) :
    U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G) := by
  apply m.centralizer_eq (Lv L v) hLK
  intro w hw
  apply G2Action.conjugate_fixed_eq_zero
    (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6))
    AlternatingAction.actor AlternatingAction.cubic_fixed_eq_zero g w
  obtain ⟨k, hk, he⟩ := hmark
  rw [← he]
  exact hw ⟨k, hk⟩

/-- The G₂ marking uses the actual ambient image of the derived carrier. -/
theorem g2_centralizer_eq
    (m : ConjugationQuotientModel K U (Atlas.G2.Natural.derivedAction (ZMod 2)))
    (hLK : Lv L v ≤ K) (g : Atlas.G2.Model (ZMod 2))
    (hmark : g * Atlas.G2.BinaryParabolicPair.cubicActor * g⁻¹ ∈
      (((Lv L v).subgroupOf K).map m.actor).map
        (commutator (Atlas.G2.Model (ZMod 2))).subtype) :
    U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G) := by
  apply m.centralizer_eq (Lv L v) hLK
  intro w hw
  apply G2Action.g2_conjugate_cubic_fixed_eq_zero g w
  obtain ⟨d, ⟨k, hk, rfl⟩, he⟩ := hmark
  rw [← he]
  exact hw ⟨k, hk⟩

/-- Application to the literal checked quotient in the A₆ branch. -/
theorem alternating_checked_centralizer_eq [Finite G]
    (m : ConjugationQuotientModel K U
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)))
    (hLK : Lv L v ≤ K) (hv : v ^ 2 = 1) (g : alternatingGroup (Fin 6))
    (hmark : g * AlternatingAction.actor * g⁻¹ ∈ ((Lv L v).subgroupOf K).map m.actor) :
    checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v)) :=
  checked_centralizer_eq_of_ambient L K U v hLK hv
    (alternating_centralizer_eq m hLK g hmark)

/-- Application to the literal checked quotient in the G₂(2)′ branch. -/
theorem g2_checked_centralizer_eq [Finite G]
    (m : ConjugationQuotientModel K U (Atlas.G2.Natural.derivedAction (ZMod 2)))
    (hLK : Lv L v ≤ K) (hv : v ^ 2 = 1) (g : Atlas.G2.Model (ZMod 2))
    (hmark : g * Atlas.G2.BinaryParabolicPair.cubicActor * g⁻¹ ∈
      (((Lv L v).subgroupOf K).map m.actor).map
        (commutator (Atlas.G2.Model (ZMod 2))).subtype) :
    checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v)) :=
  checked_centralizer_eq_of_ambient L K U v hLK hv
    (g2_centralizer_eq m hLK g hmark)


/-- Earlier local data used on printed p.932. These are statements about the
original subgroups: no parabolic placement or fixed-space conclusion is included.
The Sylow subgroup belongs to K T_v, and T_v normalizes K (relative normality). -/
structure SourceLineData (L K V T : Subgroup G) (v : G) where
  lv_le : Lv L v ≤ K
  normalizes_K : T ≤ normalizer (K : Set G)
  normalizes_Lv : T ≤ normalizer (Lv L v : Set G)
  line_le : ⁅V, Lv L v⁆ ≤ sourceU K
  line_card : Nat.card (⁅V, Lv L v⁆ : Subgroup G) = 4
  line_moved : ⁅⁅V, Lv L v⁆, Lv L v⁆ = ⁅V, Lv L v⁆
  line_invariant : Lv L v ⊔ T ≤ normalizer ((⁅V, Lv L v⁆ : Subgroup G) : Set G)
  sylow : Sylow 2 ↥(K ⊔ T)
  sylow_eq : (sylow : Subgroup ↥(K ⊔ T)) = T.subgroupOf (K ⊔ T)
  three_dvd : 3 ∣ Nat.card (Lv L v)

/-- The actual source product P=L_v(T_v∩K). -/
noncomputable def sourceP (L K T : Subgroup G) (v : G) : Subgroup G :=
  Lv L v ⊔ (T ⊓ K)

/-- Construct the A₆ syntheme parabolic and its cubic from the source line.
The model is the genuine quotient model, with its original two-core kernel. -/
theorem alternating_source_marking [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v)
    (m : ConjugationQuotientModel K (sourceU K)
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)))
    (hf : Function.Surjective m.actor) (hk : m.actor.ker = pCore 2 K) :
    ∃ g : alternatingGroup (Fin 6),
      ((sourceP L K T v).subgroupOf K).map m.actor =
        AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom ∧
      g * AlternatingAction.actor * g⁻¹ ∈ ((Lv L v).subgroupOf K).map m.actor := by
  obtain ⟨S, hS⟩ := SourceActors.exists_source_sylow d.normalizes_K d.sylow d.sylow_eq
  let e := SourcePlane.movingPlane m hf T S hS d.lv_le d.line_le d.line_moved
    d.line_card d.line_invariant
  have hp := SourceActors.image_perfect m.actor d.lv_le
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v))
  have hn : ((S.mapSurjective hf : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup _) ≤
      normalizer (((Lv L v).subgroupOf K).map m.actor : Set (alternatingGroup (Fin 6))) := by
    rw [SourceActors.sylow_image m.actor hf S hS]
    exact SourceActors.image_normalizes m.actor d.normalizes_Lv
  have h3 := SourceActors.three_dvd_image m.actor d.lv_le
    (by rw [hk]; exact pCore_isPGroup) d.three_dvd
  obtain ⟨g, hg, ha⟩ := alternating_movingPlane_recognition_of_three_dvd
    (S.mapSurjective hf) _ hp hn h3 e
  refine ⟨g, ?_, ha⟩
  change ((Lv L v ⊔ (T ⊓ K)).subgroupOf K).map m.actor = _
  rw [SourceActors.parabolic_image m.actor d.lv_le,
    ← SourceActors.sylow_image m.actor hf S hS]
  exact hg

/-- Construct the G₂(2)′ parabolic on its literal derived carrier and embed it
in the octonion automorphism group, using the source line and Sylow subgroup. -/
theorem g2_source_marking [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v)
    (m : ConjugationQuotientModel K (sourceU K) (Atlas.G2.Natural.derivedAction (ZMod 2)))
    (hf : Function.Surjective m.actor) (hk : m.actor.ker = pCore 2 K) :
    ∃ g : Atlas.G2.Model (ZMod 2),
      (((sourceP L K T v).subgroupOf K).map m.actor).map
          (commutator (Atlas.G2.Model (ZMod 2))).subtype =
        Atlas.G2.BinaryParabolicPair.derivedFirstAmbient.map (MulAut.conj g).toMonoidHom ∧
      g * Atlas.G2.BinaryParabolicPair.cubicActor * g⁻¹ ∈
        (((Lv L v).subgroupOf K).map m.actor).map
          (commutator (Atlas.G2.Model (ZMod 2))).subtype := by
  obtain ⟨S, hS⟩ := SourceActors.exists_source_sylow d.normalizes_K d.sylow d.sylow_eq
  let e := SourcePlane.movingPlane m hf T S hS d.lv_le d.line_le d.line_moved
    d.line_card d.line_invariant
  have hn : ((S.mapSurjective hf : Sylow 2 (commutator (Atlas.G2.Model (ZMod 2)))) :
      Subgroup _) ≤ normalizer (((Lv L v).subgroupOf K).map m.actor :
        Set (commutator (Atlas.G2.Model (ZMod 2)))) := by
    rw [SourceActors.sylow_image m.actor hf S hS]
    exact SourceActors.image_normalizes m.actor d.normalizes_Lv
  have h3 := SourceActors.three_dvd_image m.actor d.lv_le
    (by rw [hk]; exact pCore_isPGroup) d.three_dvd
  obtain ⟨g, hg, ha⟩ := G2Geometry.recognition_of_three_dvd
    (S.mapSurjective hf) _ hn h3 e
  refine ⟨g, ?_, ha⟩
  change (((Lv L v ⊔ (T ⊓ K)).subgroupOf K).map m.actor).map _ = _
  rw [SourceActors.parabolic_image m.actor d.lv_le,
    ← SourceActors.sylow_image m.actor hf S hS]
  exact hg

/-- The A₆ block branch now derives its marking and fixed-space comparison
from the original source four-group. -/
theorem alternating_source_centralizer_eq [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v) (h : IsAlternatingBlock K 6) :
    sourceU K ⊓ centralizer (Lv L v : Set G) = sourceU K ⊓ centralizer (K : Set G) := by
  obtain ⟨m, hf, hk⟩ := alternating_model K h
  obtain ⟨g, _, ha⟩ := alternating_source_marking d m hf hk
  exact alternating_centralizer_eq m d.lv_le g ha

/-- The G₂(2)′ block branch on the actual trace-zero scalar quotient. -/
theorem g2_source_centralizer_eq [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v) (h : IsG2TwoBlock K) :
    sourceU K ⊓ centralizer (Lv L v : Set G) = sourceU K ⊓ centralizer (K : Set G) := by
  obtain ⟨m, hf, hk⟩ := g2_model K h
  obtain ⟨g, _, ha⟩ := g2_source_marking d m hf hk
  exact g2_centralizer_eq m d.lv_le g ha

/-- Both source-correct alternatives give the ambient comparison. -/
theorem source_centralizer_eq [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v) (h : SourceBlock K) :
    sourceU K ⊓ centralizer (Lv L v : Set G) = sourceU K ⊓ centralizer (K : Set G) := by
  cases h with
  | alternating h => exact alternating_source_centralizer_eq d h
  | g2 h => exact g2_source_centralizer_eq d h

/-- The two concrete action branches supply both inputs to the common endgame:
the checked centralizer equality and [Z₀,K]=U, with Z₀ the actual center preimage. -/
theorem source_action_conclusions [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v) (h : SourceBlock K)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1) :
    (checkedImage v (sourceU K) ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v (sourceU K) ⊓ centralizer (checkedImage v K : Set (Gcheck v))) ∧
    ⁅CenterPreimage.sourceZ0 K v hK, K⁆ = sourceU K := by
  refine ⟨checked_centralizer_eq_of_ambient L K (sourceU K) v d.lv_le hv
    (source_centralizer_eq d h), sourceZ0_commutator K v hK hv ?_⟩
  cases h with
  | alternating h => exact h.2.1
  | g2 h => exact h.1

/-- Application to the literal checked-quotient endgame. The earlier conjugate
and B.2.14 supplement remain inputs belonging to the full 13.6.22 assembly. -/
theorem source_centralizes [Finite G] {V T : Subgroup G}
    (d : SourceLineData L K V T v) (h : SourceBlock K)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (a : Gv v) (F : Subgroup (Gcheck v)) [IsMulCommutative F]
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v (sourceU K) ⊔
      (F ⊓ centralizer (checkedImage v K : Set (Gcheck v)))) :
    K ≤ Gv (a : G) := by
  have hp : IsPPerfect 2 K := by
    cases h with
    | alternating h => exact h.2.1.twoPerfect
    | g2 h => exact h.1.twoPerfect
  exact Source.centralizes_of_checked_fixed_space_comparison L K (sourceU K) v a F
    hK hp hv d.lv_le ha haF hsplit (source_action_conclusions d h hK hv).1

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
