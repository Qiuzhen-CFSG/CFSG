module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Intrinsic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.BlockQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CheckedCenter
public import Theory.GroupTheory.PCoreSurjective

/-!
# The source marking for the exceptional seven branch

This file records the actual source actor, its marked quotient plane, and the
Sylow two-subgroup transported through the prescribed quotient map.  The
placement of the seed commutator is obtained from the checked center-preimage
identity; it is therefore a source geometric input rather than an assumption
of the target plane statement.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed pp. 926--932.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors

variable {G : Type*} [Group G] [Finite G]
variable {L V K : Subgroup G} (s : Marking L V)

omit [Finite G] in
theorem placement_of_checked_center
    {v : G} (hK : K ≤ Gv v) (hshort : IsShort K) (hv : v ^ 2 = 1)
    (hz : zpowers (markedZ s) ≤ checkedBlockCenterPreimage K v hK) :
    ⁅zpowers (markedZ s), K⁆ ≤ (ChapterC.blockU K).map K.subtype := by
  rw [← checkedBlockCenterPreimage_commutator K v hK hshort hv]
  exact commutator_mono hz le_rfl

omit [Finite G] in
theorem actor_image_eq_map
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    {U : Subgroup G} {ρ : Representation (ZMod 2) A W}
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L (markedV s) ≤ K) :
    actorImage s m hLK = Subgroup.map m.actor ((Lv L (markedV s)).subgroupOf K) := by
  rw [actorImage, MonoidHom.range_eq_map, ← Subgroup.map_map]
  congr 1
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_map]
  change Subgroup.map ((Lv L (markedV s)).subtype) ⊤ =
    Subgroup.map K.subtype ((Lv L (markedV s)).subgroupOf K)
  rw [Subgroup.map_subgroupOf_eq_of_le hLK]
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exceptionalSeven_source_marking
    {T : Sylow 2 G}
    (h : IsExceptionalA7Block K)
    (e : (K ⧸ pCore 2 K) ≃* A7)
    (hLK : Lv L (markedV s) ≤ K)
    {v : G} (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hz : zpowers (markedZ s) ≤ checkedBlockCenterPreimage K v hK)
    (hTv : Tv (T : Subgroup G) (markedV s) ⊓ K ≤
      normalizer ((⁅V, Lv L (markedV s)⁆ : Subgroup G) : Set G))
    (hTvLv : Tv (T : Subgroup G) (markedV s) ⊓ K ≤
      normalizer ((Lv L (markedV s) : Subgroup G) : Set G))
    (hSyl : ∃ P : Sylow 2 K,
      (P : Subgroup K).map K.subtype = Tv (T : Subgroup G) (markedV s) ⊓ K)
    (hcore : (pCore 2 K).comap (inclusion hLK) = pCore 2 (Lv L (markedV s)))
    (hLvCard : Nat.card (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) = 3) :
    letI := h.1.module_elementary
    letI : CommGroup (BlockModule K) := IsMulCommutative.instCommGroup
    let hlU := moved_le_of_seed s hLK
      (placement_of_checked_center s hK h.1 hv hz)
    ∃ (ρ : Representation (ZMod 2) A7 (Additive (BlockModule K)))
      (m : ConjugationQuotientModel K ((ChapterC.blockU K).map K.subtype) ρ)
      (P : Submodule (ZMod 2) (Additive (BlockModule K))) (S : Sylow 2 A7)
      (D : Subgroup A7),
      m.actor = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) ∧
      P = quotientPlane s m hlU ∧
      D = actorImage s m hLK ∧
      (S : Subgroup A7) =
        ((Tv (T : Subgroup G) (markedV s) ⊓ K).subgroupOf K).map m.actor ∧
      PermittedActor ρ P S D := by
  let := h.1.module_elementary
  let : CommGroup (BlockModule K) := IsMulCommutative.instCommGroup
  obtain ⟨ρ, hρ, hdim, m, hm⟩ := exceptionalSeven_quotientModel K h e
  let hlU := moved_le_of_seed s hLK
    (placement_of_checked_center s hK h.1 hv hz)
  let l := Lv L (markedV s)
  let A := (Tv (T : Subgroup G) (markedV s) ⊓ K).subgroupOf K
  let D : Subgroup A7 := actorImage s m hLK
  let f := m.actor.comp (inclusion hLK)
  have hf : Function.Surjective m.actor := by
    rw [hm]
    exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P₀, hP₀⟩ := hSyl
  let S : Sylow 2 A7 := P₀.mapSurjective (f := m.actor) hf
  have hPA : (P₀ : Subgroup K) = A := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hP₀, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hS : (S : Subgroup A7) = A.map m.actor := by
    change (P₀ : Subgroup K).map m.actor = A.map m.actor
    rw [hPA]
  have hD : D = (l.subgroupOf K).map m.actor := by
    dsimp [D, l]
    exact actor_image_eq_map s m hLK
  have hnormK : A ≤ normalizer (l.subgroupOf K : Set K) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    have hk' : (k : G) ∈ Tv (T : Subgroup G) (markedV s) ⊓ K := hk
    constructor
    · intro hx
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hTvLv hk') (x : G)).mp
        (mem_subgroupOf.mp hx))
    · intro hx
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hTvLv hk') (x : G)).mpr
        (mem_subgroupOf.mp hx))
  have hnormD : A.map m.actor ≤ normalizer D := by
    rw [hD]
    exact (map_mono hnormK).trans (Subgroup.le_normalizer_map m.actor)
  let hplane : Submodule (ZMod 2) (Additive (BlockModule K)) :=
    quotientPlane s m hlU
  have hst : (S : Subgroup A7) ≤ subspaceStabilizer ρ hplane := by
    rw [hS]
    apply le_subspaceStabilizer
    intro a ha w hw
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
    change ρ (m.actor k) w ∈ quotientPlane s m hlU
    change w ∈ quotientPlane s m hlU at hw
    have hk' : (k : G) ∈ Tv (T : Subgroup G) (markedV s) ⊓ K := hk
    exact quotientPlane_invariant_of_normalizes s m hlU k (hTv hk') hw
  have hstab : D ≤ subspaceStabilizer ρ hplane := by
    apply le_subspaceStabilizer
    intro d hd w hw
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hd
    change ρ (m.actor (inclusion hLK x)) w ∈ quotientPlane s m hlU
    change w ∈ quotientPlane s m hlU at hw
    exact quotientPlane_invariant s m hlU hLK x hw
  have hnorm : (S : Subgroup A7) ≤ normalizer D := hS ▸ hnormD
  have hmker : m.actor.ker = pCore 2 K := by
    rw [hm, ← MonoidHom.comap_ker,
      (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    ext x
    change QuotientGroup.mk' (pCore 2 K) x = 1 ↔ x ∈ pCore 2 K
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : f.ker = pCore 2 l := by
    rw [← MonoidHom.comap_ker, hmker, hcore]
  let q : l →* D := f.rangeRestrict
  have hqsurj : Function.Surjective q := f.rangeRestrict_surjective
  have hqker : q.ker = pCore 2 l := by
    change f.rangeRestrict.ker = pCore 2 l
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hpc := q.card_pCore_of_ker_isPGroup hqsurj (hqker ▸ pCore_isPGroup)
  have hpcard : Nat.card (pCore 2 D) = 1 := by
    rw [hqker] at hpc
    have hpos : 0 < Nat.card (pCore 2 l) := Nat.card_pos
    apply Nat.mul_left_cancel hpos
    simpa using hpc.symm
  have hpcore : pCore 2 D = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hpcard
  have heq : l ⧸ pCore 2 l ≃* D := by
    exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hDcard : Nat.card D = 3 := by
    exact (Nat.card_congr heq.toEquiv).symm.trans hLvCard
  have hquot : Nat.card (D ⧸ pCore 2 D) = 3 := by
    rw [hpcore, Nat.card_congr QuotientGroup.quotientBot.toEquiv]
    exact hDcard
  refine ⟨ρ, m, hplane, S, D, hm, by rfl, rfl, hS, ?_⟩
  exact ⟨hst, hstab, hnorm, actorImage_twoPerfect s m hLK, hquot,
    by simpa [hplane, D] using quotientPlane_commutator s m hlU hLK⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
