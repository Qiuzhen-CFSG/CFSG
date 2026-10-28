module
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned
public import Theory.Representation.BinaryConjugationSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedCenterOrder

/-!
# The exceptional and regular mixed DGS distance-two profiles

The literal A₅/S₃ quotient markings give graph valences five and three.
Thus the central distance-two inequality q_alpha ≤ q_beta forces the
orientation (q_alpha,q_beta)=(2,4). In the exceptional branch, D_alpha=Z_alpha,
the index q_beta² and the natural center of order q_alpha² determine the
reduced Borel core to have order 128. The existing full-Borel extension
then gives original Sylow order 128 or 256.

For the regular branch, (10.10) would give a binary irreducible section of
order 64 under the actual first reduced parabolic quotient A₅=SL₂(4).
Prime-field highest-weight parameters exclude dimension six. This proves
the mixed regular exclusion without assuming the field refinement in the
remark on p.165 or a parabolic recognition map.

The profile records retain actual intersections, indices and conjugation
coordinates. Their construction and exhaustive critical-distance selection
remain with the existing DGS producers and the mixed-size assembly owner.
Neither record is a recognition certificate or a statement of the final bound.
The commuting-distance-one numerical branch is reused by the Chapter10 consumer.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7)--(10.10), printed pp.158--165, especially the formulas on pp.162,164;
(11.7), p.174; Aschbacher--Smith F.1.12(I), pp.262--264.
-/

@[expose] public noncomputable section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem irreducible_card_ne_sixtyfour
    (ρ : Representation (ZMod 2) SL(2,k) W) [ρ.IsIrreducible]
    (hk : Nat.card k = 4) : Nat.card W ≠ 64 := by
  intro hW
  have hd : Module.finrank (ZMod 2) W = 6 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod, hW] at hh
    exact (Nat.pow_right_injective (by decide : 1 < 2)) (by simpa using hh.symm)
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! ht
    let b := Module.finBasis (ZMod 2) W
    let j : Fin (Module.finrank (ZMod 2) W) := ⟨0, by omega⟩
    let A : Subrepresentation ρ := {
      toSubmodule := Submodule.span (ZMod 2) {b j}
      apply_mem_toSubmodule := by intro g v hv; simpa only [ht, Module.End.one_apply] using hv }
    have hA : A ≠ ⊥ := by
      intro he
      have hv : b j ∈ A := Submodule.subset_span (Set.mem_singleton (b j))
      rw [he] at hv
      exact b.ne_zero j hv
    have he := congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top A).resolve_left hA)
    have hdA : Module.finrank (ZMod 2) A.toSubmodule = 1 := finrank_span_singleton (b.ne_zero j)
    change A.toSubmodule = ⊤ at he
    rw [he, finrank_top, hd] at hdA
    omega
  obtain ⟨hs,n,hn,hsdiv,_,hdeg⟩ :=
    Representation.SL2.Unsigned.exists_primeField_highestWeight_parameters
      2 ρ hnt 2 (by simpa using hk)
  have hnlt : n.val < 4 := by simpa [hk] using n.isLt
  have hsone := (Nat.dvd_prime Nat.prime_two).mp hsdiv
  simp only [Fin.prod_univ_two] at hdeg
  rcases hsone with hsone | hsone <;> rw [hsone, hd] at hdeg <;>
    interval_cases h : n.val <;> norm_num [h] at hdeg
end CFSG.Quasithin.ChapterF.Source.MixedDGS

namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S
local notation "M" => Reduction.G₀ ![K,U] S
local notation "H" => parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 0

/-- Both source orientations are determined by the literal mixed quotient markings. -/
theorem oriented_parameters (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (i : Bool) (qa qb : ℕ)
    (ha : Nat.card ((graph F).neighborSet (base F i)) = qa + 1)
    (hb : Nat.card ((graph F).neighborSet (base F (!i))) = qb + 1) :
    (i = false ∧ qa = 4 ∧ qb = 2) ∨ (i = true ∧ qa = 2 ∧ qb = 4) := by
  rw [CommutingOneProfile.mixed_reduced_neighbor_cards K U S h eK eU] at ha hb
  cases i
  · exact Or.inl ⟨rfl, by change 5 = qa + 1 at ha; omega, by change 3 = qb + 1 at hb; omega⟩
  · exact Or.inr ⟨rfl, by change 3 = qa + 1 at ha; omega, by change 5 = qb + 1 at hb; omega⟩

/-- The central distance-two field inequality selects the cubic alpha and quintic beta. -/
theorem central_parameters (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (i : Bool) (qa qb : ℕ)
    (ha : Nat.card ((graph F).neighborSet (base F i)) = qa + 1)
    (hb : Nat.card ((graph F).neighborSet (base F (!i))) = qb + 1)
    (hle : qa ≤ qb) : i = true ∧ qa = 2 ∧ qb = 4 := by
  rcases oriented_parameters h eK eU i qa qb ha hb with hs | hs
  · omega
  · exact hs

/-- The quotient map is the actual reduced first-parabolic quotient, with the original A5 marking. -/
noncomputable def firstLinearQuotient (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) : H →* Representation.SL2FourNatural.SL :=
  ((h.mixed_reduced_first_quotient eK eU).some.trans
    Representation.SL2FourNatural.alternatingFiveEquiv.symm).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 H))

private theorem regular_profile_excluded (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (i : Bool) (qa qb : ℕ)
    (ha : Nat.card ((graph F).neighborSet (base F i)) = qa + 1)
    (hb : Nat.card ((graph F).neighborSet (base F (!i))) = qb + 1)
    (hle : qa ≤ qb)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) Representation.SL2FourNatural.SL W) [ρ.IsIrreducible]
    (d : Representation.BinaryConjugationSection H (twoCore (parabolic ![K,U] S 0))
      ((Z F (base F (!i))).map (M).subtype) (ρ.comp (firstLinearQuotient h eK eU)))
    (hZ : Nat.card ((Z F (base F (!i))).map (M).subtype) = qa)
    (horder : Nat.card (twoCore (commonBorel ![K,U] S)) = qa^3 * qb^3) : False := by
  obtain ⟨hi,hqa,hqb⟩ := central_parameters h eK eU i qa qb ha hb hle
  have hc := d.card_section
  have hratio := h.mixed_borel_core_card eK eU
  have hB : Nat.card (twoCore (commonBorel ![K,U] S)) = Nat.card (pCore 2 (commonBorel ![K,U] S)) :=
    card_map_of_injective (commonBorel ![K,U] S).subtype_injective
  have hQ : Nat.card (twoCore (parabolic ![K,U] S 0)) = Nat.card (pCore 2 (parabolic ![K,U] S 0)) :=
    card_map_of_injective (parabolic ![K,U] S 0).subtype_injective
  rw [hQ,hZ,hqa] at hc
  rw [hB,hqa,hqb] at horder
  have hW : Nat.card W = 64 := by norm_num at horder; omega
  exact irreducible_card_ne_sixtyfour ρ
    (by simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field) hW
end CFSG.Quasithin.ChapterF.Source.MixedDGS

namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S
local notation "M" => Reduction.G₀ ![K,U] S
local notation "R₀" => Subgroup.subgroupOf (twoCore (commonBorel ![K,U] S)) M

private theorem exceptional_profile_size (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (i : Bool) (qa qb : ℕ)
    (ha : Nat.card ((graph F).neighborSet (base F i)) = qa + 1)
    (hb : Nat.card ((graph F).neighborSet (base F (!i))) = qb + 1)
    (hle : qa ≤ qb) (t : Vertex F)
    (hD : Q F (base F (!i)) ⊓ Q F t = Z F (base F i))
    (hsection : (Q F (base F (!i)) ⊓ Q F t).relIndex (Q F (base F i)) = qb^2)
    (hZ : Nat.card (Z F (base F i)) = qa^2)
    (hindex : (Q F (base F i)).relIndex R₀ = qa) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 128 ∧
      (Nat.card S = 128 ∨ Nat.card S = 256) := by
  obtain ⟨hi,hqa,hqb⟩ := central_parameters h eK eU i qa qb ha hb hle
  have ht := Reduction.reduced_triple h
  have hZQ : Z F (base F i) ≤ Q F (base F i) :=
    (source_Z_Q_U ht _).1.trans (map_subtype_le _)
  have hQR : Q F (base F i) ≤ R₀ := by
    have hedge : (stabilizer F (base F false) ⊓ stabilizer F (base F true)).pCoreIn 2 = R₀ := by
      have hBG : Reduction.B₀ ![K,U] S ≤ M :=
        (show Reduction.B₀ ![K,U] S ≤ Reduction.P₀ ![K,U] S 0 from le_sup_right).trans le_sup_left
      rw [show stabilizer F (base F false) = F false from Subgroup.CosetGeometry.stabilizer_base _ _,
        show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base _ _,
        show F false ⊓ F true = (Reduction.B₀ ![K,U] S).subgroupOf M from ht.intersection,
        pCoreIn_subgroupOf 2 _ _ hBG, Reduction.B₀_core h]
      rfl
    rw [←hedge]
    have hadj : (graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
    have hh := Noncommuting.graph_Q_le_edgeCore ht hadj
    change Q F (base F i) ≤ (stabilizer F (base F i) ⊓ stabilizer F (base F (!i))).pCoreIn 2 at hh
    cases i
    · exact hh
    · simpa only [Bool.not_true, inf_comm] using hh
  have hq := relIndex_mul_relIndex (⊥ : Subgroup M)
    (Z F (base F i)) (Q F (base F i)) bot_le hZQ
  rw [relIndex_bot_left,relIndex_bot_left,←hD,hsection,hD,hZ,hqa,hqb] at hq
  have hr := relIndex_mul_relIndex (⊥ : Subgroup M) (Q F (base F i)) R₀ bot_le hQR
  rw [relIndex_bot_left,relIndex_bot_left,hindex,hqa] at hr
  have hR : Nat.card R₀ = 128 := by norm_num at hq; omega
  have hRM : twoCore (commonBorel ![K,U] S) ≤ M :=
    (show twoCore (commonBorel ![K,U] S) ≤ Reduction.B₀ ![K,U] S from le_sup_right).trans
      ((show Reduction.B₀ ![K,U] S ≤ Reduction.P₀ ![K,U] S 0 from le_sup_right).trans le_sup_left)
  have hc : Nat.card (twoCore (commonBorel ![K,U] S)) = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv).symm.trans hR
  have hpc : Nat.card (pCore 2 (commonBorel ![K,U] S)) = 128 :=
    (card_map_of_injective (commonBorel ![K,U] S).subtype_injective).symm.trans hc
  have hs := h.mixed_sylow_card_borel_core_cases eK eU
  rw [hpc] at hs
  exact ⟨hc,by simpa using hs⟩
end CFSG.Quasithin.ChapterF.Source.MixedDGS

namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] (K U S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U] S
local notation "M" => Reduction.G₀ ![K,U] S
local notation "R₀" => Subgroup.subgroupOf (twoCore (commonBorel ![K,U] S)) M
local notation "H" => parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 0

/-- The literal index and center clauses used from (10.7) and the exceptional branch (10.9).
It does not contain a bound or the order of the Borel core. -/
structure ExceptionalProfile where
  alpha : Bool
  qAlpha : ℕ
  qBeta : ℕ
  alpha_valence : Nat.card ((graph F).neighborSet (base F alpha)) = qAlpha + 1
  beta_valence : Nat.card ((graph F).neighborSet (base F (!alpha))) = qBeta + 1
  fields_ordered : qAlpha ≤ qBeta
  opposite : Vertex F
  intersection : Q F (base F (!alpha)) ⊓ Q F opposite = Z F (base F alpha)
  section_index : (Q F (base F (!alpha)) ⊓ Q F opposite).relIndex
    (Q F (base F alpha)) = qBeta^2
  center_card : Nat.card (Z F (base F alpha)) = qAlpha^2
  sylow_index : (Q F (base F alpha)).relIndex R₀ = qAlpha

universe v

/-- The irreducible alternative of (10.10), with the actual quotient map,
conjugation section and source polynomial order. No recognition is encoded. -/
structure RegularProfile (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) where
  alpha : Bool
  qAlpha : ℕ
  qBeta : ℕ
  alpha_valence : Nat.card ((graph F).neighborSet (base F alpha)) = qAlpha + 1
  beta_valence : Nat.card ((graph F).neighborSet (base F (!alpha))) = qBeta + 1
  fields_ordered : qAlpha ≤ qBeta
  W : Type v
  [additive : AddCommGroup W]
  [moduleStructure : Module (ZMod 2) W]
  [finite : Finite W]
  action : Representation (ZMod 2) Representation.SL2FourNatural.SL W
  irreducible : action.IsIrreducible
  coordinates : Representation.BinaryConjugationSection H (twoCore (parabolic ![K,U] S 0))
    ((Z F (base F (!alpha))).map (M).subtype) (action.comp (firstLinearQuotient h eK eU))
  center_card : Nat.card ((Z F (base F (!alpha))).map (M).subtype) = qAlpha
  sylow_card : Nat.card (twoCore (commonBorel ![K,U] S)) = qAlpha^3 * qBeta^3

/-- The actual exceptional core indices imply the original Sylow bound through the full Borel. -/
theorem exceptional_size (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (p : ExceptionalProfile K U S) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 128 ∧
      (Nat.card S = 128 ∨ Nat.card S = 256) :=
  exceptional_profile_size h eK eU p.alpha p.qAlpha p.qBeta p.alpha_valence p.beta_valence
    p.fields_ordered p.opposite p.intersection p.section_index p.center_card p.sylow_index

/-- The exceptional profile bounds the literal original quintic parabolic core exactly. -/
theorem exceptional_first_core_card (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (p : ExceptionalProfile K U S) :
    Nat.card (pCore 2 (parabolic ![K,U] S 0)) = 32 := by
  have hc := (exceptional_size K U S h eK eU p).1
  have hmap : Nat.card (twoCore (commonBorel ![K,U] S)) =
      Nat.card (pCore 2 (commonBorel ![K,U] S)) :=
    card_map_of_injective (commonBorel ![K,U] S).subtype_injective
  rw [hmap,h.mixed_borel_core_card eK eU] at hc
  omega

/-- The regular irreducible source profile is impossible for the original mixed pair. -/
theorem not_regular_profile (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (p : RegularProfile K U S h eK eU) : False := by
  let := p.additive
  let := p.moduleStructure
  let := p.finite
  let := p.irreducible
  exact regular_profile_excluded h eK eU p.alpha p.qAlpha p.qBeta p.alpha_valence p.beta_valence
    p.fields_ordered p.action p.coordinates p.center_card p.sylow_card
end CFSG.Quasithin.ChapterF.Source.MixedDGS

namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- The surviving source alternatives after the literal mixed markings are
specialized.  The regular irreducible alternative is deliberately absent:
`not_regular_profile` proves it impossible.  The source assembly supplying
this proposition must still establish that every critical-distance branch
lands in one of these two constructors. -/
inductive MixedDGSProfile
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) : Prop
  | exceptional (p : ExceptionalProfile K U S) : MixedDGSProfile h eK eU
  | commutingOne
      (hc : IsCriticalPair F (base F false) (base F true))
      (hb : b F = 1)
      (hcomm : ⁅Z F (base F false), Z F (base F true)⁆ = ⊥) :
      MixedDGSProfile h eK eU

/-- The exceptional and commuting-one branches give the reduced kernel
orders used by (15.1).  This theorem performs the numerical specialization
of the actual A₅/S₃ valences; it does not assume a recognition map or a
kernel bound. -/
theorem mixed_profile_core_card_le_128
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (p : MixedDGSProfile h eK eU) :
    Nat.card (twoCore (commonBorel ![K,U] S)) ≤ 128 := by
  cases p with
  | exceptional p =>
    have hs := exceptional_size K U S h eK eU p
    omega
  | commutingOne hc hb hcomm =>
    have hs := DGS85.CommutingOneProfile.mixed_binary_graph_exact_row_size
      K U S h eK eU hc hb hcomm
    omega

/-- The exact exhaustive-profile input needed for the mixed numerical
consequence.  It retains the full source hypotheses, including quasithinness,
the literal Sylow placement in the generated group, both quotient markings,
and the normalized cubic Borel. -/
def MixedDGSProfileExhaustive (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (K U S : Subgroup G),
    (h : HypothesisF11 ![K,U] S) →
    IsQuasithin (generated ![K,U] S) →
    Chapter1.IsSylowIn 2 S (generated ![K,U] S) →
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) →
    borel U S ≤ normalizer (S : Set G) →
    MixedDGSProfile h eK eU

/-- Apply the existing outer transport to the specialized profile bounds.
The reduced completion is only used through its literal full-Borel core; no
Sylow assertion about the reduced generated group is introduced. -/
theorem mixed_a5_s3_sylow_card_le_of_dgs_profiles
    (profiles : MixedDGSProfileExhaustive G)
    (K U S : Subgroup G)
    (h : HypothesisF11 ![K,U] S)
    (hqt : IsQuasithin (generated ![K,U] S))
    (hSyl : Chapter1.IsSylowIn 2 S (generated ![K,U] S))
    (hK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hU : Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)))
    (hn : borel U S ≤ normalizer (S : Set G)) :
    Nat.card S ≤ 256 := by
  obtain ⟨eK⟩ := hK
  obtain ⟨eU⟩ := hU
  have p := profiles K U S h hqt hSyl eK eU hn
  have hcore := mixed_profile_core_card_le_128 h eK eU p
  have hmap : Nat.card (twoCore (commonBorel ![K,U] S)) =
      Nat.card (pCore 2 (commonBorel ![K,U] S)) :=
    card_map_of_injective (commonBorel ![K,U] S).subtype_injective
  have hs := h.mixed_sylow_card_le_twice_borel_core eK eU
  rw [← hmap] at hs
  omega

end CFSG.Quasithin.ChapterF.Source.MixedDGS
