module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FaithfulApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryApplication
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Moving-center estimates in the original source indices

Identity coordinates on the actual elementary center identify its
representation fixed-space quotient with the original centralizer index.
Consequently the proved linear, Suzuki and unitary estimates use precisely
[A:A∩Q_lambda] and [Z_lambda:C_(Z_lambda)(A)], where
A = V_beta ∩ Q_alpha'. The linear strict inequality gives an actual
faithful natural representation, retaining its original quotient formula.

Source: DGS, *Groups and Graphs* (1985), 8.2--8.7, pp.134--140.
`ReducedModuleEstimates` supplies the literal reduced-source application.
The unitary statements are restricted explicitly to field order at least
four; the source's small unitary and D₁₀ rows remain obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- With identity vector coordinates, the quotient by the fixed space has
exactly the original center's centralizer index. No quotient centralizer is
substituted for a preimage in the original ambient group. -/
theorem center_action_fixed_index {D : Type*} [Group D]
    (L Z A : Subgroup G) [IsElementaryAbelian 2 Z] [Finite Z]
    (hZL : Z ≤ L) (hnZ : L ≤ normalizer (Z : Set G)) (hAL : A ≤ L)
    (q : L →* D) (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (z : Additive Z),
      ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) :
    Nat.card (Additive Z ⧸ fixedSpace ρ ((A.subgroupOf L).map q)) =
      (centralizer (A : Set G)).relIndex Z := by
  have he : commutatorPreimage Z A ⊥ = Z ⊓ centralizer (A : Set G) := by
    apply le_antisymm
    · exact le_inf (commutatorPreimage_le _ _ _)
        (commutator_eq_bot_iff_le_centralizer.mp
          (bot_unique (commutator_commutatorPreimage_le Z A ⊥ le_normalizer_of_normal)))
    · exact le_commutatorPreimage inf_le_left
        (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le
  have hi := (centerSection L Z hZL hnZ q ρ hact).fixed_index_image ρ q A hAL
  rw [he, inf_relIndex_left] at hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact hi.symm

private theorem moving_fixed_index
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {a' beta : Vertex (family P)}
    (w : (graph (family P)).neighborSet a')
    (hAL : V (family P) beta 1 ⊓ Q (family P) a' ≤ d.localGroup w.val)
    {D : Type*} [Group D]
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let A := V (family P) beta 1 ⊓ Q (family P) a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    ∀ ρ : Representation (ZMod 2) D (Additive (Z (family P) w.val)),
      (∀ (l : d.localGroup w.val) (z : Additive (Z (family P) w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Nat.card (Additive (Z (family P) w.val) ⧸ fixedSpace ρ ((A.subgroupOf (d.localGroup w.val)).map q)) =
        (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let : Finite (Z (family P) w.val) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) w.val)) (inclusion_injective _)
  dsimp only
  intro ρ hact
  exact center_action_fixed_index _ _ _
    (pGroup_le_localGroup (family P) d w.val _ (IsElementaryAbelian.isPGroup 2 _)
      (Z_le_stabilizer (family P) w.val))
    ((d.local_le w.val).trans (stabilizer_normalizes_Z (family P) w.val)) hAL _ ρ hact

/-- Linear recognition in the original group indices. The strict comparison
produces the actual quotient action and equivariant natural coordinates. -/
theorem source_moving_linear_index_recognition
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* SL(2,K)) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    (Q F w.val).relIndex A ≤ (centralizer (A : Set G)).relIndex (Z F w.val) ∧
    ((centralizer (A : Set G)).relIndex (Z F w.val) < (Q F w.val).relIndex A ^ 2 →
      ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z F w.val))) (S : Sylow 2 SL(2,K)),
        (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
          ((ρ (e (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)) l)) z).toMul : G) =
            (l : G) * z.toMul * (l : G)⁻¹) ∧
        Function.Injective ρ ∧ NaturalRealization ρ S) := by
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  obtain ⟨ρ, S, hact, _, _, _, hf, _, _, _, hbound, hnat⟩ :=
    source_moving_linear_recognition h d hc hab hd hb hcomm w hm hn hK e
  have hi := moving_fixed_index h d w
    (source_moving_actor h d hc hab hd hb hcomm w hm).2.1 e ρ hact
  rw [hi] at hbound hnat
  exact ⟨hbound, fun hs => ⟨ρ, S, hact, hf, hnat hs⟩⟩

/-- The suzuki square exclusion as an original centralizer-index bound. -/
theorem source_moving_suzuki_index_bound
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    (m : ℕ) (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃*
      SuzukiMatrixGroup m) :
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    (Q F w.val).relIndex A ^ 2 ≤ (centralizer (A : Set G)).relIndex (Z F w.val) := by
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  obtain ⟨ρ, S, hact, _, _, _, _, _, _, _, hbound⟩ :=
    source_moving_suzuki_square_bound h d hc hab hd hb hcomm w hm m e
  have hi := moving_fixed_index h d w
    (source_moving_actor h d hc hab hd hb hcomm w hm).2.1 e ρ hact
  rwa [hi] at hbound

/-- The special unitary square exclusion as an original centralizer-index bound. -/
theorem source_moving_special_unitary_index_bound
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* J.specialSubgroup) :
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    (Q F w.val).relIndex A ^ 2 ≤ (centralizer (A : Set G)).relIndex (Z F w.val) := by
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  obtain ⟨ρ, S, hact, _, _, _, _, _, _, _, hbound⟩ :=
    source_moving_special_unitary_square_bound h d hc hab hd hb hcomm w hm J hn hK hconj e
  have hi := moving_fixed_index h d w
    (source_moving_actor h d hc hab hd hb hcomm w hm).2.1 e ρ hact
  rwa [hi] at hbound

/-- The projective unitary square exclusion as an original centralizer-index bound. -/
theorem source_moving_projective_unitary_index_bound
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    (Q F w.val).relIndex A ^ 2 ≤ (centralizer (A : Set G)).relIndex (Z F w.val) := by
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  obtain ⟨ρ, S, hact, _, _, _, _, _, _, _, _, hbound⟩ :=
    source_moving_projective_unitary_square_bound h d hc hab hd hb hcomm w hm J hn hK hconj e
  have hi := moving_fixed_index h d w
    (source_moving_actor h d hc hab hd hb hcomm w hm).2.1 e ρ hact
  rwa [hi] at hbound

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
