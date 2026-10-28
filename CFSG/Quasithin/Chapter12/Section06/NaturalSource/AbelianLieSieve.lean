module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianMathieu
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianGroupSieve
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiComplete

/-!
# The remaining Lie component carriers in the original abelian branch

The original normal component's concrete F.9.18 list now loses both
Mathieu rows and the Suzuki row. Its remaining carriers are binary PSL₂,
signed projective or special degree three, Sp₄′ and G₂′, each with field
exponent at least two. The exchanged list loses Suzuki and retains binary
PSL₂ or PSL₃(2). All statements include genuine group isomorphisms.

The final application constructs the same escaping K and reduced actor
J=K₀L₁T in Hz. It preserves relative normality, the exchanged normalizer
index, and both K/O₂(K) and K-star. It does not identify K₀ with O²(J).
The exchanged binary row, field restrictions, actual Borel and module
identifications, SL₃(4) and wreath exclusions and universal NaturalReduction
remain source obligations.

Source: Aschbacher--Smith 12.6.30--31, printed pp.835--837, using F.9.18(4--5).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)

/-- The surviving normal-component carriers, retaining their exact models
and the signed degree-three central-cover congruence. -/
inductive AbelianLieHigherFieldModel (X : Type*) [Group X] : Prop
  | linear_two (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL X 2 (2 ^ n))
  | projective_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
      (iso : Chapter1.Section02.LocalModels.IsPSLSign X unitary 3 (2 ^ n))
  | special_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
      (hmod : (2 ^ n) % 3 = if unitary then 2 else 1)
      (iso : Chapter1.Section02.LocalModels.IsSLSign X unitary 3 (2 ^ n))
  | symplectic (n : ℕ) (hn : 2 ≤ n) (iso : Models.IsSp4DerivedAt X (2 ^ n))
  | g2 (n : ℕ) (hn : 2 ≤ n) (iso : Models.IsG2DerivedAt X (2 ^ n))
/-- The intrinsic and literal star quotients carry the same remaining rows. -/
private theorem AbelianLieHigherFieldModel.of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (h : AbelianLieHigherFieldModel Y) (e : X ≃* Y) : AbelianLieHigherFieldModel X := by
  cases h with
  | linear_two n hn hm => exact .linear_two n hn (hm.of_mulEquiv e)
  | projective_three unitary n hn hm =>
    apply AbelianLieHigherFieldModel.projective_three unitary n hn
    cases unitary
    · exact ClassicalGroup.IsPSL.of_mulEquiv hm e
    · exact ClassicalGroup.IsPSU.of_mulEquiv hm e
  | special_three unitary n hn hmod hm =>
    apply AbelianLieHigherFieldModel.special_three unitary n hn hmod
    cases unitary
    · obtain ⟨F,hF,hfin,hq,⟨a⟩⟩ := hm
      exact ⟨F,hF,hfin,hq,⟨e.trans a⟩⟩
    · obtain ⟨F,hF,hfin,J,hq,hc,⟨a⟩⟩ := hm
      exact ⟨F,hF,hfin,J,hq,hc,⟨e.trans a⟩⟩
  | symplectic n hn hm => exact .symplectic n hn (hm.of_mulEquiv e)
  | g2 n hn hm => exact .g2 n hn (hm.of_mulEquiv e)

include hz hTV hTz hbound hTI hns in
/-- Only genuine higher-field Lie models remain for the normal component.
The Mathieu and Suzuki arguments are applied to this same intrinsic quotient. -/
theorem SourceHypothesis.original_abelian_normal_lie_models
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (hout : ¬ K ≤ M L)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H) (hn : (K.subgroupOf H).Normal) :
    AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
      AbelianLieHigherFieldModel (actorImage H K) := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (show (T : Subgroup G) ≤ H from fun x hx => hH.1.2 (Or.inr hx)).trans
      ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hmodels := (S.original_abelian_normal_higherField_models D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hout hgen hn).1
  have hm : AbelianLieHigherFieldModel (K ⧸ pCore 2 K) := by
    cases hmodels with
    | linear_two n hn he => exact .linear_two n hn he
    | projective_three unitary n hn he => exact .projective_three unitary n hn he
    | special_three unitary n hn hmod he => exact .special_three unitary n hn hmod he
    | symplectic n hn he => exact .symplectic n hn he
    | g2 n hn he => exact .g2 n hn he
    | mathieu he => exact (S.original_escaping_mathieu_impossible D hZ z hz hTV hTz hbound hTI hns
        hH hKH hTK (Or.inl he)).elim
    | mathieu_cover he => exact (S.original_escaping_mathieu_impossible D hZ z hz hTV hTz hbound hTI hns
        hH hKH hTK (Or.inr he)).elim
    | suzuki m hm he =>
        obtain ⟨e⟩ := he
        exact (S.original_abelian_suzuki_impossible D hZ z hz hTV hTz hbound hTI hns
          hH hKH hK hgen (by omega) e).elim
  exact ⟨hm,hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm⟩

include hz hTV hTz hbound hTI hns in
/-- Apply the Mathieu and Suzuki eliminations to the original reduced actor.
The exchanged PSL₃(2) row remains explicit, together with binary PSL₂;
the normal row consists only of the stated higher-field Lie carriers. -/
theorem SourceHypothesis.original_abelian_reduced_lie_models
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (((K.subgroupOf J).Normal ∧
          AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianLieHigherFieldModel (actorImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ((∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
            ClassicalGroup.IsPSL (actorImage J K) 2 (2 ^ n)) ∨
            (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∧
              ClassicalGroup.IsPSL (actorImage J K) 3 2)))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  rcases S.original_abelian_component_model_alternatives D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ rfl with ⟨hn,_,_⟩ | ⟨hn,hi,_,hm⟩
  · exact Or.inl ⟨hn,S.original_abelian_normal_lie_models D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ hout rfl hn⟩
  · refine Or.inr ⟨hn,hi,?_⟩
    rcases hm with ⟨n,hn,he⟩ | ⟨m,hm,⟨e⟩⟩ | he
    · exact Or.inl ⟨n,hn,he,he.of_mulEquiv (componentStarEquiv _ K hKle hKJ).symm⟩
    · exact (S.original_abelian_suzuki_impossible D hZ z hz hTV hTz hbound hTI hns
        hJ hKle hKJ rfl (by omega) e).elim
    · exact Or.inr ⟨he,he.of_mulEquiv (componentStarEquiv _ K hKle hKJ).symm⟩

end CFSG.Quasithin.Chapter12.Section06
