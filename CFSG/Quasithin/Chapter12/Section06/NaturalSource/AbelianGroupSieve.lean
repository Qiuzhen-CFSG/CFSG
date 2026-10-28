module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSmallLie

/-!
# The higher-field normal-component catalogue on the reduced actor

Combine F.9.18's actual component models with the generation-one exclusions.
For a normal escaping component, A₇, binary PSL₃, PSL₄, PSL₅, Sp₄′, G₂′
and the triple cover of A₆ are impossible. The signed degree-three cover
congruence also excludes its binary parameter. Thus every remaining Lie
row has field exponent at least two; the Mathieu and Suzuki rows remain.

The application constructs the same original escaping component and uses
its reduced actor K₀L₁T. It retains relative normality, the index-two
normalizer in the exchanged branch, and both K/O₂(K) and K-star through
the literal quotient equivalence. The exchanged catalogue is unchanged.
This is the first group sieve of 12.6.31, not its full group/module or
Borel-identification conclusion.

Source: Aschbacher--Smith 12.6.30--31, printed pp.835--836, and
F.9.18(4--5), printed pp.325--326.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter15.Section03.AbelianAmalgam.GenerationOne

/-- The remaining normal-component group rows after the generation-one
exclusions in the first paragraph of12.6.31. Each row is an actual group
isomorphism predicate; the module and local subgroup conclusions are separate. -/
inductive AbelianHigherFieldModel (X : Type*) [Group X] : Prop
  | linear_two (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL X 2 (2 ^ n))
  | projective_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
      (iso : Chapter1.Section02.LocalModels.IsPSLSign X unitary 3 (2 ^ n))
  | special_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
      (hmod : (2 ^ n) % 3 = if unitary then 2 else 1)
      (iso : Chapter1.Section02.LocalModels.IsSLSign X unitary 3 (2 ^ n))
  | symplectic (n : ℕ) (hn : 2 ≤ n) (iso : Models.IsSp4DerivedAt X (2 ^ n))
  | g2 (n : ℕ) (hn : 2 ≤ n) (iso : Models.IsG2DerivedAt X (2 ^ n))
  | mathieu (iso : Nonempty (X ≃* Sporadic.Mathieu.M22))
  | mathieu_cover (iso : Nonempty (X ≃* Models.M22Triple))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))

/-- The intrinsic and literal star quotients carry the same remaining rows. -/
theorem AbelianHigherFieldModel.of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (h : AbelianHigherFieldModel Y) (e : X ≃* Y) : AbelianHigherFieldModel X := by
  cases h with
  | linear_two n hn hm => exact .linear_two n hn (hm.of_mulEquiv e)
  | projective_three unitary n hn hm =>
    apply AbelianHigherFieldModel.projective_three unitary n hn
    cases unitary
    · exact ClassicalGroup.IsPSL.of_mulEquiv hm e
    · exact ClassicalGroup.IsPSU.of_mulEquiv hm e
  | special_three unitary n hn hmod hm =>
    apply AbelianHigherFieldModel.special_three unitary n hn hmod
    cases unitary
    · obtain ⟨F,hF,hfin,hq,⟨a⟩⟩ := hm
      exact ⟨F,hF,hfin,hq,⟨e.trans a⟩⟩
    · obtain ⟨F,hF,hfin,J,hq,hc,⟨a⟩⟩ := hm
      exact ⟨F,hF,hfin,J,hq,hc,⟨e.trans a⟩⟩
  | symplectic n hn hm => exact .symplectic n hn (hm.of_mulEquiv e)
  | g2 n hn hm => exact .g2 n hn (hm.of_mulEquiv e)
  | mathieu hm => exact .mathieu (hm.map (e.trans ·))
  | mathieu_cover hm => exact .mathieu_cover (hm.map (e.trans ·))
  | suzuki m hm he => exact .suzuki m hm (he.map (e.trans ·))

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


include hz hTV hTz hbound hTI hns in
/-- The normal escaping component has field exponent greater than one,
or is one of the genuine Mathieu rows. Suzuki remains until its module
argument is supplied. The conclusion concerns the original two-core quotient. -/
theorem SourceHypothesis.original_abelian_normal_higherField_models
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (hout : ¬ K ≤ M L)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H) (hn : (K.subgroupOf H).Normal) :
    AbelianHigherFieldModel (K ⧸ pCore 2 K) ∧
      AbelianHigherFieldModel (actorImage H K) := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (show (T : Subgroup G) ≤ H from fun x hx => hH.1.2 (Or.inr hx)).trans
      ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hb : ∀ {d : ℕ}, d = 3 ∨ d = 4 ∨ d = 5 →
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) d 2 → False :=
    fun {d} => S.original_escaping_binaryLinear_impossible D hZ z hz hTV hTz hbound hTI hns
      hH hKH hTK hout
  have hs := S.original_escaping_smallLie_impossible D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hTK hout
  obtain ⟨_,hc,hseven⟩ := S.original_abelian_normal_component_catalogue D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hout hgen hn
  have hm : AbelianHigherFieldModel (K ⧸ pCore 2 K) := by
    rcases hc with hc | ⟨m,hm,he⟩
    · cases hc with
      | linear_two n hn he => exact .linear_two n hn he
      | projective_three unitary n hn he =>
        have hn2 : 2 ≤ n := by
          cases unitary
          · change 1 ≤ n at hn
            by_contra h
            have heq : n = 1 := by omega
            subst n
            exact hb (Or.inl rfl) (by simpa [Chapter1.Section02.LocalModels.IsPSLSign] using he)
          · exact hn
        exact .projective_three unitary n hn2 he
      | special_three unitary n hn hmod he =>
        have hn2 : 2 ≤ n := by
          cases unitary
          · change 1 ≤ n at hn
            change 2 ^ n % 3 = 1 at hmod
            by_contra h
            have heq : n = 1 := by omega
            subst n
            norm_num at hmod
          · exact hn
        exact .special_three unitary n hn2 hmod he
      | symplectic n hn he =>
        have hn2 : 2 ≤ n := by
          by_contra h
          have heq : n = 1 := by omega
          subst n
          exact hs (Or.inl (by simpa using he))
        exact .symplectic n hn2 he
      | g2 n hn he =>
        have hn2 : 2 ≤ n := by
          by_contra h
          have heq : n = 1 := by omega
          subst n
          exact hs (Or.inr (Or.inl (by simpa using he)))
        exact .g2 n hn2 he
      | linear_four he => exact (hb (Or.inr (Or.inl rfl)) he).elim
      | linear_five he => exact (hb (Or.inr (Or.inr rfl)) he).elim
      | alternating_seven he => exact (hseven he).elim
      | alternating_six_cover he => exact (hs (Or.inr (Or.inr he))).elim
      | mathieu he => exact .mathieu he
      | mathieu_cover he => exact .mathieu_cover he
    · exact .suzuki m hm he
  exact ⟨hm,hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm⟩

include hz hTV hTz hbound hTI hns in
/-- Construct the escaping component and apply the sharpened group sieve
on its literal reduced actor K₀L₁T. Relative normality, the exchanged index,
and both quotient identifications are retained. -/
theorem SourceHypothesis.original_abelian_reduced_higherField_models
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (((K.subgroupOf J).Normal ∧ Models.F918Models (actorImage J K) ∧
          AbelianHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianHigherFieldModel (actorImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          NonnormalF918Models (actorImage J K) ∧ NonnormalF918Models (K ⧸ pCore 2 K))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  rcases S.original_abelian_component_model_alternatives D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ rfl with ⟨hn,hm,_⟩ | hm
  · exact Or.inl ⟨hn,hm,S.original_abelian_normal_higherField_models D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ hout rfl hn⟩
  · exact Or.inr hm

end CFSG.Quasithin.Chapter12.Section06
