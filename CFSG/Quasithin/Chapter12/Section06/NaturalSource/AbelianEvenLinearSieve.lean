module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianClassicalSieve
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalLinearThreeParity
/-!
# The reduced component catalogue after excluding odd-degree PSL₃

The normal PSL₃ row now has even defining-field exponent. Both original
quotient carriers keep the same parameter. The PSL₂(4), unitary and
special degree-three rows retain their existing precise models and
central-cover congruence. The exchanged PSL₂(4) alternative retains all
its Borel, torus, full-core and residual markings.

This is a refinement of the original reduced-actor application of
12.6.31, not its complete conclusion. Unitary restrictions, reduction of
the remaining linear degree to two, and the subsequent module and terminal
exclusions are still required. SourceInputs and the universal
NaturalReduction interface remain unchanged.

Source: Aschbacher--Smith 12.6.31, printed pp.835--837, refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components

/-- The classical rows with odd-degree PSL₃ excluded; both original quotient
carriers retain the same signed parameter and central-cover congruence. -/
inductive AbelianNormalEvenLinearModels (X Y : Type*) [Group X] [Group Y] : Prop
  | linear_two (left : ClassicalGroup.IsPSL X 2 4) (right : ClassicalGroup.IsPSL Y 2 4)
  | projective_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
      (linear_even : unitary = false → Even n)
      (left : Chapter1.Section02.LocalModels.IsPSLSign X unitary 3 (2^n))
      (right : Chapter1.Section02.LocalModels.IsPSLSign Y unitary 3 (2^n))
  | special_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
      (hmod : (2 ^ n) % 3 = if unitary then 2 else 1)
      (left : Chapter1.Section02.LocalModels.IsSLSign X unitary 3 (2^n))
      (right : Chapter1.Section02.LocalModels.IsSLSign Y unitary 3 (2^n))
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


include hz hTz hTV hbound hTI hns hH hKH hK hgen in
/-- The normal source branch has even degree whenever its projective
three-dimensional carrier is linear. -/
theorem SourceHypothesis.original_abelian_normal_evenLinear_models
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L) :
    AbelianNormalEvenLinearModels (K ⧸ pCore 2 K) (actorImage H K) := by
  have hm := S.original_abelian_normal_classical_models D hZ z hz hTz hTV hbound hTI hns
    hH hKH hK hgen hn hout
  cases hm with
  | linear_two hl hr => exact .linear_two hl hr
  | projective_three unitary n hn2 hl hr =>
    refine .projective_three unitary n hn2 ?_ hl hr
    intro hlinear
    subst unitary
    exact S.original_abelian_normal_linearThree_even D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hl
  | special_three unitary n hn2 hmod hl hr =>
    exact .special_three unitary n hn2 hmod hl hr

include hz hTz hTV hbound hTI hns hH in
/-- Apply the odd-degree PSL₃ exclusion to the original reduced actor,
preserving the complete exchanged-row markings and both quotient carriers. -/
theorem SourceHypothesis.original_abelian_reduced_evenLinear_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianNormalEvenLinearModels (K ⧸ pCore 2 K)
            (Chapter13.Section08.Source.starImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage J K) 2 4 ∧
          (primeToResidual 3 J).map J.subtype = K₀ ∧
          (D.fullSetup hZ T z).L₁ ≤ K₀ ⊓ M L ∧
          K₀ ⊔ (T : Subgroup G) = J ∧
          J ⊓ M L = (K₀ ⊓ M L) ⊔ (T : Subgroup G) ∧
          Group.IsSolvable (K₀ ⊓ M L : Subgroup G) ∧
          primeRank 3 (K₀ ⊓ M L : Subgroup G) = 2 ∧
          (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
            normalizer ((K₀ ⊓ M L : Subgroup G) : Set G) ∧
          (T : Subgroup G) ⊓ K₀ ≤ (D.fullSetup hZ T z).R₁ ∧
          ExchangedTorusAction J K (D.fullSetup hZ T z).L₁ T L (M L) 2 (by decide))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_classical_models D hZ z hz hTz hTV hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with ⟨hn,_⟩ | hexchanged
  · have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
      (le_sup_left.trans (le_sup_left :
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
          conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    exact Or.inl ⟨hn,S.original_abelian_normal_evenLinear_models D hZ z hz hTz hTV
      hbound hTI hns hJ hKle hKJ rfl hn hout⟩
  · exact Or.inr hexchanged
end CFSG.Quasithin.Chapter12.Section06
