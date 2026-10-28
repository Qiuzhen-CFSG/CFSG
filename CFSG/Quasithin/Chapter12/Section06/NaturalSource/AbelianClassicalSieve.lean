module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalOuter
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalFour
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedFour
/-!
# The classical component rows after the cyclic outer exclusions

The normal Sp₄′ and G₂′ rows are excluded on the actual reduced actor.
The earlier normal PSL₂ field argument gives PSL₂(4). The surviving
normal alternatives are therefore PSL₂(4) and the signed projective or
special degree-three groups, with the same parameter in both K/O₂(K)
and K-star and the special-group congruence retained.

The original reduced-actor application preserves the escaping relative
C-component, all exchanged PSL₂(4) Borel and torus markings, full-core
containments and quotient maps. Signed degree-three restrictions,
SL₃(4), wreath and terminal module exclusions remain unproved here;
no universal NaturalReduction is inferred from this conditional source
application or from a guarded ambient input.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components

/-- The normal component carriers left after the cyclic outer-action exclusions.
Each row marks both original quotient carriers with the same field parameter. -/
inductive AbelianNormalClassicalModels (X Y : Type*) [Group X] [Group Y] : Prop
  | linear_two (left : ClassicalGroup.IsPSL X 2 4) (right : ClassicalGroup.IsPSL Y 2 4)
  | projective_three (unitary : Bool) (n : ℕ) (hn : 2 ≤ n)
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
/-- The normal source branch retains only PSL₂(4) and signed degree three. -/
theorem SourceHypothesis.original_abelian_normal_classical_models
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L) :
    AbelianNormalClassicalModels (K ⧸ pCore 2 K) (actorImage H K) := by
  obtain ⟨hm,_⟩ := S.original_abelian_normal_lie_models D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hout hgen hn
  let e := (componentStarEquiv H K hKH hK).symm
  cases hm with
  | linear_two n hn2 hm =>
    obtain ⟨hleft,hright,_⟩ := S.original_abelian_normal_linearTwo_four D hZ z hz hTV hTz
      hbound hTI hns hH hKH hK hgen hn hout hn2 hm
    exact .linear_two hleft hright
  | projective_three unitary n hn2 hm =>
    apply AbelianNormalClassicalModels.projective_three unitary n hn2 hm
    cases unitary
    · exact hm.of_mulEquiv e
    · exact hm.of_mulEquiv e
  | special_three unitary n hn2 hmod hm =>
    apply AbelianNormalClassicalModels.special_three unitary n hn2 hmod hm
    cases unitary
    · obtain ⟨F,hF,hfin,hq,⟨a⟩⟩ := hm
      exact ⟨F,hF,hfin,hq,⟨e.trans a⟩⟩
    · obtain ⟨F,hF,hfin,J,hq,hc,⟨a⟩⟩ := hm
      exact ⟨F,hF,hfin,J,hq,hc,⟨e.trans a⟩⟩
  | symplectic n hn2 hm =>
    exact (S.original_abelian_normal_symplectic_impossible D hZ z hz hTV hTz
      hH hKH hK hgen hn hn2 hm).elim
  | g2 n hn2 hm =>
    exact (S.original_abelian_normal_g2_impossible D hZ z hz hTV hTz
      hH hKH hK hgen hn hn2 hm).elim

include hz hTz hTV hbound hTI hns hH in
/-- Apply both cyclic outer exclusions and the normal PSL₂ restriction to the
original reduced actor, preserving the complete exchanged-row markings. -/
theorem SourceHypothesis.original_abelian_reduced_classical_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianNormalClassicalModels (K ⧸ pCore 2 K)
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
    S.original_abelian_reduced_field_four D hZ z hz hTz hTV hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with ⟨hn,_,_⟩ | hexchanged
  · have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
      (le_sup_left.trans (le_sup_left :
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
          conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    exact Or.inl ⟨hn,S.original_abelian_normal_classical_models D hZ z hz hTz hTV
      hbound hTI hns hJ hKle hKJ rfl hn hout⟩
  · exact Or.inr hexchanged
end CFSG.Quasithin.Chapter12.Section06
