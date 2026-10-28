module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedField
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidualMovement
/-!
# Field order four for the original exchanged component

Cubic displacement on the marked Borel torus implies either n = 2 or
[T ∩ L,B] ≤ O₂(B). The original point-stabilizer action rules out the
latter: B contains L₁, and T ∩ L moves L₁/O₂(L₁). Thus the exchanged
PSL₂ component has field order four, without adding an action premise.

Apply this on the same reduced actor J = K₀L₁T. Both K/O₂(K) and K-star
are identified with PSL₂(4), and the relative C-component, exchange,
residual, Borel, Sylow, full-kernel and torus markings are retained.
Earlier geometry stays explicit. Normal Lie-field restrictions, the
remaining module exclusions and universal NaturalReduction are still
separate obligations.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
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
/-- The original exchanged component has binary field exponent two. -/
theorem SourceHypothesis.original_abelian_exchanged_field_eq_two
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) : n = 2 := by
  obtain ⟨ht,halt⟩ := S.original_abelian_exchanged_field_restriction D hZ z hz hTz hTV
    hbound hTI hns hH hKH hK hgen hn hn2 hm
  apply halt.resolve_right
  have hLB : (D.fullSetup hZ T z).L₁ ≤ conjugateSpanBy K (T : Subgroup G) ⊓ M L := by
    obtain ⟨t,ht,hTH,htn,hOH,e,P,hm,hnB,he,hP,hBeq,hMeq,hXB,rest⟩ := ht
    exact hXB.trans_eq hBeq
  exact S.original_point_residual_not_centralized_in_overgroup D hZ z hz hTz _ hLB

include hz hTz hTV hbound hTI hns hH in
/-- The original reduced-actor sieve has only PSL₂(4) in its exchanged row,
retaining both literal quotient models and the complete Borel marking. -/
theorem SourceHypothesis.original_abelian_reduced_field_four :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianLieHigherFieldModel (Chapter13.Section08.Source.starImage J K)) ∨
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
    S.original_abelian_reduced_field_restrictions D hZ z hz hTz hTV hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with hnormal | ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,hcore,ht,hfield⟩
  · exact Or.inl hnormal
  · have hn4 : n = 2 := hfield.resolve_right
      (S.original_point_residual_not_centralized_in_overgroup D hZ z hz hTz _ hLB)
    subst n
    exact Or.inr ⟨hn,hi,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,hcore,ht⟩
end CFSG.Quasithin.Chapter12.Section06
