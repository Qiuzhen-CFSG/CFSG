module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianUnitaryThreeSieve
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalProjectiveExclusions
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalSpecialUnitary
/-!
# Only linear models remain in the original component catalogue

The full quadratic actor excludes PSU₃(8), completing the projective-unitary
exclusion. In the special-unitary row, cubic Borel displacement gives
root-inner action, and the original residual E₉ cannot fit in the scalar
center. The normal rows are now PSL₂(4), PSL₃(2ⁿ) and SL₃(2ⁿ), with n even.
The same quadratic obstruction also excludes the projective field-four row,
so its even degree is at least four. Both literal quotient carriers and
every exchanged PSL₂(4) marking remain.
The linear field-size reduction and later module and terminal exclusions
still belong to the source assembly; this is not the universal natural reduction.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components

/-- The normal rows after excluding both unitary carriers. -/
inductive AbelianNormalLinearModels (X Y : Type*) [Group X] [Group Y] : Prop
  | linear_two (left : ClassicalGroup.IsPSL X 2 4) (right : ClassicalGroup.IsPSL Y 2 4)
  | projective_three (n : ℕ) (hn : 4 ≤ n) (degree : Even n)
      (left : ClassicalGroup.IsPSL X 3 (2^n))
      (right : ClassicalGroup.IsPSL Y 3 (2^n))
  | special_three (n : ℕ) (hn : 2 ≤ n) (degree : Even n)
      (left : Chapter1.Section02.LocalModels.IsSL X 3 (2^n))
      (right : Chapter1.Section02.LocalModels.IsSL Y 3 (2^n))
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
/-- Both original quotient carriers lie in the remaining linear rows. -/
theorem SourceHypothesis.original_abelian_normal_linear_models
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L) :
    AbelianNormalLinearModels (K ⧸ pCore 2 K) (actorImage H K) := by
  have hm := S.original_abelian_normal_unitaryThree_models D hZ z hz hTz hTV hbound hTI hns
    hH hKH hK hgen hn hout
  cases hm with
  | linear_two hl hr => exact .linear_two hl hr
  | projective_three unitary n hn2 hdegree hl hr =>
    cases unitary
    · have hn4 : 4 ≤ n := by
        have hnne : n ≠ 2 := by
          intro he
          subst n
          exact S.original_abelian_normal_linearThreeFour_excluded D hZ z hz hTV hTz
            hbound hTI hns hH hKH hK hgen hn hl
        have heven := Nat.even_iff.mp hdegree
        omega
      exact .projective_three n hn4 hdegree hl hr
    · exact (S.original_abelian_normal_unitaryThree_excluded D hZ z hz hTV hTz
        hbound hTI hns hH hKH hK hgen hn hout hn2 hl).elim
  | special_three unitary n hn2 hmod hl hr =>
    have hpar := Nat.BinaryTorusParity.two_pow_mod_three n
    cases unitary
    · have he : Even n := by
        apply Nat.even_iff.mpr
        change 2^n % 3 = 1 at hmod
        split_ifs at hpar <;> omega
      exact .special_three n hn2 he hl hr
    · have ho : Odd n := by
        apply Nat.odd_iff.mpr
        change 2^n % 3 = 2 at hmod
        split_ifs at hpar <;> omega
      exact (S.original_abelian_normal_specialUnitaryThree_odd_excluded D hZ z hz hTV hTz
        hbound hTI hns hH hKH hK hn hout hn2 ho hl).elim

include hz hTz hTV hbound hTI hns hH in
/-- Remove both unitary rows from the original reduced actor,
preserving the complete exchanged-row markings and both quotient carriers. -/
theorem SourceHypothesis.original_abelian_reduced_linear_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianNormalLinearModels (K ⧸ pCore 2 K)
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
    S.original_abelian_reduced_unitaryThree_models D hZ z hz hTz hTV hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with ⟨hn,_⟩ | hexchanged
  · have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
      (le_sup_left.trans (le_sup_left :
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
          conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    exact Or.inl ⟨hn,S.original_abelian_normal_linear_models D hZ z hz hTz hTV
      hbound hTI hns hJ hKle hKJ rfl hn hout⟩
  · exact Or.inr hexchanged
end CFSG.Quasithin.Chapter12.Section06
