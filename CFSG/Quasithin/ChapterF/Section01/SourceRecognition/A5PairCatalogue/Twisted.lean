module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Transport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Filters
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.LocalStructure
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LocalGeometry
public import Theory.GroupTheory.PCoreSectionCard
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders

/-!
# Excluding the four twisted rows at the original A5 pair

Both original A5 quotient markings give Borel index five. The genuine DGS
reduction preserves this index, and the two commuting squares transport it
through the supplied model isomorphism. The triality arms index is at least
nine. The positive Ree linear index is at least nine, while both binary Ree
parabolics are solvable. Generated quasithinness first sieves the arbitrary
unitary-five parameter to four; the native plane index seventeen then excludes
that row without enlarging quasithinness to the ambient group.

For unitary four, the perfect plane factor maps into the original factor via
the reduced parabolic's solvable residual. Its two-core quotient therefore
has order dividing sixty. The actual SL2 quotient forces the binary parameter,
where the opposite point parabolic has Borel index three instead of five.
This uses neither original-factor perfectness nor an original model marking.

All four exclusions retain both orientations and the full reduced Borel.
The ordinary G2 extension remains a separate core-control obligation.
Source: Aschbacher--Smith F.1.12(I)(4)--(7), printed pp.262--264;
DGS Theorem A and (15.2), printed pp.99--100 and 226--228.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
open DGS85.OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full original Borel has index five at an A5-marked endpoint. -/
theorem borel_index (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    (commonBorel L S).relIndex (parabolic L S i) = 5 := by
  rw [parabolic_eq_sup_commonBorel,
    relIndex_sup_of_normalizes _ _ (h.commonBorel_normalizes_local i),
    ←inf_relIndex_right, inf_comm, h.local_inf_commonBorel i]
  exact (h.a5_borel_local_indices i a).1

/-- The same index after reduction, expressed as an endpoint/overlap order identity. -/
theorem reduced_endpoint_card (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    Nat.card (parabolic L (reducedSylow L S) i) =
      Nat.card (commonBorel L (reducedSylow L S)) * 5 := by
  have hc := ((commonBorel L (reducedSylow L S)).subgroupOf
    (parabolic L (reducedSylow L S) i)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (commonBorel_le_parabolic i)).toEquiv] at hc
  change _ * (commonBorel L (reducedSylow L S)).relIndex
    (parabolic L (reducedSylow L S) i) = _ at hc
  rw [borel_index (reduced_hypothesis h) i a] at hc
  exact hc.symm

/-- Both full native Borel indices are five under the actual reduced comparison. -/
theorem model_indices (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] [Finite X] {P B Q : Subgroup X}
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (e : Iso (reducedAmalgam L S) (ofSubgroups P B Q hBP hBQ)) :
    B.relIndex P = 5 ∧ B.relIndex Q = 5 := by
  have hl := reduced_endpoint_card h 0 (a 0).some
  have hr := reduced_endpoint_card h 1 (a 1).some
  rw [Nat.card_congr e.left.toEquiv, Nat.card_congr e.middle.toEquiv] at hl
  rw [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hr
  have hcl := (B.subgroupOf P).card_mul_index
  have hcr := (B.subgroupOf Q).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv, hl] at hcl
  rw [Nat.card_congr (subgroupOfEquivOfLe hBQ).toEquiv, hr] at hcr
  exact ⟨Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B)) hcl,
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B)) hcr⟩

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics in
/-- The arms Borel index excludes every positive triality degree in either orientation. -/
theorem not_triality (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (m : ℕ) (hm : 0<m) (b : Bool)
    (e : Iso (reducedAmalgam L S) (TrialityNative.amalgam m hm b)) : False := by
  have hh := model_indices h a _ _ e
  have hi : (Parabolics.borel (binaryParameters m hm)).relIndex
      (Parabolics.parabolic (binaryParameters m hm) .arms) = 5 := by
    cases b
    · exact hh.1
    · exact hh.2
  rw [OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hi
  change (2^m)^3 + 1 = 5 at hi
  have htwo : 2 ≤ 2^m := show 2^1 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm
  have hlo : 2^3 ≤ (2^m)^3 := Nat.pow_le_pow_left htwo 3
  omega

open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds in
/-- The binary solvability and positive linear index exclude every Ree parameter. -/
theorem not_ree (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (m : ℕ) (b : Bool)
    (e : Iso (reducedAmalgam L S) (ReeNative.amalgam m b)) : False := by
  by_cases hm : m = 0
  · subst m
    let := Chapter6.Source.RankOneGeneric.Global.ReeComparison.binary_parabolic_solvable
      (ReeNative.side b)
    exact overgroup_not_solvable 0 (a 0).some (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)
  · have hh := model_indices h a _ _ e
    have hi : (Parabolics.borel m).relIndex (Parabolics.parabolic m .linear) = 5 := by
      cases b
      · exact hh.1
      · exact hh.2
    rw [SourceCompletion.borel_relIndex m (by omega), if_pos rfl] at hi
    have hlo : 2^3 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- The generated-group quasithin sieve and native plane index exclude all U5 rows. -/
theorem not_unitaryFive (h : HypothesisF11 L S)
    (hqt : IsQuasithin (generated L S))
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : GreenBook.UnitaryFive.Model q) (b : Bool)
    (e : Iso (reducedAmalgam L S) (UnitaryFiveNative.amalgam M b)) : False := by
  have hP (i : Fin 2) : parabolic L (reducedSylow L S) i ≤ generated L S := by
    apply (reduced_parabolic_le h i).trans
    rw [← parabolics_generate L S]
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hq4 : q = 4 := by
    cases b
    · exact M.field_size_eq_four_of_parabolic_embedding hq heven hqt
        ((inclusion (hP 1)).comp e.right.symm.toMonoidHom)
        ((inclusion_injective (hP 1)).comp e.right.symm.injective)
    · exact M.field_size_eq_four_of_parabolic_embedding hq heven hqt
        ((inclusion (hP 0)).comp e.left.symm.toMonoidHom)
        ((inclusion_injective (hP 0)).comp e.left.symm.injective)
  subst q
  have hh := model_indices h a _ _ e
  have hi : M.overlap.relIndex M.rightParabolic = 5 := by
    cases b
    · exact hh.1
    · exact hh.2
  have hj := M.overlap_rightParabolic_index
  change M.overlap.relIndex M.rightParabolic = 17 at hj
  omega

/-- A perfect model subgroup enters the original factor through the reduced residual. Its core quotient retains the original order bound. -/
theorem perfect_model_quotient_dvd_sixty (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    {X : Type*} [Group X] [Finite X]
    (e : parabolic L (reducedSylow L S) i ≃* X)
    (J : Subgroup X) [Group.IsPerfect J] : Nat.card (J ⧸ pCore 2 J) ∣ 60 := by
  let P := parabolic L (reducedSylow L S) i
  let f : J →* P := e.symm.toMonoidHom.comp J.subtype
  have hf : f.range ≤ solvableResidual P := by
    rw [MonoidHom.range_eq_map, ← solvableResidual_eq_top (G := J)]
    exact map_solvableResidual_le f
  let g : J →* L i := (P.subtype.comp f).codRestrict (L i) (fun x =>
    (reduced_hypothesis h).parabolic_residual_le_local i
      (mem_map_of_mem P.subtype (hf (show f x ∈ f.range from ⟨x,rfl⟩))))
  have hg : Function.Injective g := by
    intro x y heq
    apply J.subtype_injective
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : L i => (z : G)) heq
  have hd := g.card_corefree_quotient_dvd_of_embedding hg
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)
    (pCore_quotient_pCore_eq_bot (G := J) 2)
  rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd
  exact hd

open GreenBook.LieModels.UnitaryFour in
/-- The actual plane quotient forces the binary U4 parameter; its opposite Borel index then gives a contradiction. -/
theorem not_unitaryFour (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (m : ℕ) (hm : 1 ≤ m) (b : Bool)
    (e : Iso (reducedAmalgam L S) (UnitaryFourNative.amalgam m hm b)) : False := by
  have hcard : Nat.card (L2 m hm ⧸ pCore 2 (L2 m hm)) ∣ 60 := by
    let := L2_isPerfect m hm
    let J := (L2 m hm).subgroupOf (planeParabolic m hm)
    let j : J ≃* L2 m hm := subgroupOfEquivOfLe (L2_le_planeParabolic m hm)
    let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
      (f := j.symm.toMonoidHom) j.symm.surjective
    have hc : Nat.card (J ⧸ pCore 2 J) = Nat.card (L2 m hm ⧸ pCore 2 (L2 m hm)) :=
      Nat.card_congr (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).toEquiv
    have hd (i : Fin 2) (ei : parabolic L (reducedSylow L S) i ≃* planeParabolic m hm) :
        Nat.card (L2 m hm ⧸ pCore 2 (L2 m hm)) ∣ 60 := by
      rw [← hc]
      exact perfect_model_quotient_dvd_sixty h i (a i).some ei J
    cases b
    · exact hd 0 e.left
    · exact hd 1 e.right
  have hm1 : m = 1 := by
    rw [Nat.card_congr (L2QuotientEquivSL2 m hm).toEquiv, Atlas.card_sl_two,
      GaloisField.card 2 (2*m) (by omega)] at hcard
    by_contra hn
    have hp : 16 ≤ 2^(2*m) := by
      exact show 2^4 ≤ 2^(2*m) from Nat.pow_le_pow_right (by decide) (by omega)
    have hp2 : 255 ≤ (2^(2*m))^2-1 := by
      have hh : 16^2 ≤ (2^(2*m))^2 := Nat.pow_le_pow_left hp 2
      omega
    have hlo : 4080 ≤ 2^(2*m) * ((2^(2*m))^2-1) := Nat.mul_le_mul hp hp2
    have hhi := Nat.le_of_dvd (by decide : 0<60) hcard
    omega
  subst m
  have hc : Nat.card (pointParabolic 1 hm) = Nat.card (overlap 1 hm) * 5 := by
    cases b
    · have hh := reduced_endpoint_card h 1 (a 1).some
      rwa [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hh
    · have hh := reduced_endpoint_card h 0 (a 0).some
      rwa [Nat.card_congr e.left.toEquiv, Nat.card_congr e.middle.toEquiv] at hh
  rw [BinaryCompletion.point_card, BinaryCompletion.middle_card] at hc
  norm_num at hc
end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
