module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryLocal
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SolvableNineAction
/-!
# The binary unitary overgroup has order 72 or 144

The actual normal original factor and U generate the whole local closure.
Its factor index divides a power of two, and the SAME panel-action map
preserves this property. For a binary SU₃ or PSU₃ factor, the faithful
factor image is the proved normal PSU₃(2) of order 72. The solvable
nine-point action has order dividing 432, so its index is one or two.

This removes the unconstrained solvable-overgroup possibility while
retaining the index-two exception. The scalar kernel for SU₃ is removed
by the previously proved literal special-to-projective map; no perfectness
or (2B) is assumed. BinaryUnitaryApplications consumes both model branches.
Source: Fong--Seitz I (2A)--(2B), pp.7--9; (5B)--(5C), pp.25--26;
DGS (6.1), pp.118--119; Aschbacher--Smith F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

/-- The original factor image has two-power index in the whole local action. -/
theorem factor_local_index_two_power :
    ∃ k : ℕ, (factorQuotientLocalMap Q e h split i).range.index = 2^k := by
  let A := (factorMap Q e i).range
  let C := localClosure Q split i
  let F := A.subgroupOf C
  let U := split.U.subgroupOf C
  let f := (localAction Q split i).rangeRestrict
  let : F.Normal := normal_subgroupOf_of_le_normalizer
    ((localClosure_le_parabolic Q split i).trans (factor_parabolic_normalizes Q e h i))
  have hr : (factorIntoClosure Q e h split i).range = F := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a,(factorIntoClosure_coe Q e h split i a).symm⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,Subtype.ext ((factorIntoClosure_coe Q e h split i a).trans ha)⟩
  have he : (factorQuotientLocalMap Q e h split i).range = F.map f := by
    rw [← hr, ← MonoidHom.range_comp]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (L i)) z
      exact ⟨a,Subtype.ext (factorQuotientLocalMap_mk Q e h split i a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 (L i)) a,
        Subtype.ext (factorQuotientLocalMap_mk Q e h split i a)⟩
  have hsup : F ⊔ U = ⊤ := by
    rw [← subgroupOf_sup (factor_le_localClosure Q e h split i)
      (show split.U ≤ C from le_sup_left),factor_sup_unipotent Q e h split i]
    exact subgroupOf_self C
  have hidx : F.index = F.relIndex U := by
    have hh := relIndex_sup_left U F
    rwa [hsup,relIndex_top_right] at hh
  obtain ⟨n,hn⟩ := split.isTwo.exists_card_eq
  have hdiv : (factorQuotientLocalMap Q e h split i).range.index ∣ 2^n := by
    rw [he]
    apply (F.index_map_dvd (localAction Q split i).rangeRestrict_surjective).trans
    rw [hidx]
    have hd := relIndex_dvd_card F U
    have hc : Nat.card U = Nat.card split.U :=
      Nat.card_congr (subgroupOfEquivOfLe (show split.U ≤ C from le_sup_left)).toEquiv
    rwa [hc,hn] at hd
  obtain ⟨k,hk,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  exact ⟨k,heq⟩

private theorem binary_factor_local_order
    (hs : Group.IsSolvable (localGroup Q split i))
    (hp : Nat.card (Panel Q i) = 9)
    (ha : Nat.card (factorQuotientLocalMap Q e h split i).range = 72) :
    Nat.card (localGroup Q split i) = 72 ∨ Nat.card (localGroup Q split i) = 144 := by
  have hd := localGroup_card_dvd_432 Q split i hs hp
  have hb := Nat.le_of_dvd (by decide : 0 < 432) hd
  obtain ⟨k,hk⟩ := factor_local_index_two_power Q e h split i
  have he := (factorQuotientLocalMap Q e h split i).range.index_mul_card
  rw [ha,hk] at he
  have hk3 : k < 3 := by
    by_contra! hh
    have hpow : 2^3 ≤ 2^k := Nat.pow_le_pow_right (by decide) hh
    nlinarith
  interval_cases k
  · left; norm_num at he; exact he.symm
  · right; norm_num at he; exact he.symm
  · norm_num at he
    rw [← he] at hd
    norm_num at hd

open HermitianForm
variable [Finite (L i)] (T : Sylow 2 (L i))
  (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hc : Nat.card E = 2^2) (hconj : ∀ x, J.conj x = x^2)

include e h hT hc hconj in
/-- The actual binary projective local action has order 72 or 144. -/
theorem binary_projectiveUnitary_local_order
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nat.card (localGroup Q split i) = 72 ∨ Nat.card (localGroup Q split i) = 144 := by
  obtain ⟨hs,hp,hi,hn,ha⟩ := binary_projectiveUnitary_local Q e h split i T hT J hc hconj μ
  rw [projectiveUnitaryFactorLocalMap_range] at ha
  exact binary_factor_local_order Q e h split i hs hp ha

include e h hT hc hconj in
/-- The scalar-cover branch has the same two possibilities for its faithful local image. -/
theorem binary_specialUnitary_local_order
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    Nat.card (localGroup Q split i) = 72 ∨ Nat.card (localGroup Q split i) = 144 := by
  obtain ⟨hs,hp,hi,hn,ha⟩ := binary_specialUnitary_local Q e h split i T hT J hc hconj ν
  rw [specialUnitaryFactorLocalMap_range] at ha
  exact binary_factor_local_order Q e h split i hs hp ha
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

