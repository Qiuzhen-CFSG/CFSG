module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitary
public import Theory.GroupTheory.SylowMarkedCenterLifting
public import Theory.SpecificGroups.SU3.QuinticSylow
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# From the quotient root placement to the original quintic marking

The original PSL₂(4) quotient supplies an actual order-five subgroup of
K₂. The unitary model makes every quotient Sylow five-group extraspecial
of order 125. The original component two-core is prime to five, so a quotient
Sylow whose center lies in the image of K₂ lifts to a Sylow in the original
component with its center inside K₂. Both original subtype maps are retained
when embedding this group into G.

`UnitaryFiveQuotientPlacement` is the remaining geometric construction target.
It is not deduced merely from an abstract PSU₃(5) isomorphism: its producer
must use the original local configuration and the nontrivial R₂ quotient
action. The last theorem applies the lifted marking to the existing index
contradiction, retaining the independent parabolic fixed-index bound.

Source: Aschbacher--Smith, conclusion of original 4.3.2, printed p.618
(PDF p.635), following 4.3.11--16 on pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The original component inclusion, through the original root normalizer. -/
abbrev unitaryComponentEmbedding (s : SecondaryData c n) : s.component →* G :=
  (rootNormalizer c).subtype.comp s.component.subtype

/-- The remaining geometric placement in the literal two-core quotient.
The quotient image of K₂ must contain the center of an actual Sylow five-group. -/
def UnitaryFiveQuotientPlacement (s : SecondaryData c n) : Prop :=
  ∃ P : Sylow 5 (s.component ⧸ pCore 2 s.component),
    (center P).map (P : Subgroup _).subtype ≤
      ((secondary c).comap (unitaryComponentEmbedding s)).map
        (QuotientGroup.mk' (pCore 2 s.component))

private theorem quotient_sylow_structure (s : SecondaryData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (P : Sylow 5 (s.component ⧸ pCore 2 s.component)) :
    IsExtraspecial 5 P ∧ Nat.card P = 5 ^ 3 := by
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hunitary
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let d : P ≃* P' := (P : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨he, hcard⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylow.extraspecial_card J hF hc P'
  exact ⟨IsExtraspecial.of_mulEquiv d.symm he, (Nat.card_congr d.toEquiv).trans hcard⟩

/-- Lift the actual quotient center into K₂ and retain the original component Sylow.
Only the quotient placement remains a geometric premise. -/
theorem unitaryFive_marking_of_quotient_placement (s : SecondaryData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hplace : UnitaryFiveQuotientPlacement s) : Nonempty (UnitaryFiveMarking s) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let f := QuotientGroup.mk' (pCore 2 s.component)
  have hker : Nat.Coprime 5 (Nat.card f.ker) := by
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := s.component)).exists_card_eq
    rw [QuotientGroup.ker_mk', hk]
    exact (by decide : Nat.Coprime 5 2).pow_right k
  obtain ⟨P, hP⟩ := hplace
  obtain ⟨Q, hQP, hQZ⟩ := exists_sylow_center_le_of_coprime f
    (QuotientGroup.mk'_surjective _) hker
    ((secondary c).comap (unitaryComponentEmbedding s)) P hP
  let e : Q ≃* P :=
    (MulEquiv.ofBijective (f.subgroupMap (Q : Subgroup s.component)) ⟨by
      intro x y hxy
      exact injective_comp_subtype_of_coprime_ker f hker _ Q.isPGroup'
        (congrArg Subtype.val hxy), f.subgroupMap_surjective _⟩).trans
      (MulEquiv.subgroupCongr hQP)
  obtain ⟨hPe, hPc⟩ := quotient_sylow_structure s hunitary P
  let i := unitaryComponentEmbedding s
  have hi : Function.Injective i :=
    (rootNormalizer c).subtype_injective.comp s.component.subtype_injective
  let A := (Q : Subgroup s.component).map i
  let a : Q ≃* A := (Q : Subgroup s.component).equivMapOfInjective i hi
  refine ⟨{
    actor := A
    le_component := ?_
    extraspecial := IsExtraspecial.of_mulEquiv (e.symm.trans a) hPe
    card := (Nat.card_congr (e.symm.trans a).toEquiv).symm.trans hPc
    center_le_secondary := ?_
    sylow := ⟨Q, by rw [map_map]⟩ }⟩
  · change (Q : Subgroup s.component).map
      ((rootNormalizer c).subtype.comp s.component.subtype) ≤ _
    rw [← map_map]
    exact map_mono (map_subtype_le _)
  · rw [← map_embeddedCenter (Q : Subgroup s.component) i hi]
    exact (map_mono hQZ).trans (map_comap_le _ _)

/-- The literal secondary subgroup contains an order-five subgroup. -/
theorem unitaryFive_exists_secondary_quintic (s : SecondaryData c 2) :
    ∃ X : Subgroup G, X ≤ secondary c ∧ Nat.card X = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := s.secondary_model
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 from hF)
  have hcard : Nat.card (secondary c ⧸ pCore 2 (secondary c)) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv, nat_card_alternatingGroup]
    norm_num
  have hd : 5 ∣ Nat.card (secondary c) :=
    (show 5 ∣ Nat.card (secondary c ⧸ pCore 2 (secondary c)) by
      rw [hcard]; decide).trans
        (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (secondary c)))
          (QuotientGroup.mk'_surjective _))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := secondary c) 5 hd
  refine ⟨(zpowers x).map (secondary c).subtype, map_subtype_le _, ?_⟩
  rw [card_map_of_injective (secondary c).subtype_injective, Nat.card_zpowers, hx]


/-- The existing chief-factor contradiction now needs only placement in the quotient
and the independent bound on the original R₂. -/
theorem unitaryFive_false_of_quotient_placement_and_bound (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hplace : UnitaryFiveQuotientPlacement s) (hbound : QuinticRadicalBound c) : False := by
  obtain ⟨m⟩ := unitaryFive_marking_of_quotient_placement s hunitary hplace
  exact unitaryFive_false_of_marking_and_bound s D h m hbound

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
