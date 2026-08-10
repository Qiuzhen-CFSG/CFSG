module

public import FeitThompson.BGsection1.Defs
public import FeitThompson.BGsection1.CentralizerLemmas
public import FeitThompson.BGsection1.CriticalSubgroupLemmas
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.Commutator.FocalSubgroup
public import FeitThompson.GroupAction.CentralizerCondition
public import FeitThompson.GroupAction.CoprimeHall
public import FeitThompson.GroupAction.FixedPointTransport
public import FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import FeitThompson.GroupAction.SeriesPiGroup
public import FeitThompson.PCore.CentralizerControl
public import FeitThompson.Burnside.NormalComplement
public import FeitThompson.Commutator.ActionTriviality
public import FeitThompson.Frattini.CoprimeAction
public import FeitThompson.Commutator.CyclicSylow
public import FeitThompson.Commutator.Core
public import FeitThompson.ElementaryAbelian
public import FeitThompson.Fitting.Centralizer
public import FeitThompson.Fitting.Core
public import FeitThompson.Fitting.Faithful
public import FeitThompson.PGroup.NormalSubgroups
public import FeitThompson.PGroup.OmegaFrattini
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import FeitThompson.HallSubgroups.Core
public import FeitThompson.ChiefFactors.BaerCore

open scoped Pointwise

public section

lemma IsPiGroup.of_surjective {π : Set Nat.Primes} {G H : Type*} [Group G] [Finite G] [Group H]
    [Finite H] (hG : IsPiGroup π G) (f : G →* H) (hf : Function.Surjective f) :
    IsPiGroup π H := by
  rw [IsPiGroup_iff π H]
  intro p hp
  exact (IsPiGroup_iff π G).1 hG p (hp.trans (Subgroup.card_dvd_of_surjective f hf))

lemma IsPiGroup.of_injective {π : Set Nat.Primes} {G H : Type*} [Group G] [Finite G] [Group H]
    [Finite H] (hH : IsPiGroup π H) (f : G →* H) (hf : Function.Injective f) :
    IsPiGroup π G := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨by
        intro x y hxy
        exact hf (congrArg Subtype.val hxy)
      , f.rangeRestrict_surjective⟩
  rw [IsPiGroup_iff π G]
  intro p hp
  refine (IsPiGroup_iff π f.range).1 (by
    rw [IsPiGroup_iff π f.range]
    intro q hq
    exact (IsPiGroup_iff π H).1 hH q (hq.trans (Subgroup.card_subgroup_dvd_card f.range))) p ?_
  simpa [Nat.card_congr e.toEquiv] using hp

lemma IsPiGroup.of_equiv {π : Set Nat.Primes} {G H : Type*} [Group G] [Finite G] [Group H]
    [Finite H] (hH : IsPiGroup π H) (e : G ≃* H) :
    IsPiGroup π G :=
  IsPiGroup.of_injective (π := π) (G := G) (H := H) hH e.toMonoidHom e.injective

lemma IsPiSubgroup.isPiGroup {π : Set Nat.Primes} {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : IsPiSubgroup (G := G) π H) :
    IsPiGroup π ↥H := by
  rw [IsPiGroup_iff π ↥H]
  intro p hp
  exact hH p (by simpa using hp)

lemma IsPiGroup.isPiSubgroup {π : Set Nat.Primes} {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : IsPiGroup π ↥H) :
    IsPiSubgroup (G := G) π H := by
  intro p hp
  exact (IsPiGroup_iff π ↥H).1 hH p (by simpa using hp)

lemma IsPiGroup.pi {π : Set Nat.Primes} {α G : Type*} [Finite α] [Group G] [Finite G]
    (hG : IsPiGroup π G) :
    IsPiGroup π (α → G) := by
  rw [IsPiGroup_iff π (α → G)]
  intro p hp
  exact (IsPiGroup_iff π G).1 hG p <|
    p.2.dvd_of_dvd_pow (by simpa [Nat.card_fun] using hp)


lemma IsPiGroup.of_normal_subgroup_and_quotient {π : Set Nat.Primes} {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hH : IsPiSubgroup (G := G) π H)
    (hquot : IsPiGroup π (G ⧸ H)) :
    IsPiGroup π G := by
  rw [IsPiGroup_iff π G]
  intro p hp
  rcases p.2.dvd_mul.mp (by
    rw [← H.card_mul_index, H.index_eq_card] at hp
    exact hp) with hpH | hpquot
  · exact hH p hpH
  · exact (IsPiGroup_iff π (G ⧸ H)).1 hquot p hpquot

lemma IsPiGroup.quotient {π : Set Nat.Primes} {G : Type*} [Group G] [Finite G]
    (hG : IsPiGroup π G) (H : Subgroup G) [H.Normal] :
    IsPiGroup π (G ⧸ H) :=
  IsPiGroup.of_surjective (π := π) (G := G) (H := G ⧸ H) hG
    (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective (N := H))

lemma fixingSubgroupOf_univ_eq_ker_toMulAut {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] :
    fixingSubgroupOf A G (Set.univ : Set G) = (MulDistribMulAction.toMulAut A G).ker := by
  ext a
  rw [MonoidHom.mem_ker, fixingSubgroupOf, mem_fixingSubgroup_iff]
  constructor
  · intro ha
    ext g
    exact ha g (by simp)
  · intro ha g _
    exact DFunLike.congr_fun ha g

theorem centerIn_eq_map_center_local {G : Type*} [Group G] (H : Subgroup G) :
    centerIn H = (Subgroup.center H).map H.subtype := by
  simp [centerIn]
  ext x
  constructor
  · rintro ⟨hxH, hx_centralizer⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun h =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hx_centralizer (h : G) h.property)
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.property, ?_⟩
    intro g hg
    calc
      g * (h : G) = (⟨g, hg⟩ * h : H).val := by simp
      _ = (h * ⟨g, hg⟩ : H).val := by
            rw [Subgroup.mem_center_iff.mp hh ⟨g, hg⟩]
      _ = (h : G) * g := by simp


end
