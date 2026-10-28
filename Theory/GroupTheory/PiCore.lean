module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.SetTheory.Cardinal.Finite
public import Theory.GroupTheory.Hall.Basic

open scoped Pointwise

/-!
# Pi-groups and pi-cores

This module defines groups whose prime divisors lie in a prescribed set and
the largest normal subgroup with that property. It also provides the standard
transport, normality, characteristic, and closure properties of the pi-core.
-/

/-- A `π`-group (all prime divisors of its order lie in `π`). -/
public def IsPiGroup (π : Set Nat.Primes) (G : Type*) [Group G] : Prop :=
  IsPiSubgroup π (⊤ : Subgroup G)

public lemma IsPiGroup_iff (π : Set Nat.Primes) (G : Type*) [Group G] [Finite G] :
    IsPiGroup π G ↔ ∀ p : Nat.Primes, p.val ∣ Nat.card G → p ∈ π := by
  let _ := (inferInstance : Finite G)
  unfold IsPiGroup IsPiSubgroup
  simp

/-- The `π`-core `𝒪_π(G)`: the supremum of all normal `π`-subgroups of `G`. -/
@[expose]
public def piCore (π : Set Nat.Primes) (G : Type*) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ IsPiSubgroup (G := G) π K}

section PiGroup

public lemma IsPiGroup.of_surjective {π : Set Nat.Primes} {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (hG : IsPiGroup π G) (f : G →* H) (hf : Function.Surjective f) :
    IsPiGroup π H := by
  rw [IsPiGroup_iff π H]
  intro p hp
  exact (IsPiGroup_iff π G).1 hG p (hp.trans (Subgroup.card_dvd_of_surjective f hf))

public lemma IsPiGroup.of_injective {π : Set Nat.Primes} {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (hH : IsPiGroup π H) (f : G →* H) (hf : Function.Injective f) :
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
    exact (IsPiGroup_iff π H).1 hH q
      (hq.trans (Subgroup.card_subgroup_dvd_card f.range))) p ?_
  simpa [Nat.card_congr e.toEquiv] using hp

public lemma IsPiGroup.of_equiv {π : Set Nat.Primes} {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (hH : IsPiGroup π H) (e : G ≃* H) :
    IsPiGroup π G :=
  IsPiGroup.of_injective (π := π) (G := G) (H := H) hH e.toMonoidHom e.injective

public lemma IsPiSubgroup.isPiGroup {π : Set Nat.Primes} {G : Type*}
    [Group G] [Finite G] (H : Subgroup G)
    (hH : IsPiSubgroup (G := G) π H) :
    IsPiGroup π ↥H := by
  rw [IsPiGroup_iff π ↥H]
  intro p hp
  exact hH p (by simpa using hp)

public lemma IsPiGroup.isPiSubgroup {π : Set Nat.Primes} {G : Type*}
    [Group G] [Finite G] (H : Subgroup G)
    (hH : IsPiGroup π ↥H) :
    IsPiSubgroup (G := G) π H := by
  intro p hp
  exact (IsPiGroup_iff π ↥H).1 hH p (by simpa using hp)

public lemma IsPiGroup.pi {π : Set Nat.Primes} {α G : Type*}
    [Finite α] [Group G] [Finite G] (hG : IsPiGroup π G) :
    IsPiGroup π (α → G) := by
  rw [IsPiGroup_iff π (α → G)]
  intro p hp
  exact (IsPiGroup_iff π G).1 hG p <|
    p.2.dvd_of_dvd_pow (by simpa [Nat.card_fun] using hp)

public lemma IsPiGroup.of_normal_subgroup_and_quotient
    {π : Set Nat.Primes} {G : Type*} [Group G] [Finite G]
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

public lemma IsPiGroup.quotient {π : Set Nat.Primes} {G : Type*}
    [Group G] [Finite G] (hG : IsPiGroup π G) (H : Subgroup G) [H.Normal] :
    IsPiGroup π (G ⧸ H) :=
  IsPiGroup.of_surjective (π := π) (G := G) (H := G ⧸ H) hG
    (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective (N := H))

end PiGroup

section PiCore

variable {G : Type*} [Group G]

public lemma IsPiSubgroup.map {G' : Type*} [Group G'] {π : Set Nat.Primes}
    {H : Subgroup G} (hH : IsPiSubgroup (G := G) π H) (f : G →* G') :
    IsPiSubgroup (G := G') π (H.map f) := by
  intro p hp
  exact hH p (hp.trans (Subgroup.card_map_dvd (H := H) f))

public lemma IsPiSubgroup.sup_of_normal_right {π : Set Nat.Primes}
    {H K : Subgroup G} (hH : IsPiSubgroup (G := G) π H)
    (hK : IsPiSubgroup (G := G) π K) [K.Normal] :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  intro p hpSup
  have hmul : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) := by
    simpa using (Subgroup.mul_normal H K)
  have hcard_sup_set :
      Nat.card (↑(H ⊔ K) : Set G) = Nat.card ((H : Set G) * (K : Set G) : Set G) :=
    Nat.card_congr (Equiv.setCongr hmul)
  have hcard_sup :
      Nat.card (↥(H ⊔ K)) = Nat.card ((H : Set G) * (K : Set G) : Set G) := by
    simpa using hcard_sup_set
  have hcard_mul :
      Nat.card ((H : Set G) * (K : Set G) : Set G) =
        Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := K) (t := (H : Set G)))
  have hset_image :
      ((H : Set G).image (↑) : Set (G ⧸ K)) =
        (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcard_image_set :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) :=
    Nat.card_congr (Equiv.setCongr hset_image)
  have hcard_image_subgroup :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K)) := by
    exact hcard_image_set
  have hp_mul :
      p.val ∣ Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    rw [← hcard_mul, ← hcard_sup]
    exact hpSup
  rcases p.2.dvd_mul.mp hp_mul with hpK | hpImg
  · exact hK p hpK
  · have hpMap : p.val ∣ Nat.card (H.map (QuotientGroup.mk' K)) := by
      rwa [hcard_image_subgroup] at hpImg
    exact (hH.map (QuotientGroup.mk' K)) p hpMap

public lemma normalPiSubgroups_nonempty (π : Set Nat.Primes) :
    ({K : Subgroup G | K.Normal ∧ IsPiSubgroup (G := G) π K} :
      Set (Subgroup G)).Nonempty := by
  refine ⟨⊥, ?_⟩
  constructor
  · infer_instance
  · intro p hp
    exfalso
    exact p.2.not_dvd_one (by simpa using hp)

public lemma directedOn_normal_piSubgroups (π : Set Nat.Primes) :
    DirectedOn (· ≤ ·)
      ({K : Subgroup G | K.Normal ∧ IsPiSubgroup (G := G) π K} : Set (Subgroup G)) := by
  intro H hH K hK
  rcases hH with ⟨hHnorm, hHπ⟩
  rcases hK with ⟨hKnorm, hKπ⟩
  refine ⟨H ⊔ K, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · have : H.Normal := hHnorm
    have : K.Normal := hKnorm
    exact Subgroup.sup_normal H K
  · have : K.Normal := hKnorm
    exact hHπ.sup_of_normal_right hKπ

public lemma piCore_map_iso {π : Set Nat.Primes} {G' : Type*} [Group G']
    (f : G ≃* G') :
    (piCore π G).map f.toMonoidHom = piCore π G' := by
  let S : Set (Subgroup G) := {K | K.Normal ∧ IsPiSubgroup (G := G) π K}
  let S' : Set (Subgroup G') := {K' | K'.Normal ∧ IsPiSubgroup (G := G') π K'}
  let F : Subgroup G ≃o Subgroup G' := MulEquiv.mapSubgroup f
  have hImage : F '' S = S' := by
    ext K'
    constructor
    · rintro ⟨K, ⟨hKnorm, hKπ⟩, rfl⟩
      constructor
      · exact Subgroup.Normal.map hKnorm f.toMonoidHom f.surjective
      · change IsPiSubgroup (G := G') π (K.map f.toMonoidHom)
        exact hKπ.map f.toMonoidHom
    · intro hK'
      refine ⟨F.symm K', ?_, ?_⟩
      constructor
      · exact Subgroup.Normal.map hK'.1 f.symm.toMonoidHom f.symm.surjective
      · simpa [F] using hK'.2.map f.symm.toMonoidHom
      · ext x
        simp [F]
  calc
    (piCore π G).map f.toMonoidHom = (sSup S).map f.toMonoidHom := rfl
    _ = F (sSup S) := rfl
    _ = ⨆ K ∈ S, F K := OrderIso.map_sSup F S
    _ = sSup (F '' S) := by simp [sSup_image]
    _ = sSup S' := by rw [hImage]
    _ = piCore π G' := rfl

public instance piCore_characteristic (π : Set Nat.Primes) :
    (piCore π G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  simpa using (piCore_map_iso (G := G) (G' := G) (π := π) φ)

public instance piCore_normal (π : Set Nat.Primes) : (piCore π G).Normal := by
  refine ⟨?_⟩
  intro n hn g
  have hdir := directedOn_normal_piSubgroups (G := G) π
  have hne := normalPiSubgroups_nonempty (G := G) π
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hn) with ⟨K, hK, hnK⟩
  exact Subgroup.mem_sSup_of_mem hK (hK.1.conj_mem n hnK g)

public lemma piCore_isPiSubgroup [Finite G] (π : Set Nat.Primes) :
    IsPiSubgroup (G := G) π (piCore π G) := by
  let S : Set (Subgroup G) := {K | K.Normal ∧ IsPiSubgroup (G := G) π K}
  have hne : S.Nonempty := normalPiSubgroups_nonempty (G := G) π
  have hImageFinite : ((fun L : Subgroup G => Nat.card L) '' S).Finite := by
    refine (Set.finite_Iic (Nat.card G)).subset ?_
    rintro n ⟨K, hK, rfl⟩
    simpa [Set.mem_Iic] using
      (Subgroup.card_le_of_le (show K ≤ (⊤ : Subgroup G) by exact le_top))
  obtain ⟨K, hKmax⟩ :=
    hImageFinite.exists_maximalFor' (f := fun L : Subgroup G => Nat.card L) S hne
  have hKmem : K ∈ S := hKmax.1
  have hpiCore_le : piCore π G ≤ K := by
    intro x hx
    have hdir := directedOn_normal_piSubgroups (G := G) π
    have hne' := normalPiSubgroups_nonempty (G := G) π
    rcases (Subgroup.mem_sSup_of_directedOn hne' hdir).mp hx with ⟨L, hLmem, hxL⟩
    have hsup_mem : L ⊔ K ∈ S := by
      rcases hLmem with ⟨hLnorm, hLπ⟩
      rcases hKmem with ⟨hKnorm, hKπ⟩
      refine ⟨?_, ?_⟩
      · have : L.Normal := hLnorm
        have : K.Normal := hKnorm
        exact Subgroup.sup_normal L K
      · have : K.Normal := hKnorm
        exact hLπ.sup_of_normal_right hKπ
    have hcard_sup_le : Nat.card ↥(L ⊔ K) ≤ Nat.card ↥K := hKmax.le hsup_mem
    have hcard_K_le : Nat.card ↥K ≤ Nat.card ↥(L ⊔ K) :=
      Subgroup.card_le_of_le le_sup_right
    have hcard_eq : Nat.card ↥(L ⊔ K) = Nat.card ↥K :=
      Nat.le_antisymm hcard_sup_le hcard_K_le
    have hsup_eq : L ⊔ K = K := by
      symm
      exact Subgroup.eq_of_le_of_card_ge le_sup_right (by simpa using hcard_sup_le)
    have hL_le_K : L ≤ K := by
      intro y hy
      have hy_sup : y ∈ L ⊔ K := Subgroup.mem_sup_left hy
      simpa [hsup_eq] using hy_sup
    exact hL_le_K hxL
  have hK_le_piCore : K ≤ piCore π G := le_sSup hKmem
  have hEq : piCore π G = K := le_antisymm hpiCore_le hK_le_piCore
  simpa [hEq] using hKmem.2

public lemma le_piCore_of_normal_isPiSubgroup
    (π : Set Nat.Primes) (K : Subgroup G) [K.Normal]
    (hKπ : IsPiSubgroup (G := G) π K) :
    K ≤ piCore π G := by
  exact le_sSup
    (show K ∈ {K : Subgroup G | K.Normal ∧ IsPiSubgroup (G := G) π K} from
      ⟨‹_›, hKπ⟩)

end PiCore
