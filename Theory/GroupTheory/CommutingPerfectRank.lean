module

public import Theory.PGroup
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Sylow

/-!
# Three commuting copies of a perfect group force odd rank three

A nontrivial finite perfect group has a noncentral cyclic subgroup of
odd prime-power order. Choose a maximal subgroup of that cyclic subgroup
containing its intersection with the center. Its quotient has prime order.
For three commuting copies, every relation between the three cyclic factors
has central coordinates. The three prime-order quotients therefore descend
through their multiplication image. This abelian prime-group image has
generator rank at least three, hence witnesses odd prime rank at least three.

This is the model-independent rank step in Aschbacher--Smith A.3.8(3),
printed p.46. The source consumer supplies commutation through A.3.7.
-/

public section
noncomputable section
namespace Theory.GroupTheory.CommutingPerfectRank
open Subgroup
open scoped IsMulCommutative
variable {B G : Type*} [Group B] [Group G]

private theorem exists_noncentral_cyclic_odd_pGroup
    [Finite B] [Nontrivial B] [Group.IsPerfect B] :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ C : Subgroup B,
      IsPGroup p C ∧ IsMulCommutative C ∧ ¬ C ≤ center B := by
  let Q := B ⧸ center B
  let q : B →* Q := QuotientGroup.mk' (center B)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hZ : center B ≠ ⊤ := fun h =>
    Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h)
  have : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hZ
  have : Group.IsPerfect Q := Group.IsPerfect.ofSurjective hq
  have hn : ¬ IsPGroup 2 Q := fun h =>
    Group.IsPerfect.not_isNilpotent Q h.isNilpotent
  have hsub : ¬ (Nat.card Q).primeFactors ⊆ (2 : ℕ).primeFactors := by
    simpa only [← isPGroup_iff_primeFactors_card_subset (G := Q) (by decide : 2 ≠ 0)]
      using hn
  obtain ⟨p, hpQ, hp2⟩ := Finset.not_subset.mp hsub
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hpQ
  have hne : p ≠ 2 := by
    intro he
    apply hp2
    rw [he]
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩
  have : Fact p.Prime := ⟨hp⟩
  let S : Sylow p B := Classical.choice inferInstance
  have hSn : ¬ (S : Subgroup B) ≤ center B := by
    intro hs
    have hb : (S : Subgroup B).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro a ha
      change QuotientGroup.mk' (center B) a = 1
      exact (QuotientGroup.eq_one_iff _).mpr (hs ha)
    exact (S.mapSurjective hq).ne_bot_of_dvd_card hpd
      (by simpa only [Sylow.coe_mapSurjective] using hb)
  obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hSn
  let C := zpowers a
  have hCS : C ≤ (S : Subgroup B) := zpowers_le.mpr ha
  exact ⟨p, hp, hp.odd_of_ne_two hne, C,
    S.isPGroup'.of_injective (inclusion hCS) (inclusion_injective hCS),
    inferInstance, fun hc => hna (hc (mem_zpowers a))⟩

private theorem rotate_eq_one (a b c : G) (h : a * b * c = 1) :
    b * c * a = 1 := by
  calc
    b * c * a = a⁻¹ * (a * b * c) * a := by group
    _ = 1 := by rw [h]; simp

private theorem central_coordinate_of_relation
    (f g h : B →* G) (hf : Function.Injective f)
    (hfg : ∀ x y, Commute (f x) (g y))
    (hfh : ∀ x y, Commute (f x) (h y))
    (x y z : B) (he : f x * g y * h z = 1) : x ∈ center B := by
  have hx : f x = (g y * h z)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp (by simpa only [mul_assoc] using he)
  apply mem_center_iff.mpr
  intro b
  apply hf
  rw [map_mul, map_mul, hx]
  exact ((hfg b y).mul_right (hfh b z)).inv_right.eq

private theorem rank_three_of_noncentral_abelian_pGroup [Finite B] [Finite G]
    {p : ℕ} [Fact p.Prime] (C : Subgroup B) (hCp : IsPGroup p C)
    [IsMulCommutative C] (hCZ : ¬ C ≤ center B)
    (f₀ f₁ f₂ : B →* G)
    (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁)
    (hf₂ : Function.Injective f₂)
    (h₀₁ : ∀ x y, Commute (f₀ x) (f₁ y))
    (h₀₂ : ∀ x y, Commute (f₀ x) (f₂ y))
    (h₁₂ : ∀ x y, Commute (f₁ x) (f₂ y)) : 3 ≤ primeRank p G := by
  let : CommGroup C := IsMulCommutative.instCommGroup
  have : Fact (IsPGroup p C) := ⟨hCp⟩
  let Z : Subgroup C := (center B).comap C.subtype
  have hZ : Z ≠ ⊤ := by
    intro he
    apply hCZ
    intro b hb
    exact (show (⟨b, hb⟩ : C) ∈ Z from he ▸ mem_top _)
  obtain ⟨M, hM, hZM⟩ := (eq_top_or_exists_le_coatom Z).resolve_left hZ
  have : M.Normal := coatom_normal_of_isPGroup (p := p) hM
  let E := C ⧸ M
  let q : C →* E := QuotientGroup.mk' M
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hcE : Nat.card E = p := card_quotient_coatom_eq_prime (p := p) hM
  let D := (C × C) × C
  let u : C × C →* G := (f₀.comp C.subtype).noncommCoprod (f₁.comp C.subtype)
    (fun x y => h₀₁ x y)
  let m : D →* G := u.noncommCoprod (f₂.comp C.subtype)
    (fun x z => (h₀₂ x.1 z).mul_left (h₁₂ x.2 z))
  let ψ : D →* (E × E) × E := (q.prodMap q).prodMap q
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨x, y⟩, z⟩
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    obtain ⟨c, rfl⟩ := hq z
    exact ⟨((a, b), c), rfl⟩
  have hk : m.rangeRestrict.ker ≤ ψ.ker := by
    rintro ⟨⟨x, y⟩, z⟩ hx
    have he : f₀ (x : B) * f₁ (y : B) * f₂ (z : B) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxZ : x ∈ Z := central_coordinate_of_relation f₀ f₁ f₂ hf₀
      h₀₁ h₀₂ x y z he
    have hyZ : y ∈ Z := central_coordinate_of_relation f₁ f₂ f₀ hf₁
      h₁₂ (fun a b => (h₀₁ b a).symm) y z x (rotate_eq_one _ _ _ he)
    have hzZ : z ∈ Z := central_coordinate_of_relation f₂ f₀ f₁ hf₂
      (fun a b => (h₀₂ b a).symm) (fun a b => (h₁₂ b a).symm) z x y
      (rotate_eq_one _ _ _ (rotate_eq_one _ _ _ he))
    change ((q x, q y), q z) = 1
    exact Prod.ext (Prod.ext ((QuotientGroup.eq_one_iff _).mpr (hZM hxZ))
      ((QuotientGroup.eq_one_iff _).mpr (hZM hyZ)))
      ((QuotientGroup.eq_one_iff _).mpr (hZM hzZ))
  let d : m.range →* (E × E) × E :=
    m.rangeRestrict.liftOfSurjective m.rangeRestrict_surjective ⟨ψ, hk⟩
  have hd (x : D) : d (m.rangeRestrict x) = ψ x :=
    m.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x
  have hds : Function.Surjective d := by
    intro x
    obtain ⟨y, rfl⟩ := hψ x
    exact ⟨m.rangeRestrict y, hd y⟩
  have hpE : ∀ x : (E × E) × E, x ^ p = 1 := by
    rintro ⟨⟨x, y⟩, z⟩
    apply Prod.ext
    · apply Prod.ext
      · change x ^ p = 1
        simpa only [hcE] using (pow_card_eq_one' (x := x))
      · change y ^ p = 1
        simpa only [hcE] using (pow_card_eq_one' (x := y))
    · change z ^ p = 1
      simpa only [hcE] using (pow_card_eq_one' (x := z))
  have hc : Nat.card ((E × E) × E) = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, hcE]
    ring
  have hr : 3 ≤ Group.rank ((E × E) × E) := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    rw [← hc]
    exact card_dvd_exponent_pow_rank' _ hpE
  have hDp : IsPGroup p D := by
    obtain ⟨n, hn⟩ := hCp.exists_card_eq
    apply IsPGroup.of_card (n := n + n + n)
    simp only [D, Nat.card_prod, hn, pow_add]
  have : IsMulCommutative m.range := ⟨⟨fun x y => by
    obtain ⟨a, rfl⟩ := m.rangeRestrict_surjective x
    obtain ⟨b, rfl⟩ := m.rangeRestrict_surjective y
    rw [← map_mul, mul_comm, map_mul]⟩⟩
  exact hr.trans ((Group.rank_le_of_surjective d hds).trans
    (Subgroup.rank_le_primeRank p m.range
      (hDp.of_surjective m.rangeRestrict m.rangeRestrict_surjective)))

/-- Three commuting embedded copies of a nontrivial finite perfect group
force rank at least three at an odd prime. Shared centers are allowed. -/
theorem exists_odd_prime_rank_three_of_commuting_perfect
    [Finite B] [Nontrivial B] [Group.IsPerfect B] [Finite G]
    (f₀ f₁ f₂ : B →* G)
    (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁)
    (hf₂ : Function.Injective f₂)
    (h₀₁ : ∀ x y, Commute (f₀ x) (f₁ y))
    (h₀₂ : ∀ x y, Commute (f₀ x) (f₂ y))
    (h₁₂ : ∀ x y, Commute (f₁ x) (f₂ y)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 ≤ primeRank p G := by
  obtain ⟨p, hp, ho, C, hCp, hCc, hCZ⟩ :=
    exists_noncentral_cyclic_odd_pGroup (B := B)
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative C := hCc
  exact ⟨p, hp, ho, rank_three_of_noncentral_abelian_pGroup C hCp hCZ
    f₀ f₁ f₂ hf₀ hf₁ hf₂ h₀₁ h₀₂ h₁₂⟩

end Theory.GroupTheory.CommutingPerfectRank
