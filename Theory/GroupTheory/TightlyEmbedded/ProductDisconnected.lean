module

public import Theory.GroupTheory.TightlyEmbedded
public import Theory.GroupTheory.ProductDisconnected

/-!
# Product disconnection from tightly embedded subgroups

Let `K` be tightly embedded and suppose that the normalizer of `K` inside each
distinct conjugate of `K` has odd order. Then the ambient conjugacy closure `Z`
of its involutions meets `N_G(K)` exactly in the involutions of `K`. Centralizer
control from tight embedding shows that `Z` is closed under products of distinct
commuting elements. If `K` is not normal, these facts establish Definition ZD.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem I.8.2, first paragraph of proof, printed p. 429.
-/

namespace Theory.GroupTheory

open BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

/-- The union of ambient conjugacy classes meeting the involutions of `K`. -/
@[expose] public def involutionConjugates (K : Subgroup G) : Set G :=
  {z | ∃ g x, x ∈ K ∧ IsInvolution x ∧ MulAut.conj g x = z}

/-- Every involution of `K` belongs to its ambient conjugacy closure. -/
public theorem mem_involutionConjugates {K : Subgroup G} {x : G}
    (hxK : x ∈ K) (hx : IsInvolution x) : x ∈ involutionConjugates K :=
  ⟨1, x, hxK, hx, by simp⟩

/-- The ambient conjugacy closure is invariant under conjugation. -/
public theorem involutionConjugates_invariant {K : Subgroup G} (g : G) {z : G}
    (hz : z ∈ involutionConjugates K) : MulAut.conj g z ∈ involutionConjugates K := by
  obtain ⟨h, x, hxK, hx, rfl⟩ := hz
  exact ⟨g * h, x, hxK, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- All elements of the conjugacy closure are involutions. -/
public theorem involutionConjugates_isInvolution {K : Subgroup G} {z : G}
    (hz : z ∈ involutionConjugates K) : IsInvolution z := by
  obtain ⟨g, x, hxK, hx, rfl⟩ := hz
  exact ⟨fun h => hx.ne_one ((MulAut.conj g).injective (by simpa using h)),
    by rw [← map_pow, hx.sq_eq_one, map_one]⟩

/-- Every distinct conjugate `J` of `K` has odd `N_J(K)`. -/
@[expose] public def HasOddConjugateNormalizers (K : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
    Odd (Nat.card ↥(Subgroup.normalizer (K : Set G) ⊓
      K.map (MulAut.conj g).toMonoidHom))

private theorem no_involution_of_odd {H : Subgroup G} (hH : Odd (Nat.card H))
    {z : G} (hzH : z ∈ H) (hz : IsInvolution z) : False := by
  let zH : H := ⟨z, hzH⟩
  have hz2 : zH ^ 2 = 1 := Subtype.ext hz.sq_eq_one
  have hzne : zH ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have hord : orderOf zH = 2 := orderOf_eq_prime hz2 hzne
  exact hH.not_two_dvd_nat (hord ▸ orderOf_dvd_natCard zH)

/-- An involution in a conjugate of `K` can normalize `K` only if that
conjugate equals `K`. -/
public theorem HasOddConjugateNormalizers.conjugator_mem {K : Subgroup G}
    (hodd : HasOddConjugateNormalizers K) {g x : G}
    (hxK : x ∈ K) (hx : IsInvolution x)
    (hgx : MulAut.conj g x ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hg
  apply no_involution_of_odd (hodd g hg)
    (show MulAut.conj g x ∈ Subgroup.normalizer (K : Set G) ⊓
      K.map (MulAut.conj g).toMonoidHom from
      ⟨hgx, Subgroup.mem_map_of_mem _ hxK⟩)
  exact involutionConjugates_isInvolution ⟨g, x, hxK, hx, rfl⟩

/-- The identity labelled (*) in the proof of I.8.2. -/
public theorem HasOddConjugateNormalizers.inter_normalizer {K : Subgroup G}
    (hodd : HasOddConjugateNormalizers K) :
    involutionConjugates K ∩ (Subgroup.normalizer (K : Set G) : Set G) =
      {z : G | z ∈ K ∧ IsInvolution z} := by
  ext z
  constructor
  · rintro ⟨⟨g, x, hxK, hx, rfl⟩, hzM⟩
    have hg := hodd.conjugator_mem hxK hx hzM
    exact ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxK,
      involutionConjugates_isInvolution ⟨g, x, hxK, hx, rfl⟩⟩
  · rintro ⟨hzK, hz⟩
    exact ⟨mem_involutionConjugates hzK hz, Subgroup.le_normalizer hzK⟩

variable [Finite G]

/-- Centralizers of involutions in a tightly embedded subgroup normalize it. -/
public theorem IsTightlyEmbedded.involution_centralizer_le {K : Subgroup G}
    (hK : IsTightlyEmbedded K) {z : G} (hzK : z ∈ K) (hz : IsInvolution z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hz.sq_eq_one hz.ne_one]
    simp
  have hne : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    have := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at this
    exact hz.ne_one this
  apply le_trans _ (hK.normalizer_le hp hne (Subgroup.zpowers_le.mpr hzK))
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
  exact Subgroup.centralizer_le_normalizer _

/-- The conjugacy closure is closed under products of distinct commuting
involutions, as proved in I.8.2. -/
public theorem IsTightlyEmbedded.involutionConjugates_mul {K : Subgroup G}
    (hK : IsTightlyEmbedded K) (hodd : HasOddConjugateNormalizers K)
    {x y : G} (hx : x ∈ involutionConjugates K) (hy : y ∈ involutionConjugates K)
    (hc : Commute x y) (hne : x ≠ y) : x * y ∈ involutionConjugates K := by
  obtain ⟨g, a, haK, ha, rfl⟩ := hx
  let b := MulAut.conj g⁻¹ y
  have hbZ : b ∈ involutionConjugates K := involutionConjugates_invariant _ hy
  have hgb : MulAut.conj g b = y := by simp [b, MulAut.conj_apply, mul_assoc]
  have hab : Commute a b := by
    apply (MulAut.conj g).injective
    simpa only [map_mul, hgb] using hc.eq
  have hbM : b ∈ Subgroup.normalizer (K : Set G) :=
    hK.involution_centralizer_le haK ha
      (Subgroup.mem_centralizer_singleton_iff.mpr hab.eq.symm)
  have hbK : b ∈ K := (Set.ext_iff.mp hodd.inter_normalizer b).mp ⟨hbZ, hbM⟩ |>.1
  have hb := involutionConjugates_isInvolution hbZ
  have habne : a * b ≠ 1 := by
    intro h
    have hab' : a = b := by
      calc
        a = b⁻¹ := eq_inv_of_mul_eq_one_left h
        _ = b := hb.inv_eq_self
    apply hne
    rw [hab', hgb]
  have hab2 : (a * b) ^ 2 = 1 := by rw [hab.mul_pow, ha.sq_eq_one, hb.sq_eq_one, mul_one]
  exact ⟨g, a * b, K.mul_mem haK hbK, ⟨habne, hab2⟩, by rw [map_mul, hgb]⟩

/-- A tightly embedded subgroup contains an involution. -/
public theorem IsTightlyEmbedded.exists_involution {K : Subgroup G}
    (hK : IsTightlyEmbedded K) : ∃ z : G, z ∈ K ∧ IsInvolution z := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp hK.1)
  have hzne : z ≠ 1 := by intro h; simp [h] at hz
  exact ⟨z, z.property, fun h => hzne (Subtype.ext h),
    congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)⟩

/-- The product-disconnected reduction in the first paragraph of I.8.2. -/
public theorem IsTightlyEmbedded.productDisconnected {K : Subgroup G}
    (hK : IsTightlyEmbedded K) (hnormal : ¬ K.Normal)
    (hodd : HasOddConjugateNormalizers K) :
    IsProductDisconnected (involutionConjugates K) (Subgroup.normalizer (K : Set G)) := by
  refine ⟨fun _ hz => involutionConjugates_isInvolution hz,
    fun g _ hz => involutionConjugates_invariant g hz,
    fun h => hnormal (Subgroup.normalizer_eq_top_iff.mp h), ?_, ?_, ?_⟩
  · obtain ⟨z, hzK, hz⟩ := hK.exists_involution
    exact ⟨z, mem_involutionConjugates hzK hz, Subgroup.le_normalizer hzK⟩
  · intro z hz hzM g
    have hzK := ((Set.ext_iff.mp hodd.inter_normalizer z).mp ⟨hz, hzM⟩).1
    constructor
    · exact hodd.conjugator_mem hzK (involutionConjugates_isInvolution hz)
    · intro hg
      exact Subgroup.le_normalizer ((Subgroup.mem_normalizer_iff.mp hg z).mp hzK)
  · intro x hx z hz hxz hxzM
    have hxI := involutionConjugates_isInvolution hx
    have hzI := involutionConjugates_isInvolution hz
    have hc : Commute x z := by
      have hi := hxz.inv_eq_self
      rw [mul_inv_rev, hxI.inv_eq_self, hzI.inv_eq_self] at hi
      exact hi.symm
    have hne : x ≠ z := by
      intro h
      apply hxz.ne_one
      rw [h, ← pow_two, hzI.sq_eq_one]
    have hxzZ := hK.involutionConjugates_mul hodd hx hz hc hne
    have hxzK := ((Set.ext_iff.mp hodd.inter_normalizer (x * z)).mp ⟨hxzZ, hxzM⟩).1
    exact hK.involution_centralizer_le hxzK hxz
end Theory.GroupTheory
