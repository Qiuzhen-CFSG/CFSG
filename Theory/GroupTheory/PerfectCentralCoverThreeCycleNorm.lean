module

public import Theory.GroupTheory.CentralExtensionSwap
public import Theory.GroupTheory.PerfectCentralSupplement
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Tactic.FinCases

/-!
# Perfect central covers and permutation tori

An ambient swap makes lifts of two commuting odd-order generators commute.
This proves that the full preimage of a torus with pairwise swapped generators
is abelian. If a three-cycle permutes three independent cyclic coordinates,
every fixed torus element is a norm. A norm of a lift commutes with a lift of
the three-cycle, because its cube is central. The covering is consequently
injective on the derived subgroup of the torus-by-cycle preimage. Central
transfer excludes any prime not dividing the local subgroup's index.

This avoids requiring inversion of a rank-three torus. The concrete consumer
is the norm-one diagonal torus in degree-four unitary groups, in
`HigherClassicalCovers.Nondefining.UnitaryQuadratic`.

Source: the perfect-central-cover convention and transfer argument of
Aschbacher–Smith I.1.1–I.1.2, printed p.407, used for A.2.17, printed p.39.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace PerfectCentralCovering

/-- Pairwise ambient swaps of odd-order commuting generators give an abelian full preimage. -/
theorem isMulCommutative_comap_of_swapped_generators
    {E G I : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (T : Subgroup G) (x : I → G) (hgen : closure (Set.range x) = T)
    (hxy : ∀ i j, Commute (x i) (x j))
    (hswap : ∀ i j, i ≠ j → ∃ s : G, s*x i*s⁻¹ = x j ∧ s*x j*s⁻¹ = x i)
    {m : ℕ} (hm : m.Coprime 2) (hx : ∀ i, x i ^ m = 1) :
    IsMulCommutative (T.comap f) := by
  classical
  choose a ha using fun i => hf (x i)
  have hab (i j : I) : Commute (a i) (a j) := by
    by_cases hij : i = j
    · subst j; exact Commute.refl _
    obtain ⟨s, hs, hs'⟩ := hswap i j hij
    exact CentralExtension.commute_lifts_of_swap f hf hk (x i) (x j) s hm (hx i)
      (hxy i j) hs hs' (a i) (a j) (ha i) (ha j)
  let L := closure (Set.range a)
  have hL : IsMulCommutative L := by
    apply isMulCommutative_closure
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact (hab i j).eq
  have hmap : L.map f = T := by
    change (closure (Set.range a)).map f = T
    rw [MonoidHom.map_closure, ← Set.range_comp,
      show f ∘ a = x from funext ha, hgen]
  have hle : T.comap f ≤ center E ⊔ L := by
    rw [← hmap, comap_map_eq]
    exact sup_le le_sup_right (hk.trans le_sup_left)
  have hcomm : IsMulCommutative (center E ⊔ L : Subgroup E) := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le (center_le_centralizer _)
    apply le_centralizer_iff.mpr
    exact sup_le (center_le_centralizer _)
      (le_centralizer_iff_isMulCommutative.mpr hL)
  exact le_centralizer_iff_isMulCommutative.mp
    (hle.trans ((le_centralizer_iff_isMulCommutative.mpr hcomm).trans
      (centralizer_le hle)))

private theorem abelian_commute {E : Type*} [Group E] (A : Subgroup E)
    (hA : IsMulCommutative A) {a b : E} (ha : a ∈ A) (hb : b ∈ A) : Commute a b := by
  let := hA
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)

/-- The norm of a lift commutes with a lift of an element whose cube is one. -/
theorem threeCycleNorm_commute {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ center E)
    (T : Subgroup G) (hT : IsMulCommutative (T.comap f))
    (c : G) (hc : c ∈ normalizer (T : Set G)) (hc3 : c ^ 3 = 1)
    (b a : E) (hb : f b = c) (ha : f a ∈ T) :
    Commute (a * (b * a * b⁻¹) * (b ^ 2 * a * (b ^ 2)⁻¹)) b := by
  have h3 : b ^ 3 * a * (b ^ 3)⁻¹ = a := by
    have hz : b ^ 3 ∈ center E := hk (by
      rw [MonoidHom.mem_ker, map_pow, hb, hc3])
    rw [← mem_center_iff.mp hz a, mul_inv_cancel_right]
  have hba : f (b * a * b⁻¹) ∈ T := by
    simpa only [map_mul, map_inv, hb] using (mem_normalizer_iff.mp hc (f a)).mp ha
  have hb2a : f (b ^ 2 * a * (b ^ 2)⁻¹) ∈ T := by
    simpa only [map_mul, map_inv, map_pow, hb] using
      (mem_normalizer_iff.mp ((normalizer (T : Set G)).pow_mem hc 2) (f a)).mp ha
  have hcomm := (abelian_commute (T.comap f) hT ha hba).mul_right
    (abelian_commute (T.comap f) hT ha hb2a)
  have he : b * (a * (b*a*b⁻¹) * (b^2*a*(b^2)⁻¹)) * b⁻¹ =
      a * (b*a*b⁻¹) * (b^2*a*(b^2)⁻¹) := by
    calc
      _ = (b*a*b⁻¹) * (b^2*a*(b^2)⁻¹) * (b^3*a*(b^3)⁻¹) := by group
      _ = (b*a*b⁻¹) * (b^2*a*(b^2)⁻¹) * a := by rw [h3]
      _ = a * ((b*a*b⁻¹) * (b^2*a*(b^2)⁻¹)) := hcomm.eq.symm
      _ = _ := (mul_assoc _ _ _).symm
  exact (show Commute b _ from mul_inv_eq_iff_eq_mul.mp he).symm

private theorem derived_join_le {E : Type*} [Group E] (A B : Subgroup E)
    (hA : IsMulCommutative A) (hB : IsMulCommutative B)
    (hn : B ≤ normalizer (A : Set E)) : ⁅A ⊔ B, A ⊔ B⁆ ≤ ⁅A, B⁆ := by
  have hform {g : E} (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
    have he := coe_mul_of_right_le_normalizer_left A B hn
    change g ∈ (↑(A ⊔ B) : Set E) at hg
    rw [he] at hg
    exact hg
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hform hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hform hy
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_mul_right_eq_mul_conj,
    (abelian_commute B hB hb hd).commutator_eq, mul_one, mul_inv_cancel_right,
    commutatorElement_mul_right_eq_mul_conj,
    (abelian_commute A hA ha hc).commutator_eq, one_mul]
  apply mul_mem
  · exact (mem_normalizer_iff.mp (normalizer_commutator_ge_left A B ha) _).mp
      (by rw [commutator_comm]; exact commutator_mem_commutator hb hc)
  · exact (mem_normalizer_iff.mp (normalizer_commutator_ge_left A B hc) _).mp
      (commutator_mem_commutator ha hd)

private theorem exists_torus_commutator_hom {E : Type*} [Group E] [Finite E]
    (A : Subgroup E) (hA : IsMulCommutative A) (b : E)
    (hb : b ∈ normalizer (A : Set E)) :
    ∃ d : A →* E, (∀ a, d a = ⁅(a : E), b⁆) ∧
      d.range = ⁅A ⊔ zpowers b, A ⊔ zpowers b⁆ := by
  have hn : zpowers b ≤ normalizer (A : Set E) := zpowers_le.mpr hb
  have hDA : ⁅A, zpowers b⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hn
  let d : A →* E := {
    toFun a := ⁅(a : E), b⁆
    map_one' := by simp
    map_mul' a a' := by
      change ⁅(a : E) * a', b⁆ = ⁅(a : E), b⁆ * ⁅(a' : E), b⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        (abelian_commute A hA a.property
          (hDA (commutator_mem_commutator a'.property (mem_zpowers b)))).eq,
        mul_inv_cancel_right]
      exact (abelian_commute A hA
        (hDA (commutator_mem_commutator a'.property (mem_zpowers b)))
        (hDA (commutator_mem_commutator a.property (mem_zpowers b)))).eq }
  have hd (a : A) : d a = ⁅(a : E), b⁆ := rfl
  have hconj {z : E} (hz : z ∈ d.range) : b * z * b⁻¹ ∈ d.range := by
    obtain ⟨a, rfl⟩ := hz
    refine ⟨⟨b * a * b⁻¹, (mem_normalizer_iff.mp hb a).mp a.property⟩, ?_⟩
    simp only [hd]
    conv_rhs => rw [conjugate_commutatorElement]
    simp
  have hp (a : E) (ha : a ∈ A) (n : ℕ) : ⁅a, b ^ n⁆ ∈ d.range := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', commutatorElement_mul_right_eq_mul_conj,
        mul_assoc, mul_assoc, ← mul_assoc b]
      exact d.range.mul_mem ⟨⟨a,ha⟩,rfl⟩ (hconj ih)
  refine ⟨d, hd, le_antisymm ?_ ?_⟩
  · rintro z ⟨a,rfl⟩
    exact commutator_mem_commutator (mem_sup_left a.property) (mem_sup_right (mem_zpowers b))
  · apply (derived_join_le A (zpowers b) hA inferInstance hn).trans
    apply commutator_le.mpr
    intro a ha y hy
    obtain ⟨n,rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hy)
    exact hp a ha n

/-- Surjectivity of the three-cycle norm onto the fixed torus excludes kernel primes by transfer. -/
theorem Cover.not_dvd_kernel_of_threeCycleNorm
    {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]
    (f : Cover E G) {r : ℕ} [Fact r.Prime]
    (T : Subgroup G) (c : G) (hc : c ∈ normalizer (T : Set G)) (hc3 : c ^ 3 = 1)
    (hT : IsMulCommutative (T.comap f.toMonoidHom))
    (hnorm : ∀ t ∈ T, Commute t c → ∃ u ∈ T,
      u * (c*u*c⁻¹) * (c^2*u*(c^2)⁻¹) = t)
    (hi : ¬ r ∣ (T ⊔ zpowers c).index) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let := f.isPerfect
  obtain ⟨b, hb⟩ := f.surjective c
  let A := T.comap f.toMonoidHom
  have hbA : b ∈ normalizer (A : Set E) := by
    apply mem_normalizer_iff.mpr
    intro a
    change f.toMonoidHom a ∈ T ↔ f.toMonoidHom (b*a*b⁻¹) ∈ T
    simpa only [map_mul, map_inv, hb] using mem_normalizer_iff.mp hc (f.toMonoidHom a)
  have hgen : A ⊔ zpowers b = (T ⊔ zpowers c).comap f.toMonoidHom := by
    have he : (A ⊔ zpowers b).map f.toMonoidHom = T ⊔ zpowers c := by
      rw [Subgroup.map_sup, map_comap_eq_self_of_surjective f.surjective,
        MonoidHom.map_zpowers, hb]
    rw [← he, comap_map_eq_self]
    exact (T.ker_le_comap f.toMonoidHom).trans le_sup_left
  obtain ⟨d, hd, hrange⟩ := exists_torus_commutator_hom A hT b hbA
  have hfaithful {z : E} (hz : z ∈ d.range) (hzk : z ∈ f.toMonoidHom.ker) : z = 1 := by
    obtain ⟨a, rfl⟩ := hz
    have hcomm : Commute (f.toMonoidHom a) c := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [MonoidHom.mem_ker, hd, map_commutatorElement, hb] at hzk
      exact hzk
    obtain ⟨u, hu, he⟩ := hnorm (f.toMonoidHom a) a.property hcomm
    obtain ⟨v, hv⟩ := f.surjective u
    let w := v * (b*v*b⁻¹) * (b^2*v*(b^2)⁻¹)
    have hw : f.toMonoidHom w = f.toMonoidHom a := by
      simpa only [w, map_mul, map_inv, map_pow, hb, hv] using he
    rw [hd, CentralExtension.commutator_eq_of_image_eq f.toMonoidHom
      f.ker_le_center hw.symm rfl]
    exact (threeCycleNorm_commute f.toMonoidHom f.ker_le_center T hT c hc hc3
      b v hb (hv ▸ hu)).commutator_eq
  intro hdiv
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hdiv
  have hzE : orderOf (z : E) = r := (Subgroup.orderOf_coe z).trans hz
  let Z := zpowers (z : E)
  have hZker : Z ≤ f.toMonoidHom.ker := zpowers_le.mpr z.property
  have hZp : IsPGroup r Z := IsPGroup.of_card (n := 1)
    (by simpa only [Z, Nat.card_zpowers, pow_one] using hzE)
  have hzD : (z : E) ∈ ⁅A ⊔ zpowers b, A ⊔ zpowers b⁆ := by
    apply central_pSubgroup_le_commutator (A ⊔ zpowers b) Z
      (hZker.trans (by rw [hgen]; exact (T ⊔ zpowers c).ker_le_comap _))
      (hZker.trans f.ker_le_center) hZp _ (mem_zpowers _)
    rwa [hgen, index_comap_of_surjective _ f.surjective]
  have hzone := hfaithful (hrange.symm ▸ hzD) z.property
  exact (Fact.out : r.Prime).ne_one (hzE.symm.trans (orderOf_eq_one_iff.mpr hzone))

/-- A three-cycle on three independent coordinates has surjective norm onto its fixed subgroup. -/
theorem threeCycleNorm_surjective_fixed
    {C G : Type*} [CommGroup C] [Group G]
    (t : (Fin 3 → C) →* G) (ht : Function.Injective t) (c : G)
    (hact : ∀ a, c * t a * c⁻¹ = t ![a 2, a 0, a 1]) :
    ∀ z ∈ t.range, Commute z c → ∃ u ∈ t.range,
      u * (c*u*c⁻¹) * (c^2*u*(c^2)⁻¹) = z := by
  rintro _ ⟨a,rfl⟩ hcomm
  have hfix : (![a 2, a 0, a 1] : Fin 3 → C) = a := by
    apply ht
    rw [← hact, hcomm.symm.eq, mul_inv_cancel_right]
  have h01 : a 0 = a 1 := by simpa using congrFun hfix 1
  have h12 : a 1 = a 2 := by simpa using congrFun hfix 2
  refine ⟨t ![a 0,1,1], ⟨_,rfl⟩, ?_⟩
  have htwice : c ^ 2 * t ![a 0,1,1] * (c ^ 2)⁻¹ = t ![1,1,a 0] := by
    calc
      _ = c * (c * t ![a 0,1,1] * c⁻¹) * c⁻¹ := by simp only [pow_two]; group
      _ = _ := by simp [hact]
  rw [htwice, hact, ← map_mul, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp [h01, h12]

/-- A cyclic generator in each coordinate generates the whole rank-three torus image. -/
theorem closure_coordinate_generators
    {C G : Type*} [CommGroup C] [Group G]
    (t : (Fin 3 → C) →* G) (u : C) (hu : ∀ a, a ∈ zpowers u) :
    closure (Set.range (fun i : Fin 3 => t (Pi.mulSingle i u))) = t.range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨_,rfl⟩
  · rintro _ ⟨a,rfl⟩
    have hsingle (i : Fin 3) : t (Pi.mulSingle i (a i)) ∈
        closure (Set.range (fun i : Fin 3 => t (Pi.mulSingle i u))) := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hu (a i))
      rw [← hk, Pi.mulSingle_zpow, map_zpow]
      exact zpow_mem (subset_closure (Set.mem_range_self i)) k
    have he : a = Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) * Pi.mulSingle 2 (a 2) := by
      ext i
      fin_cases i <;> simp
    rw [he, map_mul, map_mul]
    exact mul_mem (mul_mem (hsingle 0) (hsingle 1)) (hsingle 2)

/-- The coordinate three-cycle normalizes the literal image of the torus homomorphism. -/
theorem threeCycle_mem_normalizer
    {C G : Type*} [CommGroup C] [Group G]
    (t : (Fin 3 → C) →* G) (c : G)
    (hact : ∀ a, c * t a * c⁻¹ = t ![a 2, a 0, a 1]) :
    c ∈ normalizer (t.range : Set G) := by
  apply mem_normalizer_iff.mpr
  intro z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨_, (hact a).symm⟩
  · rintro ⟨a,ha⟩
    refine ⟨![a 1,a 2,a 0], ?_⟩
    apply (MulAut.conj c).injective
    change c * t ![a 1,a 2,a 0] * c⁻¹ = c * z * c⁻¹
    rw [hact]
    change t ![a 0,a 1,a 2] = c * z * c⁻¹
    have he : (![a 0,a 1,a 2] : Fin 3 → C) = a := by
      ext i
      fin_cases i <;> rfl
    rwa [he]

/-- A rank-three odd cyclic torus with swaps and a three-cycle excludes primes absent from its local index. -/
theorem Cover.not_dvd_kernel_of_permuted_torus
    {E G C : Type*} [Group E] [Finite E] [Group G] [Finite G]
    [CommGroup C] [Finite C] [IsCyclic C]
    (f : Cover E G) {r : ℕ} [Fact r.Prime]
    (t : (Fin 3 → C) →* G) (ht : Function.Injective t)
    (hodd : (Nat.card C).Coprime 2)
    (hswap : ∀ i j : Fin 3, i ≠ j → ∃ s : G, ∀ u : C,
      s * t (Pi.mulSingle i u) * s⁻¹ = t (Pi.mulSingle j u) ∧
      s * t (Pi.mulSingle j u) * s⁻¹ = t (Pi.mulSingle i u))
    (c : G) (hc3 : c^3 = 1)
    (hact : ∀ a, c * t a * c⁻¹ = t ![a 2, a 0, a 1])
    (hi : ¬ r ∣ (t.range ⊔ zpowers c).index) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := C)
  have hT : IsMulCommutative (t.range.comap f.toMonoidHom) := by
    apply isMulCommutative_comap_of_swapped_generators f.toMonoidHom f.surjective
      f.ker_le_center t.range (fun i : Fin 3 => t (Pi.mulSingle i u))
      (closure_coordinate_generators t u hu)
    · intro i j
      exact (Commute.all _ _).map t
    · intro i j hij
      obtain ⟨s, hs⟩ := hswap i j hij
      exact ⟨s, hs u⟩
    · exact hodd
    · intro i
      rw [← map_pow, ← Pi.mulSingle_pow, pow_card_eq_one', Pi.mulSingle_one, map_one]
  exact f.not_dvd_kernel_of_threeCycleNorm t.range c (threeCycle_mem_normalizer t c hact) hc3 hT
    (threeCycleNorm_surjective_fixed t ht c hact) hi

/-- An abelian preimage at index prime to r excludes r from a perfect central kernel. -/
theorem Cover.not_dvd_kernel_of_abelian_preimage_at_prime_index
    {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]
    (f : Cover E G) {r : ℕ} [Fact r.Prime]
    (T : Subgroup G) (hT : IsMulCommutative (T.comap f.toMonoidHom))
    (hi : ¬ r ∣ T.index) : ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let := f.isPerfect
  intro hdiv
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hdiv
  have hzE : orderOf (z : E) = r := (Subgroup.orderOf_coe z).trans hz
  let Z := zpowers (z : E)
  have hZker : Z ≤ f.toMonoidHom.ker := zpowers_le.mpr z.property
  have hZp : IsPGroup r Z := IsPGroup.of_card (n := 1)
    (by simpa only [Z, Nat.card_zpowers, pow_one] using hzE)
  have hzD : (z : E) ∈ ⁅T.comap f.toMonoidHom, T.comap f.toMonoidHom⁆ :=
    central_pSubgroup_le_commutator (T.comap f.toMonoidHom) Z
      (hZker.trans (T.ker_le_comap _)) (hZker.trans f.ker_le_center) hZp
      (by rwa [index_comap_of_surjective _ f.surjective]) (mem_zpowers _)
  rw [commutator_self_eq_bot_iff.mpr hT] at hzD
  exact (Fact.out : r.Prime).ne_one
    (hzE.symm.trans (orderOf_eq_one_iff.mpr (mem_bot.mp hzD)))

/-- Two swapped odd-order commuting generators suffice at index prime to r. -/
theorem Cover.not_dvd_kernel_of_swapped_pair_at_prime_index
    {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]
    (f : Cover E G) {r : ℕ} [Fact r.Prime]
    (T : Subgroup G) (x y s : G)
    (hgen : closure ({x,y} : Set G) = T) (hxy : Commute x y)
    (hsx : s*x*s⁻¹ = y) (hsy : s*y*s⁻¹ = x)
    {m : ℕ} (hm : m.Coprime 2) (hx : x^m = 1) (hi : ¬ r ∣ T.index) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨a, ha⟩ := f.surjective x
  obtain ⟨b, hb⟩ := f.surjective y
  have hab := CentralExtension.commute_lifts_of_swap f.toMonoidHom f.surjective
    f.ker_le_center x y s hm hx hxy hsx hsy a b ha hb
  exact f.not_dvd_kernel_of_abelian_preimage_at_prime_index T
    (CentralExtension.isMulCommutative_comap_of_pair_lifts f.toMonoidHom
      f.ker_le_center T a b hab (by simpa only [ha,hb] using hgen)) hi

end PerfectCentralCovering
