module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondSmallSporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstRee
public import Theory.Representation.SymplecticFour.BinaryDegree
public import Theory.Representation.Triality.PrimitiveDegree
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order

/-!
# The non-linear Lie rows at the second flag normalizer

The full original V₂ has binary dimension at most 3n, including C_V(L).
A prime divisor of a simple two-core quotient must divide the order of
its action image: otherwise the action kernel surjects onto that quotient,
and perfectness kills the remaining two-group image. The literal natural
L₂ action rules out this trivial action.

Primitive primes for Sp₄(q), G₂(q), and the Ree carrier have binary orders
4n, 6n, and 12n. The actual triality order gives 12m in both source field
relations n=m and n=3m. All exceed 3n. Ree simplicity is derived from the
ambient SQTK component, its two-rank and its core-free parabolic; it is
not assumed as an additional model fact. Thus only the two linear rows
remain in the characteristic-two part of the source embedding catalogue.
SecondCatalogue applies this reduction to the actual containing component.

The preceding natural-plane projection and its exact central kernel belong
to qt-d-1222-natural-flag-cartan, with final discharge by
qt-d-1222-natural-local-geometry. The remaining linear and field-four rows,
second-component equality, triangle and final assembly stay with
qt-d-1222-natural-relative-components.

Source: Aschbacher--Smith 11.1.2, printed pp.764--765, and G.7.1,
printed p.347, combined manuscript of 1 March 2004. The imported G₂
order calculation retains its ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem simple_quotient_small_action {A W : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] [IsSimpleGroup (A ⧸ pCore 2 A)]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {r : ℕ} (hr : r ∣ Nat.card (A ⧸ pCore 2 A))
    (ρ : Representation (ZMod 2) A W)
    (hbad : ¬ r ∣ Nat.card (GL (Fin (Module.finrank (ZMod 2) W)) (ZMod 2)))
    (a : A) : ρ a = 1 := by
  let φ := ρ.asGroupHom
  let N := φ.ker
  let q := QuotientGroup.mk' (pCore 2 A)
  let : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  have hfull : N.map q = ⊤ := by
    rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with h | h
    · have hN : N ≤ pCore 2 A := by
        simpa only [q,MonoidHom.comap_bot,QuotientGroup.ker_mk'] using
          map_le_iff_le_comap.mp h.le
      have hdiv : r ∣ Nat.card φ.range := by
        have hi := hr.trans (index_dvd_of_le hN)
        simpa only [N,index_ker] using hi
      let R := φ.range
      let : Finite R := Finite.of_surjective _ φ.rangeRestrict_surjective
      let σ : Representation (ZMod 2) R W :=
        { toFun r := r.val.val
          map_one' := rfl
          map_mul' _ _ := rfl }
      have hf : Function.Injective σ := Units.val_injective.comp Subtype.val_injective
      exact (hbad (hdiv.trans (Representation.card_dvd_card_GL_of_injective σ hf))).elim
    · exact h
  have hs : N ⊔ pCore 2 A = ⊤ := by
    have he := congrArg (comap q) hfull
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he
  let : Group.IsNilpotent (A ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N (pCore 2 A) pCore_isPGroup hs).isNilpotent
  have hN : N = ⊤ := top_unique (by simpa only [solvableResidual_eq_top] using
    solvableResidual_le_of_solvable_quotient N)
  have ha : a ∈ N := hN ▸ mem_top a
  exact congrArg Units.val ha

private theorem g2_prime {A : Type*} [Group A] [Finite A] {n : ℕ} (hn : 1 < n)
    (hm : ClassificationModels.IsG2At A (2 ^ n)) :
    IsSimpleGroup A ∧ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card A ∧
      orderOf (2 : ZMod r) = 6 * n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let : IsSimpleGroup (Atlas.G2.Model F) := Atlas.G2.isSimple hlarge
  obtain ⟨r,hr,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_six_mul (by omega : 2 ≤ n)
  have hr2 : r ≠ 2 := by
    rintro rfl
    change orderOf (0 : ZMod 2) = 6 * n at ho
    rw [orderOf_zero] at ho
    omega
  refine ⟨e.isSimpleGroup,r,hr,hr2,?_,ho⟩
  have hpow : (2 : ZMod r) ^ (6 * n) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hdiv : r ∣ 2 ^ (6 * n) - 1 := by
    apply (Nat.modEq_iff_dvd' (one_le_pow₀ (by decide) : 1 ≤ 2 ^ (6 * n))).mp
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hpow.symm
  rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF,← pow_mul,mul_comm n 6]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdiv _) _

private theorem symplectic_prime {A : Type*} [Group A] [Finite A] {n : ℕ} (hn : 1 < n)
    (hm : Source.IsSp A 2 (2 ^ n)) :
    IsSimpleGroup A ∧ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card A ∧
      orderOf (2 : ZMod r) = 4 * n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup_of_card_eq_two_pow
    (show 2 ≤ n by omega) hF
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  obtain ⟨r,hr,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul (by omega : 0 < n)
  have hr2 : r ≠ 2 := by
    rintro rfl
    change orderOf (0 : ZMod 2) = 4 * n at ho
    rw [orderOf_zero] at ho
    omega
  refine ⟨e.isSimpleGroup,r,hr,hr2,?_,ho⟩
  rw [Nat.card_congr e.toEquiv]
  exact Representation.SymplecticFour.prime_dvd_card_of_orderOf_two (by omega) hF hr ho

private theorem triality_prime {A : Type*} [Group A] [Finite A] {m : ℕ} (hm : 0 < m)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ m) A) :
    IsSimpleGroup A ∧ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card A ∧
      orderOf (2 : ZMod r) = 12 * m := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ m hm).mp hmodel
  refine ⟨e.isSimpleGroup,?_⟩
  simpa only [Nat.card_congr e.toEquiv] using Triality.PrimitiveDegree.exists_prime_dvd_card m hm

private theorem ree_simple {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) {B : Subgroup H}
    (hB : B.IsCComponent) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At (B ⧸ pCore 2 B) m) :
    IsSimpleGroup (B ⧸ pCore 2 B) := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* d.fixedGroup := (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  let := pCore_isNilpotent (p := 2) (G := H)
  have hCQ : C.IsCComponent := hB.map_quotient _
  let : Group.IsPerfect C := hCQ.perfect
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
    (f := eC.toMonoidHom) eC.surjective
  have hHQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hH.isKGroup.quotient _⟩
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hH.stronglyQuasithin r hr hor)
  have htwo : 2 ≤ primeRank 2 C := by
    rw [primeRank_congr 2 (eC.trans d.modelEquiv)]
    exact (by decide : 2 ≤ 3).trans (ReeF4.three_le_twoRank m)
  let : IsQuasisimple C :=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
      hHQ (pCore_quotient_pCore_eq_bot 2) hCQ htwo
  have hz : center C = ⊥ := by
    apply bot_unique
    intro z hz
    exact eC.map_eq_one_iff.mp ((ExceptionalActors.ree_center_eq_bot_of_perfect hm d).le
      ((centerCongr eC) ⟨z,hz⟩).property)
  let eZ : (C ⧸ center C) ≃* d.fixedGroup :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : IsSimpleGroup d.fixedGroup := eZ.symm.isSimpleGroup
  exact e.isSimpleGroup

private theorem ree_prime {A : Type*} [Group A] [Finite A] {m : ℕ}
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At A m) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card A ∧
      orderOf (2 : ZMod r) = 12 * (2 * m + 1) := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  obtain ⟨r,hr,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_six_mul
    (by omega : 2 ≤ 2 * (2 * m + 1))
  have ho' : orderOf (2 : ZMod r) = 12 * (2 * m + 1) := by omega
  let : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    change orderOf (0 : ZMod 2) = 12 * (2 * m + 1) at ho'
    rw [orderOf_zero] at ho'
    omega
  refine ⟨r,hr,hr2,?_,ho'⟩
  have hpow : ((2 : ZMod r) ^ (2 * m + 1)) ^ 12 = 1 := by
    rw [← pow_mul,Nat.mul_comm (2 * m + 1) 12,← ho']
    exact pow_orderOf_eq_one _
  have hsix : ((2 : ZMod r) ^ (2 * m + 1)) ^ 6 ≠ 1 := by
    intro hh
    rw [← pow_mul] at hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ho'] at hd
    have hle := Nat.le_of_dvd (by omega : 0 < (2 * m + 1) * 6) hd
    omega
  have hz : (((2 : ZMod r) ^ (2 * m + 1)) ^ 6 - 1) *
      (((2 : ZMod r) ^ (2 * m + 1)) ^ 6 + 1) = 0 := by
    calc
      _ = ((2 : ZMod r) ^ (2 * m + 1)) ^ 12 - 1 := by ring
      _ = 0 := by rw [hpow,sub_self]
  have hfactor := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hsix)
  have hd : r ∣ (2 ^ (2 * m + 1)) ^ 6 + 1 :=
    (ZMod.natCast_eq_zero_iff _ r).mp (by simpa using hfactor)
  rw [Nat.card_congr (e.trans d.modelEquiv).toEquiv,
    ReeF4.CentralCovers.OddPrimary.Order.card_model]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right hd _) _) _) _

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Every odd prime in a simple two-core quotient satisfies the binary degree
bound on the full original plane. No faithful action of K is assumed. -/
theorem second_cover_prime_order_bound
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)]
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ Nat.card (K ⧸ pCore 2 K)) :
    orderOf (2 : ZMod r) ≤ 3 * S.field.degree := by
  by_contra hbound
  let : Group.IsPerfect (K.subgroupOf (normalizer (f.Vi 1 : Set G))) := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  have hbad : ¬ r ∣ Nat.card (GL (Fin (Module.finrank (ZMod 2) (Additive (f.Vi 1)))) (ZMod 2)) := by
    intro hh
    exact hbound ((BinaryPrimeDegree.orderOf_le_of_dvd_card_GL hr hr2 hh).trans
      (second_cover_finrank_le D S f p hp hk))
  let ρ := (flagAction f 1).comp (inclusion hK.1)
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier
    (![1,0]) (![0,1]) (by simp) (by simp)
  obtain ⟨a,rfl⟩ := hπ g
  obtain ⟨v,hv⟩ := hp (![1,0])
  have he : flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v = v :=
    LinearMap.congr_fun (simple_quotient_small_action hd ρ hbad ⟨a,hLK a.property⟩) v
  have ha := hact a v
  rw [he,hv] at ha
  have hg' : specialLinearNatural 2 (π a) (![1,0]) = (![0,1]) := hg
  rw [hg'] at ha
  have hz := congrFun ha 0
  simp at hz

/-- The complete non-linear Lie part of the second-normalizer sieve,
including both triality field conventions, leaves only the linear rows. -/
theorem second_lie_is_linear
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hmodel : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) := by
  have hn := S.nonbinary
  have exclude [IsSimpleGroup (K ⧸ pCore 2 K)] {d : ℕ}
      (hd : 3 * S.field.degree < d)
      (hprime : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card (K ⧸ pCore 2 K) ∧
        orderOf (2 : ZMod r) = d) : False := by
    obtain ⟨r,hr,hr2,hrd,ho⟩ := hprime
    have hb := second_cover_prime_order_bound D S f hK hLK π hπ p hp hact hk hr hr2 hrd
    rw [ho] at hb
    omega
  cases hmodel with
  | sl3 h => exact .inl h
  | psl3 h => exact .inr h
  | sp4 h =>
    obtain ⟨hs,hp⟩ := symplectic_prime hn h
    let := hs
    exact (exclude (by omega) hp).elim
  | g2 h =>
    obtain ⟨hs,hp⟩ := g2_prime hn h
    let := hs
    exact (exclude (by omega) hp).elim
  | triality h =>
    obtain ⟨hs,hp⟩ := triality_prime (by omega : 0 < S.field.degree) h
    let := hs
    exact (exclude (by omega) hp).elim
  | trialityCube m hm he h =>
    obtain ⟨hs,hp⟩ := triality_prime (by omega : 0 < m) h
    let := hs
    exact (exclude (by omega) hp).elim
  | ree m hm he h =>
    obtain ⟨d,⟨e⟩⟩ := h
    let B := K.subgroupOf (normalizer (f.Vi 1 : Set G))
    let eB : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
      QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1) (pCore_map_iso 2 _)
    let : IsSimpleGroup (B ⧸ pCore 2 B) := ree_simple
      (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)) hK.2 hm
      ⟨d,⟨eB.trans e⟩⟩
    let : IsSimpleGroup (K ⧸ pCore 2 K) := eB.symm.isSimpleGroup
    exact (exclude (by omega) (ree_prime ⟨d,⟨e⟩⟩)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
