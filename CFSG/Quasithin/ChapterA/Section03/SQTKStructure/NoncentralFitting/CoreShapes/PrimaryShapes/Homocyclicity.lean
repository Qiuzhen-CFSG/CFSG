module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Seeds
public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.ElementaryAbelian.PrimePlane
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Homocyclicity of abelian primary cores

For a finite perfect ambient group, an abelian primary core with a primary
seed is homocyclic of rank two. The supercritical order-p centralizer condition
identifies the seed with the literal first omega subgroup. Its order p² then
forces exactly two nontrivial factors in the finite abelian decomposition.

If their exponents differ, the highest nontrivial power image is an invariant
order-p subgroup of the seed. Perfectness kills the actions on that cyclic
subgroup and its cyclic quotient. The remaining displacement action is abelian,
so perfectness kills it as well, contradicting the seed's noncentrality. This
is the invariant-line obstruction for the actual elementary-plane action; no
irreducibility or homocyclic coordinates are assumed.

The resulting equivalence retains every positive common exponent and supplies
`hhomocyclic` in `primary_shapes_of_elementary_steps`, with perfectness supplied
by the C-component. Abelianness remains the separate inversion input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.44–45. The finite-abelian factor-counting argument adapts
`Theory/GroupTheory/PGroup/AbelianRankTwoHomocyclic.lean` from two to any prime.
-/

namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes

open scoped IsMulCommutative

namespace PrimaryHomocyclicFactors

private def powerKerEquiv (p : ℕ) {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    (powMonoidHom p : A →* A).ker ≃* (powMonoidHom p : B →* B).ker where
  toFun x := ⟨e x, by change (e x)^p = 1; rw [← map_pow, show (x : A)^p = 1 from x.property, map_one]⟩
  invFun x := ⟨e.symm x, by change (e.symm x)^p = 1; rw [← map_pow, show (x : B)^p = 1 from x.property, map_one]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e (x : A) (y : A))

private def powerKerPiEquiv (p : ℕ) {ι : Type*} (B : ι → Type*) [∀ i, CommGroup (B i)] :
    (powMonoidHom p : (∀ i, B i) →* (∀ i, B i)).ker ≃
      (∀ i, (powMonoidHom p : B i →* B i).ker) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def piReindex {ι κ : Type*} (B : ι → Type*) [∀ i, Group (B i)] (e : κ ≃ ι) :
    (∀ i, B i) ≃* (∀ j, B (e j)) where
  __ := (Equiv.piCongrLeft B e).symm
  map_mul' _ _ := rfl

private def piTwo (B : Fin 2 → Type*) [∀ i, Group (B i)] :
    (∀ i, B i) ≃* B 0 × B 1 where
  __ := piFinTwoEquiv B
  map_mul' _ _ := rfl

/-- The first omega subgroup counts the nontrivial cyclic factors. -/
private theorem equiv_two_cyclic_factors
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) (homega : Nat.card (omega₁ A (p := p)) = p ^ 2) :
    ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
      (A ≃* (Multiplicative (ZMod (p^n)) × Multiplicative (ZMod (p^m)))) := by
  classical
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨ι, hι, d, hd, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  let B (i : ι) := Multiplicative (ZMod (d i))
  have hB (i : ι) : IsPGroup p (B i) :=
    (hA.of_equiv e).of_surjective (Pi.evalMonoidHom B i)
      (Function.surjective_eval i)
  have hpow (i : ι) : ∃ n : ℕ, d i = p^n := by
    have : NeZero (d i) := ⟨by have := hd i; omega⟩
    simpa [B] using (IsPGroup.iff_card.mp (hB i))
  choose n hn using hpow
  have hnpos (i : ι) : 1 ≤ n i := by
    have := hd i
    rw [hn i] at this
    by_contra h
    have : n i = 0 := by omega
    simp_all
  have hcardker (i : ι) : Nat.card (powMonoidHom p : B i →* B i).ker = p := by
    let : NeZero (d i) := ⟨by have := hd i; omega⟩
    rw [IsCyclic.card_powMonoidHom_ker]
    have hdiv : p ∣ d i := by rw [hn i]; exact dvd_pow_self p (by have := hnpos i; omega)
    simp [B, Nat.gcd_eq_right hdiv]
  have hcard : p ^ Fintype.card ι = p ^ 2 := by
    rw [omega₁, OmegaAction.omega_eq_pow_ker, pow_one] at homega
    rw [Nat.card_congr (powerKerEquiv p e).toEquiv,
      Nat.card_congr (powerKerPiEquiv p B), Nat.card_pi] at homega
    simpa only [hcardker, Finset.prod_const, Finset.card_univ] using homega
  have htwo : Fintype.card ι = 2 := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard
  let f := (Fintype.equivFinOfCardEq htwo).symm
  refine ⟨n (f 0), n (f 1), hnpos _, hnpos _, ⟨?_⟩⟩
  have hc (i : ι) : B i ≃* Multiplicative (ZMod (p^(n i))) := by
    dsimp [B]
    rw [hn i]
  exact (e.trans (piReindex B f)).trans
    ((piTwo (fun j => B (f j))).trans ((hc (f 0)).prodCongr (hc (f 1))))

end PrimaryHomocyclicFactors

open Subgroup
open scoped IsMulCommutative
namespace PrimaryHomocyclicPlane
variable {A V : Type*} [Group A] [Group V]

private def restrictAction (ρ : A →* MulAut V) (D : Subgroup V)
    (hD : ∀ g, D.map (ρ g).toMonoidHom = D) : A →* MulAut D where
  toFun g := ((ρ g).subgroupMap D).trans (MulEquiv.subgroupCongr (hD g))
  map_one' := by apply MulEquiv.ext; intro x; apply Subtype.ext; exact congrArg (fun f : MulAut V => f x.val) (map_one ρ)
  map_mul' g h := by apply MulEquiv.ext; intro x; apply Subtype.ext; exact congrArg (fun f : MulAut V => f x.val) (map_mul ρ g h)

private def quotientAction (ρ : A →* MulAut V) (D : Subgroup V) [D.Normal]
    (hD : ∀ g, D.map (ρ g).toMonoidHom = D) : A →* MulAut (V ⧸ D) where
  toFun g := QuotientGroup.congr D D (ρ g) (hD g)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D x
    change QuotientGroup.mk' D (ρ 1 x) = QuotientGroup.mk' D x
    rw [map_one]; rfl
  map_mul' g h := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D x
    change QuotientGroup.mk' D (ρ (g*h) x) = QuotientGroup.mk' D (ρ g (ρ h x))
    rw [map_mul]; rfl

private theorem cyclic_action_eq_one [Group.IsPerfect A] [IsCyclic V]
    (ρ : A →* MulAut V) (g : A) : ρ g = 1 := by
  let _ := (IsCyclic.mulAutMulEquiv V).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv V).injective
  exact Abelianization.commutator_subset_ker ρ Group.IsPerfect.mem_commutator

/-- A perfect action on an abelian group preserving a cyclic subgroup with
cyclic quotient is trivial. This is the triangular-action obstruction. -/
private theorem trivial_of_cyclic_subquotient [Group.IsPerfect A] [IsMulCommutative V]
    (ρ : A →* MulAut V) (D : Subgroup V)
    (hD : ∀ g, D.map (ρ g).toMonoidHom = D)
    [IsCyclic D] [IsCyclic (V ⧸ D)] : ρ = 1 := by
  have hfix (g : A) (x : V) (hx : x ∈ D) : ρ g x = x := by
    exact congrArg (fun f : MulAut D => (f ⟨x, hx⟩ : V))
      (cyclic_action_eq_one (restrictAction ρ D hD) g)
  have hdiff (g : A) (x : V) : x⁻¹ * ρ g x ∈ D := by
    have h := congrArg (fun f : MulAut (V ⧸ D) => f (QuotientGroup.mk' D x))
      (cyclic_action_eq_one (quotientAction ρ D hD) g)
    exact QuotientGroup.eq.mp h.symm
  have hc (g h : A) : ρ g * ρ h = ρ h * ρ g := by
    ext x
    have hg := hfix g (x⁻¹ * ρ h x) (hdiff h x)
    have hh := hfix h (x⁻¹ * ρ g x) (hdiff g x)
    simp only [map_mul, map_inv] at hg hh
    change ρ g (ρ h x) = ρ h (ρ g x)
    calc
      _ = ρ g x * (x⁻¹ * ρ h x) := by rw [← hg]; simp
      _ = ρ h x * (x⁻¹ * ρ g x) := by ac_rfl
      _ = _ := by rw [← hh]; simp
  let : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  let : IsMulCommutative ρ.range := ⟨⟨by
    rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    exact Subtype.ext (hc g h)⟩⟩
  let : Subsingleton ρ.range := inferInstance
  apply MonoidHom.ext
  intro g
  exact congrArg Subtype.val (Subsingleton.elim (ρ.rangeRestrict g) 1)
end PrimaryHomocyclicPlane

open Subgroup
open scoped IsMulCommutative
namespace PrimaryHomocyclicLine

private abbrev C (p n : ℕ) := Multiplicative (ZMod (p ^ n))
private abbrev B (p n m : ℕ) := C p n × C p m

private def powerRangeEquiv {P Q : Type*} [CommGroup P] [CommGroup Q]
    (e : P ≃* Q) (k : ℕ) :
    (powMonoidHom k : P →* P).range ≃* (powMonoidHom k : Q →* Q).range where
  toFun x := ⟨e x, by obtain ⟨y, hy⟩ := x.property; exact ⟨e y, by simpa using congrArg e hy⟩⟩
  invFun x := ⟨e.symm x, by obtain ⟨y, hy⟩ := x.property; exact ⟨e.symm y, by simpa using congrArg e.symm hy⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e (x : P) (y : P))

private theorem model_card_power_range {p : ℕ} [Fact p.Prime]
    (n m : ℕ) (h : m < n) :
    Nat.card (powMonoidHom (p^(n-1)) : B p n m →* B p n m).range = p := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have he : (powMonoidHom (p^(n-1)) : B p n m →* B p n m).range =
      (powMonoidHom (p^(n-1)) : C p n →* C p n).range.prod
        (powMonoidHom (p^(n-1)) : C p m →* C p m).range := by
    rw [← MonoidHom.range_prodMap]
    rfl
  rw [he, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_range]
  have hd : p ^ (n-1) ∣ p ^ n := pow_dvd_pow p (by omega)
  have hmd : p ^ m ∣ p ^ (n-1) := pow_dvd_pow p (by omega)
  simp only [C, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
    Nat.gcd_eq_right hd, Nat.gcd_eq_left hmd,
    Nat.div_self (pow_pos (Fact.out : p.Prime).pos m), mul_one]
  have he : p ^ n = p ^ (n-1) * p := by rw [← pow_succ]; congr 1; omega
  rw [he]
  exact Nat.mul_div_right p (pow_pos (Fact.out : p.Prime).pos _)

/-- Unequal factors produce a characteristic order-p power image in first omega. -/
private theorem power_line {P : Type*} [CommGroup P] {p : ℕ} [Fact p.Prime]
    (n m : ℕ) (h : m < n) (e : P ≃* B p n m) :
    Nat.card (powMonoidHom (p^(n-1)) : P →* P).range = p ∧
      (powMonoidHom (p^(n-1)) : P →* P).range ≤ omega₁ P (p := p) := by
  refine ⟨(Nat.card_congr (powerRangeEquiv e _).toEquiv).trans
    (model_card_power_range n m h), ?_⟩
  rintro x ⟨y, rfl⟩
  apply Subgroup.subset_closure
  change (y ^ (p^(n-1))) ^ (p^1) = 1
  rw [pow_one, ← pow_mul]
  have he : p ^ (n-1) * p = p ^ n := by rw [← pow_succ]; congr 1; omega
  rw [he]
  apply e.injective
  rw [map_pow, map_one]
  apply Prod.ext
  · change (e y).1 ^ (p^n) = 1
    let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    simpa [C] using (pow_card_eq_one' (x := (e y).1))
  · change (e y).2 ^ (p^n) = 1
    have hy : (e y).2 ^ (p^m) = 1 := by
      let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      simpa [C] using (pow_card_eq_one' (x := (e y).2))
    obtain ⟨k, hk⟩ := pow_dvd_pow p h.le
    calc
      (e y).2 ^ (p^n) = (e y).2 ^ (p^m * k) := congrArg (fun r : ℕ => (e y).2 ^ r) hk
      _ = 1 := by rw [pow_mul, hy, one_pow]

end PrimaryHomocyclicLine

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
open CFSG.Quasithin.Chapter1.Section02 LocalModels
open scoped IsMulCommutative

private theorem power_range_characteristic {P : Type*} [CommGroup P] (k : ℕ) :
    (powMonoidHom k : P →* P).range.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro f
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨f z, (map_pow f z k).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(f.symm y)^k, ⟨f.symm y, rfl⟩, by simp⟩

private theorem trivial_on_subgroup_of_power_line
    {A P : Type*} [Group A] [Group.IsPerfect A] [CommGroup P] [Finite P]
    {p : ℕ} [Fact p.Prime] (ρ : A →* MulAut P)
    (X : Subgroup P) [X.Characteristic] (hX : Nat.card X = p^2)
    (k : ℕ) (hc : Nat.card (powMonoidHom k : P →* P).range = p)
    (hle : (powMonoidHom k : P →* P).range ≤ X) :
    (MulAut.characteristic X).comp ρ = 1 := by
  let D := (powMonoidHom k : P →* P).range
  let : D.Characteristic := power_range_characteristic k
  let W := D.subgroupOf X
  have hw : Nat.card W = p :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hc
  let : IsCyclic W := isCyclic_of_prime_card hw
  have hq : Nat.card (X ⧸ W) = p := by
    have hh := W.index_mul_card
    change Nat.card (X ⧸ W) * Nat.card W = Nat.card X at hh
    rw [hw, hX, pow_two] at hh
    exact mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hh
  let : IsCyclic (X ⧸ W) := isCyclic_of_prime_card hq
  apply PrimaryHomocyclicPlane.trivial_of_cyclic_subquotient _ W
  intro g
  let a := ((MulAut.characteristic X).comp ρ) g
  have hinv (x : P) : ρ g x ∈ D ↔ x ∈ D := by
    change x ∈ D.comap (ρ g).toMonoidHom ↔ x ∈ D
    rw [Subgroup.characteristic_iff_comap_eq.mp inferInstance]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hinv y).mpr hy
  · intro hx
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    apply (hinv (a.symm x)).mp
    change (a (a.symm x) : P) ∈ D
    rw [a.apply_symm_apply]
    exact hx

variable {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

omit [Finite A] in
/-- In an abelian primary core, the supercritical seed is the literal first omega subgroup. -/
public theorem PrimarySeed.eq_omega_of_abelian (s : PrimarySeed p A)
    [IsMulCommutative (pCore p A)] : s.X = omega₁ (pCore p A) (p := p) := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.subset_closure
    change x ^ (p ^ 1) = 1
    rw [pow_one]
    exact congrArg Subtype.val (s.supercritical.pow_eq_one ⟨x, hx⟩)
  · apply (closure_le _).mpr
    intro x hx
    change x ^ (p ^ 1) = 1 at hx
    by_cases he : x = 1
    · exact he ▸ s.X.one_mem
    · apply s.supercritical.order_p_mem x
      · exact mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
      · apply orderOf_eq_prime_iff.mpr
        exact ⟨by simpa only [pow_one] using hx, he⟩

omit [Finite A] [Fact p.Prime] in
/-- The seed's actual conjugation action is nontrivial, by its noncentrality. -/
public theorem PrimarySeed.coreAction_ne_one (s : PrimarySeed p A) : coreAction s.X ≠ 1 := by
  intro h
  apply s.noncentral
  rintro x ⟨y, hy, rfl⟩
  apply mem_center_iff.mpr
  intro g
  have hh := congrArg (fun f : MulAut s.X => ((f ⟨y, hy⟩ : pCore p A) : A))
    (DFunLike.congr_fun h g)
  change g * (y : A) * g⁻¹ = y at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The abelian branch of A.3.6: the whole primary core has two equal positive
cyclic exponents, forced by the seed's actual nontrivial perfect action. -/
public theorem homocyclic_core [Group.IsPerfect A] (s : PrimarySeed p A)
    (hab : IsMulCommutative (pCore p A)) : HomocyclicTwo p (pCore p A) := by
  let : IsMulCommutative (pCore p A) := hab
  let : CommGroup (pCore p A) := IsMulCommutative.instCommGroup
  let : IsElementaryAbelian p s.X :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := s.supercritical.exponent_dvd_p }
  have hc : Nat.card s.X = p ^ 2 :=
    IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two s.rank_two
  have ho : Nat.card (omega₁ (pCore p A) (p := p)) = p ^ 2 :=
    s.eq_omega_of_abelian ▸ hc
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ :=
    PrimaryHomocyclicFactors.equiv_two_cyclic_factors pCore_isPGroup ho
  have impossible (i j : ℕ) (hji : j < i)
      (f : pCore p A ≃* (Multiplicative (ZMod (p^i)) × Multiplicative (ZMod (p^j)))) : False := by
    obtain ⟨hd, hle⟩ := PrimaryHomocyclicLine.power_line i j hji f
    have hh := trivial_on_subgroup_of_power_line
      (MulAut.conjNormal : A →* MulAut (pCore p A)) s.X hc (p^(i-1)) hd
      (hle.trans s.eq_omega_of_abelian.ge)
    exact s.coreAction_ne_one hh
  have heq : n = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact impossible m n h (e.trans MulEquiv.prodComm)
    · exact impossible n m h e
  subst m
  refine ⟨n, hn, ⟨e.trans ?_⟩⟩
  let t : (Multiplicative (ZMod (p^n)) × Multiplicative (ZMod (p^n))) ≃*
      (Fin 2 → Multiplicative (ZMod (p^n))) :=
    { __ := (piFinTwoEquiv (fun _ : Fin 2 => Multiplicative (ZMod (p^n)))).symm
      map_mul' _ _ := by ext i; fin_cases i <;> rfl }
  exact t.trans (MulEquiv.piMultiplicative (fun _ : Fin 2 => ZMod (p^n))).symm

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
