module

public import Theory.SpecificGroups.MacWilliams.UnitaryFrame
public import Theory.SpecificGroups.MacWilliams.UnitaryGeneratorLifting
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticClassification
public import Theory.SpecificGroups.MacWilliams.UnitaryInvolutions
public import Theory.Frattini.PGroup
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Recognition from the unitary generating relations

A generating tuple satisfying the exact unitary table gives a surjective
presentation homomorphism. If the presentation is finite of order at most 64
and the target has order 64, that homomorphism is bijective. This separates
the presentation argument from the intrinsic construction of the tuple via
the central quotient square map.

Source: the unitary alternative of Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3(b), p.386, and MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow

/-- A tuple generates precisely when its presentation homomorphism is
surjective. This applies to either of the MacWilliams tables. -/
public theorem presentationHom_surjective_iff
    {n : ℕ} {G : Type*} [Group G] {t : Table n} {x : Fin n → G}
    (h : Relations t x) :
    Function.Surjective (presentationHom h) ↔
      Subgroup.closure (Set.range x) = ⊤ := by
  have hrange : (presentationHom h).range = Subgroup.closure (Set.range x) := by
    rw [MonoidHom.range_eq_map, ← generator_closure t, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (presentationHom_generator h i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨generator t i, ⟨i, rfl⟩, presentationHom_generator h i⟩
  rw [← MonoidHom.range_eq_top, hrange]

/-- A finite presentation with no more elements than its generated image is
identified with that image by the universal homomorphism. -/
public noncomputable def presentationEquivOfCardLE
    {n : ℕ} {G : Type*} [Group G] {t : Table n} [Finite (Model t)]
    {x : Fin n → G} (h : Relations t x)
    (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hcard : Nat.card (Model t) ≤ Nat.card G) : Model t ≃* G :=
  MulEquiv.ofBijective (presentationHom h)
    (((presentationHom_surjective_iff h).mpr hgen).bijective_of_nat_card_le hcard)

/-- The equivalence retains the specified labeling of the generators. -/
@[simp] public theorem presentationEquivOfCardLE_generator
    {n : ℕ} {G : Type*} [Group G] {t : Table n} [Finite (Model t)]
    {x : Fin n → G} (h : Relations t x)
    (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hcard : Nat.card (Model t) ≤ Nat.card G) (i : Fin n) :
    presentationEquivOfCardLE h hgen hcard (generator t i) = x i :=
  presentationHom_generator h i

/-- Exact generating relations recognize the unitary presentation once its
finite upper bound and the intrinsic group order are known. -/
public theorem nonempty_unitary_equiv_of_generators
    {P : Type*} [Group P] [Finite UnitarySylow]
    (hmodel : Nat.card UnitarySylow ≤ 64) (hcard : Nat.card P = 64)
    (x : Fin 6 → P) (hrel : Relations unitaryTable x)
    (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Nonempty (P ≃* UnitarySylow) := by
  exact ⟨(presentationEquivOfCardLE hrel hgen (hcard.symm ▸ hmodel)).symm⟩

/-- Intrinsic recognition of the unitary Sylow group from its central quotient
square map. The supplied central and Frattini identities make the quotient a
binary elementary abelian group of order sixteen; the balanced quadratic-frame
normal form then lifts to the exact published six-generator presentation. -/
public theorem nonempty_unitary_equiv_of_intrinsic_data
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (_hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ Subgroup.center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hcard : Nat.card P = 64)
    (hexp : ∀ x : P, x ^ 4 = 1)
    (hder : Subgroup.center P = commutator P)
    (hPhi : Subgroup.center P = frattini P)
    (hZelem : IsElementaryAbelian 2 (Subgroup.center P))
    (hZcard : Nat.card (Subgroup.center P) = 4) :
    Nonempty (P ≃* MacWilliamsSylow.UnitarySylow) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (Subgroup.center P) := hZelem
  have hD : commutator P ≤ Subgroup.center P := by
    rw [← hder]
  let : IsElementaryAbelian 2 (P ⧸ Subgroup.center P) := by
    let _ : IsMulCommutative (P ⧸ Subgroup.center P) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hD
    apply IsElementaryAbelian.mk
    apply (Monoid.exponent_dvd_iff_forall_pow_eq_one).2
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    apply (QuotientGroup.eq_one_iff (N := Subgroup.center P) (x := x ^ 2)).2
    have hf := pth_power_mem_frattini_of_isPGroup (R := P) (p := 2) x
    rw [← hPhi] at hf
    exact hf
  have hqcard : Nat.card (P ⧸ Subgroup.center P) = 16 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    rw [hcard, hZcard] at hh
    omega
  obtain ⟨square, polar, hsq1, hsq, hpol, han, hsqev, hpolev, hbal, hlift⟩ :=
    exists_balanced_square_data_and_generating_lifts
      hD hcentral hthree htrans hexp hcard hZcard
  obtain ⟨F⟩ :=
    exists_unitaryQuadraticFrame hqcard hZcard square polar hsq1 hsq hpol han hbal
  obtain ⟨x, hrel, hgen⟩ := hlift F
  have hmodel : Nat.card UnitarySylow ≤ 64 := by
    rw [unitarySylow_card]
  exact nonempty_unitary_equiv_of_generators hmodel hcard x hrel hgen

end MacWilliamsSylow
