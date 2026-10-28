module

public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic
public meta import Mathlib.Algebra.Group.End

/-!
# A normal four-group of squares in C₂ times S₄

For a finite group isomorphic to `C₂ × S₄`, there is a normal elementary
abelian subgroup of order four all of whose elements are squares. Its
centralizer is precisely the two-core of the whole group.

In `S₄` the permutations whose squares are one and which are themselves
squares form the usual Klein four subgroup: its three nonidentity elements
are squares of four-cycles. Kernel-checked finite calculations verify its
normality, elementary abelianness, order, and self-centralizing property.
The required subgroup is its product with the identity of `C₂`. Its
centralizer is the product with the whole `C₂`, a normal elementary group
of order eight. The existing symmetric-four model core theorem identifies
this centralizer with the two-core by containment and cardinality. A group
isomorphism transports all properties to the supplied group.

This intrinsic calculation supplies the square four-group used in
Kurzweil–Stellmacher, *The Theory of Finite Groups*, Chapter 12, proof of
Theorem 3, printed pp. 365–366 (`refs/latex/kurzweil.tex`). The source uses
`O₂(O²(P))`; the witness here has the needed properties without introducing
an additional residual-subgroup interface. All concrete subgroups and
intermediate computations remain private.
-/

private abbrev S4 := Equiv.Perm (Fin 4)
private abbrev C2 := Multiplicative (ZMod 2)

set_option maxRecDepth 10000 in
private def squareFour : Subgroup S4 where
  carrier := {sigma | sigma ^ 2 = 1 ∧ ∃ tau : S4, tau ^ 2 = sigma}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

private instance : DecidablePred (· ∈ squareFour) :=
  fun sigma => inferInstanceAs (Decidable (sigma ^ 2 = 1 ∧ ∃ tau : S4, tau ^ 2 = sigma))

set_option maxRecDepth 10000 in
private instance : squareFour.Normal where
  conj_mem := by decide

set_option maxRecDepth 10000 in
private instance : IsElementaryAbelian 2 squareFour where
  is_comm.comm := by decide
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide)

set_option maxRecDepth 10000 in
private theorem squareFour_card : Nat.card squareFour = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 10000 in
private theorem squareFour_selfCentralizing :
    Subgroup.centralizer (squareFour : Set S4) = squareFour := by
  ext sigma
  change (∀ tau : S4, tau ∈ squareFour → tau * sigma = sigma * tau) ↔ sigma ∈ squareFour
  revert sigma
  decide

private def modelPlane : Subgroup (C2 × S4) :=
  (⊥ : Subgroup C2).prod squareFour

private def modelCentralizer : Subgroup (C2 × S4) :=
  (⊤ : Subgroup C2).prod squareFour

private instance : modelPlane.Normal :=
  inferInstanceAs (((⊥ : Subgroup C2).prod squareFour).Normal)

private instance : modelCentralizer.Normal :=
  inferInstanceAs (((⊤ : Subgroup C2).prod squareFour).Normal)

private instance : IsElementaryAbelian 2 modelCentralizer where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · exact mul_comm _ _
    · exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨x.1.2, x.2.2⟩ : squareFour)
          ⟨y.1.2, y.2.2⟩)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (show ∀ c : C2, c ^ 2 = 1 by decide) x.1.1
    · exact x.2.2.1

private instance : IsElementaryAbelian 2 modelPlane where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · exact mul_comm _ _
    · exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨x.1.2, x.2.2⟩ : squareFour)
          ⟨y.1.2, y.2.2⟩)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (show ∀ c : C2, c ^ 2 = 1 by decide) x.1.1
    · exact x.2.2.1

private theorem modelPlane_card : Nat.card modelPlane = 4 := by
  change Nat.card ((⊥ : Subgroup C2).prod squareFour) = 4
  rw [Nat.card_congr ((⊥ : Subgroup C2).prodEquiv squareFour).toEquiv,
    Nat.card_prod, Subgroup.card_bot, squareFour_card, one_mul]

private theorem modelCentralizer_card : Nat.card modelCentralizer = 8 := by
  change Nat.card ((⊤ : Subgroup C2).prod squareFour) = 8
  rw [Nat.card_congr ((⊤ : Subgroup C2).prodEquiv squareFour).toEquiv,
    Nat.card_prod, Subgroup.card_top, squareFour_card]
  norm_num [Nat.card_eq_fintype_card]

private theorem modelCentralizer_eq_core : modelCentralizer = pCore 2 (C2 × S4) := by
  have hle : modelCentralizer ≤ pCore 2 (C2 × S4) :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 modelCentralizer⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  have hd := (symmetric_four_model_twoCore_data
    (K := C2 × S4) (Or.inr ⟨MulEquiv.refl _⟩)).2
  rw [modelCentralizer_card]
  rcases hd with h | h
  · exact h.1.le.trans (by decide)
  · exact h.1.le

private theorem modelPlane_centralizer :
    Subgroup.centralizer (modelPlane : Set (C2 × S4)) = modelCentralizer := by
  ext x
  constructor
  · intro hx
    refine ⟨Subgroup.mem_top _, ?_⟩
    rw [← squareFour_selfCentralizing]
    intro y hy
    exact congrArg Prod.snd (hx (1, y) ⟨Subgroup.one_mem _, hy⟩)
  · rintro ⟨_, hx⟩ y hy
    apply Prod.ext
    · exact mul_comm _ _
    · have hxcent : x.2 ∈ Subgroup.centralizer (squareFour : Set S4) :=
        squareFour_selfCentralizing.symm ▸ hx
      exact hxcent y.2 hy.2

private theorem modelPlane_square (q : C2 × S4) (hq : q ∈ modelPlane) :
    ∃ x : C2 × S4, x ^ 2 = q := by
  obtain ⟨r, hr⟩ := hq.2.2
  refine ⟨(1, r), ?_⟩
  apply Prod.ext
  · exact (Subgroup.mem_bot.mp hq.1).symm
  · exact hr

/-- A `C₂ × S₄` model contains a normal elementary four-group of squares
whose centralizer is the two-core. -/
public theorem c2s4_exists_square_plane
    {K : Type*} [Group K] [Finite K]
    (hModel : Nonempty (K ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    ∃ Q : Subgroup K, Q.Normal ∧ IsElementaryAbelian 2 Q ∧ Nat.card Q = 4 ∧
      (∀ q : K, q ∈ Q → ∃ x : K, x ^ 2 = q) ∧
      Subgroup.centralizer (Q : Set K) = pCore 2 K := by
  obtain ⟨e⟩ := hModel
  let Q := modelPlane.map e.symm.toMonoidHom
  refine ⟨Q, Subgroup.Normal.map inferInstance _ e.symm.surjective,
    IsElementaryAbelian.map _, ?_, ?_, ?_⟩
  · exact (Subgroup.card_map_of_injective e.symm.injective).trans modelPlane_card
  · rintro q ⟨q₀, hq₀, rfl⟩
    obtain ⟨r, hr⟩ := modelPlane_square q₀ hq₀
    refine ⟨e.symm r, ?_⟩
    change e.symm r ^ 2 = e.symm q₀
    rw [← map_pow, hr]
  · have hcent : Subgroup.centralizer (Q : Set K) =
        (Subgroup.centralizer (modelPlane : Set (C2 × S4))).comap e.toMonoidHom := by
      ext x
      constructor
      · intro hx y hy
        apply e.symm.injective
        simpa only [map_mul, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using
          hx (e.symm y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      · intro hx
        rintro y ⟨z, hz, rfl⟩
        apply e.injective
        simpa only [map_mul, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hx z hz
    rw [hcent, modelPlane_centralizer, modelCentralizer_eq_core,
      ← pCore_map_iso 2 e, Subgroup.comap_map_eq_self_of_injective e.injective]
