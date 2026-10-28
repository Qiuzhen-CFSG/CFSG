module
public import ABG.ChapterII.Section3.QSylowExtensionData
public import ABG.ChapterII.Section3.LinearCentralLayer
public import ABG.ChapterII.Section3.UnitaryCentralLayer

/-!
# Concrete matrix recognition of the actual Q-group central layer

For any supplied Sylow two-subgroup R of a finite enlarged Q-group H with
trivial odd core and a supplied normal SL2(GF(p^d)) subgroup L0, an exact
center radius r gives concrete linear and unitary central-join models under
their respective field divisibilities. The main at-Sylow interface retains
the original R and radius, so subsequent extension geometry can choose its
model without replacing the Sylow witness. The existential wrapper chooses
a valid radius and one of the two models from the source geometry.
The original Sylow center has order 2^(r+1) and maps to the full model
center. The chosen equivalence preserves the prescribed SL2 map, using
an explicitly supplied SU2-to-SL2 equivalence in the unitary alternative.
This permits a later coefficient-equivariant choice of unitary coordinates.

The projective decomposition's element equation identifies the intersection
Z(R) with L0 as the kernel of the SL2 projective cover, of order two. The
actual Sylow extension geometry supplies the center radius and exact field
two-part. In the semidihedral/quaternion branch the radius is zero; in the
wreathed-overgroup branch it is below the field two-part exponent. These
divisibilities feed the existing concrete central-product recognition
theorems. Every matrix group is the original determinant-defined subgroup;
fields of orders three and nine and proper quaternion overgroups remain.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26.
This proves its central-layer matrix identification; recognition of the
possible exterior index-two extension and the semilinear action are later
steps and are not assumed here.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup
universe u

private theorem central_intersection_card
    {H : Type u} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (R : Sylow 2 H)
    (L0 : Subgroup H) [L0.Normal] (F : Type u) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nat.card (subgroupCenter (R : Subgroup H) ⊓ L0 : Subgroup H) = 2 := by
  let Z := subgroupCenter (R : Subgroup H)
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH R
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  obtain ⟨_, _, _, _, f, L, E, hfker, _, _, _, _, _, _, _, _, _, _, hfcore⟩ :=
    qGroup_projective_linear_complement_with_core_map hH hcore R Z rfl L0 F hF eL0
  have hZI : Z.subgroupOf L0 = (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).comap
      eL0.toMonoidHom := by
    ext l
    change (l : H) ∈ Z ↔ eL0 l ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)
    rw [← hfker]
    change f l = 1 ↔ _
    rw [hfcore]
    have hi (x : Matrix.SpecialLinearGroup (Fin 2) F) :
        x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔
          sl2ProjectiveProjection F x = 1 := by
      exact (QuotientGroup.eq_one_iff x).symm
    rw [hi]
    change SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (sl2ProjectiveProjection F (eL0 l))) = 1 ↔ sl2ProjectiveProjection F (eL0 l) = 1
    constructor
    · intro h
      have h1 := SemidirectProduct.inl_injective (h.trans (map_one _).symm)
      exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (h1.trans (map_one _).symm)
    · intro h
      simp only [h, map_one]
  have hcard : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
    rw [← sl2ProjectiveProjection_ker F]
    apply sl2ProjectiveProjection_ker_card
    obtain ⟨p, n, _, hp, _, he⟩ := hF
    rw [he]
    exact hp.pow
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L0.subtype_injective,
    hZI]
  rw [← Subgroup.card_map_of_injective (f := eL0.toMonoidHom) eL0.injective,
    Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr eL0.surjective, top_inf_eq]
  exact hcard

public theorem qGroup_central_layer_matrix_models_at_sylow
    {H : Type} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (L0 : Subgroup H) [L0.Normal]
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (eSU : (unitaryForm 2 p d hd).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (R : Sylow 2 H) (r : ℕ)
    (hcard : Nat.card (subgroupCenter (R : Subgroup H)) = 2 ^ (r + 1)) :
    let Z := subgroupCenter (R : Subgroup H)
    (2 ^ (r + 1) ∣ p ^ d - 1 →
      ∃ e : (Z ⊔ L0 : Subgroup H) ≃* determinantTwoPower (GaloisField p d) r,
        (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val =
          Matrix.SpecialLinearGroup.toGL (eL0 l)) ∧
        (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom =
          Subgroup.center (determinantTwoPower (GaloisField p d) r)) ∧
    (2 ^ (r + 1) ∣ p ^ d + 1 →
      ∃ e : (Z ⊔ L0 : Subgroup H) ≃* SU2Level p d hd r,
        (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val.val =
          (eSU.symm (eL0 l)).val) ∧
        (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom = Subgroup.center (SU2Level p d hd r)) := by
  let F := GaloisField p d
  have hFc : Nat.card F = p ^ d := GaloisField.card p d hd
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, d, Fact.out, hp, by omega, hFc⟩
  have hFo : Odd (Nat.card F) := hFc ▸ hp.pow
  let Z := subgroupCenter (R : Subgroup H)
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH R
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : IsCyclic Z :=
    ((Subgroup.center R).equivMapOfInjective (R : Subgroup H).subtype
      (R : Subgroup H).subtype_injective).isCyclic.mp
        (qGroup_sylow_center_quotient_geometry hH R).1
  have hcap := central_intersection_card hH hcore R L0 F hF eL0
  exact ⟨fun hdiv => linear_central_layer_model F hFo r (hFc ▸ hdiv)
      Z L0 hZc hcard hcap eL0,
    fun hdiv => unitary_central_layer_model p d hp hd r hdiv
      Z L0 hZc hcard hcap eL0 eSU⟩

public theorem qGroup_central_layer_matrix_model
    {H : Type} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (L0 : Subgroup H) [L0.Normal]
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (eSU : (unitaryForm 2 p d hd).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d)) :
    ∃ (R : Sylow 2 H) (r : ℕ), let Z := subgroupCenter (R : Subgroup H)
      Nat.card Z = 2 ^ (r + 1) ∧
      ((∃ e : (Z ⊔ L0 : Subgroup H) ≃* determinantTwoPower (GaloisField p d) r,
        (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val =
          Matrix.SpecialLinearGroup.toGL (eL0 l)) ∧
        (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom =
          Subgroup.center (determinantTwoPower (GaloisField p d) r)) ∨
      (∃ e : (Z ⊔ L0 : Subgroup H) ≃* SU2Level p d hd r,
        (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val.val =
          (eSU.symm (eL0 l)).val) ∧
        (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom = Subgroup.center (SU2Level p d hd r))) := by
  let F := GaloisField p d
  have hFc : Nat.card F = p ^ d := GaloisField.card p d hd
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, d, Fact.out, hp, by omega, hFc⟩
  have hFo : Odd (Nat.card F) := hFc ▸ hp.pow
  obtain ⟨R, n, hn, hfield, hgeo⟩ :=
    qGroup_sylow_normal_sl2_extension_data hH hcore L0 F hF eL0
  let Z := subgroupCenter (R : Subgroup H)
  have hzcard : Nat.card Z = Nat.card (Subgroup.center R) :=
    Subgroup.card_map_of_injective (R : Subgroup H).subtype_injective
  have build (r : ℕ) (hc : Nat.card Z = 2 ^ (r + 1))
      (hdiv : 2 ^ (r + 1) ∣ Nat.card F - 1 ∨ 2 ^ (r + 1) ∣ Nat.card F + 1) :
      (∃ e : (Z ⊔ L0 : Subgroup H) ≃* determinantTwoPower F r,
        (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val =
          Matrix.SpecialLinearGroup.toGL (eL0 l)) ∧
        (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom = Subgroup.center (determinantTwoPower F r)) ∨
      (∃ e : (Z ⊔ L0 : Subgroup H) ≃* SU2Level p d hd r,
        (∀ l : L0, (e ⟨l.val, (show L0 ≤ Z ⊔ L0 from le_sup_right) l.property⟩).val.val =
          (eSU.symm (eL0 l)).val) ∧
        (Z.subgroupOf (Z ⊔ L0)).map e.toMonoidHom = Subgroup.center (SU2Level p d hd r)) := by
    obtain ⟨hlin, huni⟩ := qGroup_central_layer_matrix_models_at_sylow
      hH hcore L0 p d hp hd eL0 eSU R r hc
    rcases hdiv with hm | hp'
    · exact Or.inl (hlin (hFc ▸ hm))
    · exact Or.inr (huni (hFc ▸ hp'))
  rcases hgeo with ⟨_, hc, _⟩ | ⟨r, hr, hc, _⟩
  · have hc' : Nat.card Z = 2 ^ (0 + 1) := by simpa using hzcard.trans hc
    refine ⟨R, 0, hc', build 0 hc' ?_⟩
    rcases hfield with hlin | huni
    · right
      simp only [zero_add, pow_one]
      exact even_iff_two_dvd.mp hFo.add_one
    · left
      simp only [zero_add, pow_one]
      exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hFo odd_one)
  · have hc' := hzcard.trans hc
    refine ⟨R, r, hc', build r hc' ?_⟩
    have hpow : 2 ^ (r + 1) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
    rcases hfield with hlin | huni
    · exact Or.inl (hpow.trans hlin.2.1)
    · exact Or.inr (hpow.trans huni.2.1)

end ABG
