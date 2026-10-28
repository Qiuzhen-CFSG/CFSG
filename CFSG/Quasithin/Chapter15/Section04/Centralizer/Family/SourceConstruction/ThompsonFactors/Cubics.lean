module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.FactorGeometry
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual alternating residual product

Independent Sylow involutions invert the cubic factors. Their product is
normal, elementary of order 3^r for r=1 or 2, and equals its commutator
with the actual Thompson Sylow image. Together with that Sylow image it
generates the original product of symmetric-three factors.

This supplies the residual and image coverage used in 15.4.12 and the
lower minimal-parabolic application of B.2.18.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (closure S)]

theorem cubicFactor_elementary (d : Exceptional S) (i : Fin d.count) :
    IsElementaryAbelian 3 (cubicFactor d i) := by
  let : IsCyclic (cubicFactor d i) := isCyclic_of_prime_card (cubicFactor_card d i)
  refine { exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (fun x => by simpa only [cubicFactor_card] using pow_card_eq_one' (x := x))

theorem cubicFactors_centralize (d : Exceptional S) (i j : Fin d.count) :
    cubicFactor d j ≤ centralizer (cubicFactor d i : Set (Star (S := S))) := by
  intro y hy x hx
  by_cases hij : i = j
  · subst j
    let := cubicFactor_elementary d i
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : cubicFactor d i) ⟨y,hy⟩)
  · exact factors_commute d hij (cubicFactor_le d i hx) (cubicFactor_le d j hy)

theorem cubicFactors_disjoint (d : Exceptional S) {i j : Fin d.count} (hij : i ≠ j) :
    Disjoint (cubicFactor d i) (cubicFactor d j) :=
  (factors_disjoint d hij).mono (cubicFactor_le d i) (cubicFactor_le d j)

theorem cubicProduct_le (d : Exceptional S) (I : Finset (Fin d.count)) :
    cubicProduct d I ≤ thompsonImage (S := S) :=
  Finset.sup_le fun i _ => (cubicFactor_le d i).trans (factor_le_thompsonImage d i)

theorem cubicProduct_elementary (d : Exceptional S) (I : Finset (Fin d.count))
    (hI : I.card = 1 ∨ I.card = 2) : IsElementaryAbelian 3 (cubicProduct d I) := by
  classical
  rcases hI with hI | hI
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hI
    rw [cubicProduct, Finset.sup_singleton]
    exact cubicFactor_elementary d i
  · obtain ⟨i,j,_,rfl⟩ := Finset.card_eq_two.mp hI
    rw [cubicProduct, Finset.sup_insert, Finset.sup_singleton]
    let := cubicFactor_elementary d i
    let := cubicFactor_elementary d j
    exact IsElementaryAbelian.sup_of_le_centralizer (cubicFactors_centralize d i j)

theorem cubicProduct_card (d : Exceptional S) (I : Finset (Fin d.count))
    (hI : I.card = 1 ∨ I.card = 2) : Nat.card (cubicProduct d I) = 3 ^ I.card := by
  classical
  rcases hI with hI | hI
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hI
    rw [cubicProduct, Finset.sup_singleton, Finset.card_singleton, pow_one, cubicFactor_card]
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hI
    rw [cubicProduct, Finset.sup_insert, Finset.sup_singleton, Finset.card_pair hij,
      card_sup_eq_mul_of_normalizes_of_disjoint _ _
        ((cubicFactors_centralize d i j).trans (Subgroup.centralizer_le_normalizer _))
        (cubicFactors_disjoint d hij), cubicFactor_card, cubicFactor_card]
    rfl

theorem cubicProduct_eq_iSup (d : Exceptional S) :
    cubicProduct d Finset.univ = ⨆ i, cubicFactor d i := by
  classical
  exact Finset.sup_univ_eq_iSup (f := cubicFactor d)

theorem cubicProduct_normal (d : Exceptional S) : (cubicProduct d Finset.univ).Normal := by
  classical
  apply normal_iff_map_conj_eq.mpr
  intro g
  rw [cubicProduct_eq_iSup, Subgroup.map_iSup]
  change (⨆ i, (cubicFactor d i).map (MulAut.conj g).toMonoidHom) = _
  simp only [cubicFactor_action]
  exact Equiv.iSup_comp (factorAction d g)

private theorem perm_inversion : ∀ t x : Equiv.Perm (Fin 3),
    t ≠ 1 → t^2 = 1 → x^3 = 1 → t*x*t⁻¹ = x⁻¹ := by decide +kernel

theorem factor_involution_inverts (d : Exceptional S) (i : Fin d.count)
    {t : Star (S := S)} (ht : t ∈ d.factor i) (ht1 : t ≠ 1) (ht2 : t^2 = 1)
    {x : Star (S := S)} (hx : x ∈ cubicFactor d i) : t*x*t⁻¹ = x⁻¹ := by
  let e := factorModel d i
  let tt : d.factor i := ⟨t,ht⟩
  let xx : d.factor i := ⟨x,cubicFactor_le d i hx⟩
  have h1 : e tt ≠ 1 := by
    intro he
    exact ht1 (congrArg Subtype.val (e.injective (he.trans e.map_one.symm)))
  have h2 : (e tt)^2 = 1 := by
    rw [← map_pow, ← e.map_one]
    exact congrArg e (Subtype.ext ht2)
  have hx3 : x^3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : cubicFactor d i))
    rw [cubicFactor_card] at hh
    exact congrArg Subtype.val hh
  have h3 : (e xx)^3 = 1 := by
    rw [← map_pow, ← e.map_one]
    exact congrArg e (Subtype.ext hx3)
  have hh := perm_inversion (e tt) (e xx) h1 h2 h3
  have he : tt*xx*tt⁻¹ = xx⁻¹ := by
    apply e.injective
    simpa only [map_mul, map_inv] using hh
  exact congrArg Subtype.val he

variable [Finite H]

theorem cubicFactor_le_commutator (d : Exceptional S) (i : Fin d.count) :
    cubicFactor d i ≤ ⁅cubicFactor d i,sylowImage (S := S)⁆ := by
  obtain ⟨t,hti,htS,ht1,ht2⟩ := exists_factor_involution d i
  intro x hx
  have hx3 : x^3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : cubicFactor d i))
    rw [cubicFactor_card] at hh
    exact congrArg Subtype.val hh
  have he : ⁅x⁻¹,t⁆ = x := by
    rw [commutatorElement_def]
    have hh := factor_involution_inverts d i hti ht1 ht2 hx
    rw [inv_inv]
    calc
      x⁻¹*t*x*t⁻¹ = x⁻¹*(t*x*t⁻¹) := by group
      _ = x⁻¹*x⁻¹ := by rw [hh]
      _ = x := by
        have hpow : x^2 = x⁻¹ := (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_succ] using hx3))
        rw [← mul_inv_rev, ← pow_two, hpow, inv_inv]
  rw [← he]
  exact commutator_mem_commutator ((cubicFactor d i).inv_mem hx) htS

theorem cubicProduct_commutator (d : Exceptional S) :
    ⁅cubicProduct d Finset.univ,sylowImage (S := S)⁆ = cubicProduct d Finset.univ := by
  let := cubicProduct_normal d
  apply le_antisymm (commutator_le_left _ _)
  rw [cubicProduct_eq_iSup]
  apply iSup_le
  intro i
  exact (cubicFactor_le_commutator d i).trans (commutator_mono (le_iSup (cubicFactor d) i) le_rfl)

theorem cubicProduct_sylow_sup (d : Exceptional S) (hc : d.count = 1 ∨ d.count = 2) :
    cubicProduct d Finset.univ ⊔ sylowImage (S := S) = thompsonImage (S := S) := by
  classical
  let := cubicProduct_normal d
  have hI : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
      (Finset.univ : Finset (Fin d.count)).card = 2 := by simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have hcard : Nat.card (cubicProduct d Finset.univ) = 3^d.count := by
    simpa only [Finset.card_univ, Fintype.card_fin] using cubicProduct_card d Finset.univ hI
  apply eq_of_le_of_card_ge
  · apply sup_le (cubicProduct_le d _)
    obtain ⟨P,hP⟩ := d.sylow
    change Sylow 2 (thompsonImage (S := S)) at P
    change (P : Subgroup (thompsonImage (S := S))).map thompsonImage.subtype = sylowImage at hP
    rw [← hP]
    exact map_subtype_le _
  · have hdis : Disjoint (cubicProduct d Finset.univ) (sylowImage (S := S)) :=
      disjoint_of_coprime_natCard (by rw [hcard,sylowImage_card d]; exact Nat.Coprime.pow _ _ (by decide))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ (by rw [normalizer_eq_top]; exact le_top) hdis,
      hcard, sylowImage_card d, thompsonImage_card d, ← mul_pow]
    rfl

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
