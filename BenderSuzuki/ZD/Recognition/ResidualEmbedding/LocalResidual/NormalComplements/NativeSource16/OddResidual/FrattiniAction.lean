module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.FrattiniLines

/-!
# The literal Frattini action and the product tuv

Cyclicity of the four source subgroups R_u, R_v, R_tu and R_tv descends to
their fixed subgroups in R/Φ(R). Noncyclicity forces this quotient to be an
actual p²-plane. The opposite inversion on R_v makes the two fixed lines
distinct, so the checked fixed-plane theorem gives trivial action of tuv.
Burnside's Frattini automorphism theorem then lifts this to centralization
of the original subgroup R. Every action and quotient here is the original
ambient conjugation action.

Source: GLS IV, Chapter 2, Proposition 16.5, last two paragraphs.
-/

namespace BenderSuzuki.ZD.Source16OddResidual
open Subgroup Theory.GroupTheory OddInvolutionFrattini
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  (P A : Subgroup G) [IsElementaryAbelian 2 A] (hP : IsPGroup p P)
  (hp : Odd p) (hAP : A ≤ normalizer P) {t u v : G}
  (htA : t∈A) (huA : u∈A) (hvA : v∈A) (ht : PFAppendixIII.IsInvolution t)

include hP hp ht in
private theorem fixed_cyclic_of_rw {w : G} (hwA : w∈A) (hc : IsCyclic (Rw P t w)) :
    IsCyclic (MulAut.fixedSubgroup
      (quotientConjugation A (R P t) (normalizes_R P A hAP htA) ⟨w,hwA⟩)) := by
  let := hc
  rw [←image_rw_eq_fixed P A hP hp hAP htA hwA ht]
  let f := QuotientGroup.mk' (frattini (R P t))
  let S := (Rw P t w).subgroupOf (R P t)
  let : IsCyclic S := isCyclic_of_injective
    (subgroupOfEquivOfLe (rw_le P t w)).toMonoidHom
    (subgroupOfEquivOfLe (rw_le P t w)).injective
  exact isCyclic_of_surjective (f.subgroupMap S) (f.subgroupMap_surjective S)

include A hP hp hAP htA huA hvA ht in
/-- The source fixed-line argument proves centralization of the original R
by the literal product tuv, with no prescribed cardinality of R/Φ(R). -/
public theorem product_centralizes_of_cyclic_fixed_commutators
    (hu : IsCyclic (Rw P t u)) (hv : IsCyclic (Rw P t v))
    (htu : IsCyclic (Rw P t (t*u))) (htv : IsCyclic (Rw P t (t*v)))
    (hn : ¬IsCyclic (R P t))
    (huRv : ∀x∈Rw P t v, u*x*u⁻¹=x⁻¹) :
    Nat.card (R P t ⧸ frattini (R P t))=p^2 ∧
      R P t ≤ centralizer ({t*u*v} : Set G) := by
  let H := R P t
  let E := H ⧸ frattini H
  let hAR := normalizes_R P A hAP htA
  let f := quotientConjugation A H hAR
  let τA : A := ⟨t,htA⟩
  let au : A := ⟨u,huA⟩
  let av : A := ⟨v,hvA⟩
  have hHp : IsPGroup p H := hP.of_injective
    (inclusion (r_le P (hAP htA))) (inclusion_injective _)
  let : Fact (IsPGroup p H) := ⟨hHp⟩
  let : IsElementaryAbelian p E := isElementaryAbelian_quotient_frattini
  have ha2 (a : A) : a^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hi (a : A) : Function.Involutive (f a) := by
    intro x
    have he : (f a)^2=1 := by rw [←map_pow,ha2,map_one]
    exact congrArg (fun g : MulAut E => g x) he
  have htinv : ∀x:E, f τA x=x⁻¹ := inverts_frattini_quotient P A hP hAP htA ht
  have hnc : ¬IsCyclic E := noncyclic_frattini_quotient hn
  have hcu : IsCyclic (f au).fixedSubgroup := fixed_cyclic_of_rw P A hP hp hAP htA ht huA hu
  have hcv : IsCyclic (f av).fixedSubgroup := fixed_cyclic_of_rw P A hP hp hAP htA ht hvA hv
  have hctu : IsCyclic (f τA*f au).fixedSubgroup := by
    rw [←map_mul]
    exact fixed_cyclic_of_rw P A hP hp hAP htA ht (A.mul_mem htA huA) htu
  have hctv : IsCyclic (f τA*f av).fixedSubgroup := by
    rw [←map_mul]
    exact fixed_cyclic_of_rw P A hP hp hAP htA ht (A.mul_mem htA hvA) htv
  obtain ⟨hcard,hucard,_⟩ := fixed_lines_of_cyclic hp (f au) (f τA) (hi au) htinv hcu hctu hnc
  have hvcard := (fixed_lines_of_cyclic hp (f av) (f τA) (hi av) htinv hcv hctv hnc).2.1
  have hflip : ∀x∈(f av).fixedSubgroup, f au x=x⁻¹ := by
    intro x hx
    rw [←image_rw_eq_fixed P A hP hp hAP htA hvA ht] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [quotientConjugation_mk, ←map_inv]
    congr 1
    apply Subtype.ext
    exact huRv y hy
  have hne : ¬(f av).fixedSubgroup ≤ (f au).fixedSubgroup := by
    intro hle
    have heq : (f av).fixedSubgroup=⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hxinv : x=x⁻¹ := ((MulAut.mem_fixedSubgroup _ _).mp (hle hx)).symm.trans (hflip x hx)
      have hx2 : x^2=1 := by rw [pow_two,eq_inv_iff_mul_eq_one.mp hxinv]
      have hxp : x^p=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) x
      have ho := Nat.eq_one_of_dvd_coprimes hp.coprime_two_right
        (orderOf_dvd_of_pow_eq_one hxp) (orderOf_dvd_of_pow_eq_one hx2)
      exact orderOf_eq_one_iff.mp ho
    simp only [heq,Subgroup.card_bot] at hvcard
    exact (Fact.out : p.Prime).ne_one hvcard.symm
  have hc : Commute (f au) (f av) := (Commute.all au av).map f
  have htriv : f (τA*au*av)=1 := by
    rw [map_mul,map_mul]
    exact Theory.GroupAction.inversion_mul_commuting_fixed_lines_eq_one
      (Fact.out : p.Prime) hcard (f au) (f av) (f τA) (hi au) (hi av) hc hucard hvcard hne htinv
  exact ⟨hcard,centralizes_of_quotientConjugation_eq_one A H hHp hp hAR (τA*au*av)
    (ha2 _) htriv⟩

end BenderSuzuki.ZD.Source16OddResidual
