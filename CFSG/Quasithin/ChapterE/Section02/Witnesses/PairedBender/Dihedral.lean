module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Linear
import all CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Basic

/-!
# The order-two projected paired witness

An involution in the nontrivial order-two first projection inverts an odd
prime rotation. Lift that rotation in the first factor and use every element
of the original V: each either fixes or inverts it. The original maximal
two-core makes the rotation disjoint from M. The resulting internal pair
has Sylow exactly V and a genuine odd dihedral quotient, including diagonal
second-coordinate kernels.

Source: Aschbacher–Smith E.2.7, printed p.219, paired rank-one subcase.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
variable {H G A : Type*} [Group H] [Finite H] [Group G] [Finite G] [Group A]

omit [Finite H] in
private theorem pair_of_coreFree (T : Sylow 2 H) (M V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T) {p : ℕ}
    (w : Solvable.CoreFreeWitness M V p) :
    ∃ u : QuotientLift.Pair T M V, ∃a : ℕ, 0<a ∧
      Nonempty (u.subgroup ⧸ (M.subgroupOf u.subgroup).normalCore ≃* DihedralGroup (p^a)) := by
  have hTS : (T : Subgroup H).subgroupOf w.subgroup = w.sylow := by
    apply w.sylow.is_maximal' T.isPGroup'.comap_subtype
    intro x hx
    have hv := mem_map_of_mem w.subgroup.subtype hx
    rw [w.sylow_eq] at hv
    exact hVT hv
  have htwo : IsPGroup 2 (M.subgroupOf w.subgroup).normalCore := by
    rw [w.maximal_eq]
    exact ((IsElementaryAbelian.isPGroup 2 V).comap_subtype).to_le (normalCore_le _)
  have hclosed : ∃S : Sylow 2 (M.subgroupOf w.subgroup).normalCore,
      (S : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal := by
    refine ⟨(htwo.to_subgroup ⊤).toSylow (by simp),?_⟩
    exact inferInstanceAs (⊤ : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal
  let u : QuotientLift.Pair T M V :=
    ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,by
      rw [← hTS,subgroupOf_map_subtype],hclosed⟩
  exact ⟨u,w.exponent,w.positive,w.dihedral⟩

/-- A nontrivial order-two projection gives the dihedral E.2.4 alternative
on the full original elementary subgroup, including a diagonal kernel. -/
theorem exists_dihedral_product (W : Subgroup (G × A)) [IsElementaryAbelian 2 W]
    (hc : Nat.card (W.map (MonoidHom.fst G A)) = 2)
    (hcoreG : pCore 2 G = ⊥) (T : Sylow 2 H) (M : Subgroup H)
    (f : G × A →* H) (hf : Function.Injective f)
    (hVT : W.map f ≤ T) (hVM : W.map f ≤ M.pCoreIn 2) :
    ∃p : ℕ,p.Prime ∧ p≠2 ∧ ∃u : QuotientLift.Pair T M (W.map f),
      ∃a : ℕ,0<a ∧ Nonempty (u.subgroup ⧸ (M.subgroupOf u.subgroup).normalCore ≃*
        DihedralGroup (p^a)) := by
  let U := W.map (MonoidHom.fst G A)
  let V := W.map f
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hUn : U ≠ ⊥ := by
    intro he
    have hh := card_eq_one.mpr he
    change Nat.card U=2 at hc
    omega
  obtain ⟨v,hv,hv1⟩ := U.bot_or_exists_ne_one.resolve_left hUn
  obtain ⟨w,hw,hwv⟩ := hv
  have hvU : v∈U := ⟨w,hw,hwv⟩
  have hv2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hvU
  have hinv : BenderSuzuki.PFAppendixIII.IsInvolution v := ⟨hv1,hv2⟩
  have hvout : v ∉ pCore 2 G := by rw [hcoreG,mem_bot]; exact hv1
  obtain ⟨p,hp,hp2,r,hr,hi⟩ := BenderSuzuki.involution_outside_twoCore_inverts_odd_prime v hinv hvout
  let : Fact p.Prime := ⟨hp⟩
  let rr : H := f (r,1)
  let vv : H := f w
  have hiG : v*r*v⁻¹ = r⁻¹ := by
    simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem,hinv.inv_eq_self] using hi
  have hiv : vv*rr*vv⁻¹ = rr⁻¹ := by
    change f w * f (r,1) * (f w)⁻¹ = (f (r,1))⁻¹
    rw [← map_inv,← map_mul,← map_mul,← map_inv]
    apply congrArg f
    apply Prod.ext
    · change w.1*r*w.1⁻¹=r⁻¹
      change w.1=v at hwv
      rwa [hwv]
    · simp
  have hrr : orderOf rr=p := by
    rw [orderOf_injective f hf]
    have hh := orderOf_injective (MonoidHom.inl G A) (by intro x y h; exact congrArg Prod.fst h) r
    exact hh.trans hr
  have hvV : vv ∈ V := mem_map_of_mem f hw
  have hrrM : rr ∉ M := Involution.rotation_not_mem_of_inverter_in_core M vv rr hp2
    (hVM hvV) hrr hiv
  have hdM : Disjoint (zpowers rr) M := (M.disjoint_zpowers_of_prime_order_not_mem rr hrr hrrM).symm
  have hsign : ∀z∈V,z*rr*z⁻¹=rr ∨ z*rr*z⁻¹=rr⁻¹ := by
    rintro z ⟨a,ha,rfl⟩
    have haU : a.1∈U := mem_map_of_mem (MonoidHom.fst G A) ha
    have ha1 : a.1=1 ∨ a.1=v := by
      by_cases h:a.1=1
      · exact Or.inl h
      · right
        obtain ⟨b,hb,hu⟩ := (Nat.card_eq_two_iff' (1:U)).mp hc
        exact congrArg Subtype.val ((hu ⟨a.1,haU⟩ (fun he=>h (congrArg Subtype.val he))).trans
          (hu ⟨v,hvU⟩ (fun he=>hv1 (congrArg Subtype.val he))).symm)
    have heq : f a * rr * (f a)⁻¹ = f (a.1*r*a.1⁻¹,1) := by
      change f a*f (r,1)*(f a)⁻¹ = _
      rw [← map_inv,← map_mul,← map_mul]
      apply congrArg f
      apply Prod.ext
      · rfl
      · simp
    rw [heq]
    rcases ha1 with ha1 | hav
    · left
      simp only [ha1,one_mul,inv_one,mul_one]
      rfl
    · right
      rw [hav,hiG]
      change f (r⁻¹,1) = (f (r,1))⁻¹
      simpa using map_inv f (r,1)
  obtain ⟨w⟩ := Involution.witness_of_inverted_line M V (hVM.trans (pCoreIn_le 2 M))
    rr vv 1 hvV (by decide) (by simpa only [pow_one] using hrr)
    (hrr ▸ hp.odd_of_ne_two hp2) (fun h=>hp.ne_one (hrr.symm.trans (h ▸ orderOf_one)))
    hiv hsign hdM
  exact ⟨p,hp,hp2,pair_of_coreFree T M V hVT w⟩
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender
