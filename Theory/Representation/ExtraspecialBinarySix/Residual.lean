module
public import Theory.Representation.ExtraspecialBinarySix.CyclicCentralizer
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.NormalInvariants
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupAction.QuotientConjugation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# The residual above a faithful extraspecial binary six-space

Let a finite group act faithfully on a binary six-space and contain a normal
extraspecial subgroup of order27. A center-fixing involution with displacement
at most two makes its centralizer cover the quotient. The faithful quotient
embeds in GL2(3). If the ambient group is a quotient of a group of three-rank
at most two, the source centralizer theorem makes its three-subgroups cyclic.
The small displacement lemma excludes order nine, forcing the quotient to
be a two-group and the extraspecial subgroup to be the actual two-residual.

All actions, centralizers and quotient maps are the original ones. This is
the residual identification in Aschbacher--Smith 15.1.2, printed p.1086,
before applying Sylow irreducibility on the extraspecial Frattini quotient.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Representation.ExtraspecialBinarySix
variable {G V : Type*} [Group G] [Finite G]
 [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem quotient_action_ker
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P]
    (hC : centralizer (P : Set G) ≤ P) :
    (((quotientAut (frattini P)).comp MulAut.conjNormal) : G →* MulAut (P ⧸ frattini P)).ker = P := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · intro x hx
    have hi : (MulAut.conjNormal x : MulAut P) ∈ (MulAut.conj : P →* MulAut P).range := by
      rw [← IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := 3)]
      exact hx
    obtain ⟨y, hy⟩ := hi
    have he : (MulAut.conjNormal (y : G) : MulAut P) = MulAut.conjNormal x := by
      rw [MulAut.conjNormal_val]
      exact hy
    have hc : (y : G)⁻¹ * x ∈ centralizer (P : Set G) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer P]
      change (MulAut.conjNormal ((y : G)⁻¹ * x) : MulAut P) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using P.mul_mem y.property (hC hc)
  · intro x hx
    change MulAut.conjNormal x ∈ (quotientAut (frattini P)).ker
    rw [IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := 3)]
    exact ⟨⟨x,hx⟩,(MulAut.conjNormal_val (h := (⟨x,hx⟩ : P))).symm⟩

private theorem quotient_card_and_central_inverter
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P]
    (hC : centralizer (P : Set G) ≤ P) (hc : Nat.card P = 27)
    (t : G) (hinv : ∀ r : P, QuotientGroup.mk' (frattini P) (MulAut.conjNormal t r) =
      (QuotientGroup.mk' (frattini P) r)⁻¹) :
    Nat.card (G ⧸ P) ∣ 48 ∧ QuotientGroup.mk' P t ∈ center (G ⧸ P) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E := P ⧸ frattini P
  let : IsElementaryAbelian 3 E := by
    dsimp only [E]
    let := IsExtraspecial.quotient_elementary_abelian 3 P
    let e := QuotientGroup.quotientMulEquivOfEq (IsExtraspecial.frattini_eq_center (p := 3) (P := P))
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hE : Nat.card E = 9 := by
    have hh := (frattini P).card_eq_card_quotient_mul_card_subgroup
    rw [hc,IsExtraspecial.frattini_eq_center (p := 3),IsExtraspecial.center_order_p 3 P] at hh
    change Nat.card (P ⧸ frattini P) = 9
    rw [IsExtraspecial.frattini_eq_center (p := 3)]
    omega
  let β : G →* MulAut E := (quotientAut (frattini P)).comp MulAut.conjNormal
  have hk : β.ker = P := quotient_action_ker P hC
  let b := QuotientGroup.lift P β hk.ge
  have hb : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff b).mp
    apply bot_unique
    intro x hx
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective P x
    have hy : y ∈ β.ker := hx
    rw [hk] at hy
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have ht : ∀ v : E, β t v = v⁻¹ := by
    intro v
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) v
    change quotientAut (frattini P) (MulAut.conjNormal t) _ = _
    rw [quotientAut_apply_mk]
    exact hinv r
  obtain ⟨a,ha⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) E (by rw [hE]; decide)
  have h48 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  refine ⟨?_,?_⟩
  · rw [← h48]
    exact card_dvd_of_injective (a.comp b) (ha.comp hb)
  · rw [mem_center_iff]
    intro x
    apply hb
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective P x
    rw [map_mul,map_mul]
    change β y * β t = β t * β y
    apply MulEquiv.ext
    intro v
    change β y (β t v) = β t (β y v)
    rw [ht,ht,map_inv]

private theorem centralizer_surjective (P : Subgroup G) [P.Normal]
    (hodd : Odd (Nat.card P)) (t : G) (ht : orderOf t = 2)
    (hz : QuotientGroup.mk' P t ∈ center (G ⧸ P)) :
    Function.Surjective ((QuotientGroup.mk' P).comp (centralizer ({t} : Set G)).subtype) := by
  let q := QuotientGroup.mk' P
  have hk : Nat.Coprime 2 (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using Nat.coprime_two_left.mpr hodd
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P v
  have hxord : orderOf (MulAut.conj x t) = 2 := ((MulAut.conj x).orderOf_eq t).trans ht
  have hxq : q (MulAut.conj x t) = q t := by
    change q (x * t * x⁻¹) = q t
    rw [map_mul, map_mul, map_inv, Subgroup.mem_center_iff.mp hz (q x), mul_inv_cancel_right]
  obtain ⟨g, hg⟩ := involutions_same_image_conj_ker q hk hxord ht hxq
  have hct : (g : G) * x ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using hg
  refine ⟨⟨(g : G) * x, hct⟩, ?_⟩
  change q ((g : G) * x) = q x
  rw [map_mul, g.property, one_mul]

private theorem odd_isTwoPerfect {H : Type*} [Group H] [Finite H]
    (hodd : Odd (Nat.card H)) : IsPPerfect 2 H := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (H ⧸ N) = 1
  apply htwo.card_eq_or_dvd.resolve_right
  intro hd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hd.trans N.card_quotient_dvd_card))

/-- The source rank and small displacement force the marked extraspecial
subgroup to be the entire two-residual. -/
theorem normal_extraspecial_eq_twoResidual
    {K : Type*} [Group K] [Finite K] (f : K →* G) (hf : Function.Surjective f)
    (hrank : primeRank 3 K ≤ 2)
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) V = 6)
    (t : G) (ht : orderOf t = 2) (hr : fixedCodim ρ (zpowers t) ≤ 2)
    (hZt : ⁅(center P).map P.subtype,zpowers t⁆ = ⊥) : P = pResidual 2 G := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Z := (center P).map P.subtype
  have hZ : Nat.card Z = 3 := by
    rw [show Nat.card Z = Nat.card (center P) from
      (Nat.card_congr ((center P).equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm]
    exact IsExtraspecial.center_order_p 3 P
  have hZP : Z ≤ P := map_subtype_le _
  have hZC : Z ≤ centralizer ({t} : Set G) := by
    intro z hz
    apply mem_centralizer_singleton_iff.mpr
    exact ((commutator_eq_bot_iff_le_centralizer.mp hZt) hz t (mem_zpowers t)).symm
  have hcentral := centralizer_le ρ P hρ hP hd
  have htP : t ∉ centralizer (P : Set G) := by
    intro h
    have hx := P.orderOf_dvd_natCard (hcentral h)
    rw [ht,hP] at hx
    norm_num at hx
  have hinv : ∀ r : P, QuotientGroup.mk' (frattini P) (MulAut.conjNormal t r) =
      (QuotientGroup.mk' (frattini P) r)⁻¹ := by
    apply (IsExtraspecial.exponent_and_frattini_inversion_of_card27 hP
      (MulAut.conjNormal t) ?_ ?_ ?_).2
    · intro x
      have he := congrArg (fun a : MulAut P => a x)
        (show (MulAut.conjNormal t : MulAut P) * MulAut.conjNormal t = 1 by
          rw [← map_mul,← pow_two,← ht,pow_orderOf_eq_one,map_one])
      exact he
    · intro he
      apply htP
      rw [← MulAut.conjNormal_ker_eq_centralizer P]
      exact he
    · intro z hz
      apply Subtype.ext
      change t * (z : G) * t⁻¹ = z
      have hc := mem_centralizer_singleton_iff.mp (hZC (mem_map_of_mem P.subtype hz))
      change (z : G) * t = t * (z : G) at hc
      rw [← hc,mul_inv_cancel_right]
  have hfix : fixedSpace ρ Z = ⊥ := by
    rw [← fixedSpace_comp_map]
    let σ := ρ.comp P.subtype
    let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
      (hρ.comp P.subtype_injective) hP hd
    by_contra hn
    have hh := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hn
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr (hρ.comp P.subtype_injective)] using hh)
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  let C := centralizer ({t} : Set G)
  have hz3 : IsPGroup 3 (Z.subgroupOf C) :=
    (IsPGroup.of_card (n := 1) (by simpa using hZ)).comap_subtype
  obtain ⟨S,hZS⟩ := hz3.exists_le_sylow
  let R := (S : Subgroup C).map C.subtype
  have hR : IsPGroup 3 R := S.isPGroup'.map C.subtype
  have hRt : R ≤ C := map_subtype_le _
  let : IsCyclic R := cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (by decide : Odd 3) f hf hrank P (IsExtraspecial.isPGroup 3 P) t ht htP R hR hRt
  have hZR : Z ≤ R := by
    intro z hz
    exact mem_map_of_mem C.subtype (hZS (show (⟨z,hZC hz⟩ : C) ∈ Z.subgroupOf C from hz))
  have hRcard := cyclic_three_centralizer_card_le ρ hρ t ht hr Z R hZ hZR hfix hR hRt
  have hScard : Nat.card S ≤ 3 := by
    rwa [Nat.card_congr ((S : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toEquiv]
  obtain ⟨hq48,hqt⟩ := quotient_card_and_central_inverter P hcentral hP t hinv
  let q := (QuotientGroup.mk' P).comp C.subtype
  have hq : Function.Surjective q := centralizer_surjective P (by rw [hP]; decide) t ht hqt
  have hker : 3 ∣ Nat.card q.ker := by
    have hh : Z.subgroupOf C ≤ q.ker := by
      intro z hz
      exact (QuotientGroup.eq_one_iff (z : G)).mpr (hZP hz)
    have hzcard : Nat.card (Z.subgroupOf C) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv).trans hZ
    rw [← hzcard]
    exact card_dvd_of_le hh
  have hqnot : ¬ 3 ∣ Nat.card (G ⧸ P) := by
    intro hx
    have hnine : 3 ^ 2 ∣ Nat.card C := by
      have he := q.ker.card_eq_card_quotient_mul_card_subgroup
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv] at he
      rw [he]
      exact Nat.mul_dvd_mul hx hker
    have hnineS := S.pow_dvd_card_of_pow_dvd_card hnine
    have := Nat.le_of_dvd (Nat.card_pos (α := S)) hnineS
    norm_num at this
    omega
  have htwo : IsPGroup 2 (G ⧸ P) := by
    apply IsPGroup.of_card_dvd_pow (n := 4)
    have hc : Nat.Coprime (Nat.card (G ⧸ P)) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hqnot).symm
    exact hc.dvd_of_dvd_mul_right hq48
  exact (pResidual_eq_of_isPPerfect P (odd_isTwoPerfect (by rw [hP]; decide)) htwo).symm

end Representation.ExtraspecialBinarySix
