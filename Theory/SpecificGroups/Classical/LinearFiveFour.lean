module
public import Theory.LinearAlgebra.MatrixTwoCentralizer
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Module
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.WreathedThirtyTwo
public import ABG.ChapterII.Section1.WreathedNoncyclicInvolution
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupAction.OddFourGroupLine
public import Theory.ElementaryAbelian.Basic
/-!
# A cubic cannot preserve a four-group through an SL₃(5) involution

An odd automorphism of a four-group fixing an involution is trivial. The
involution centralizer in SL₃(5) is the actual GL₂(5). In its natural degree
two action, a nonscalar involution has a two-dimensional matrix centralizer;
a cubic in that centralizer must be the identity. Only 25 scalar pairs over
F₅ are checked. Thus a cubic fixing an involution cannot normalize a four
through it. The canonical SL₃-to-PSL₃ map handles the projective source row.

The wreathed Sylow calculation places the central involution in every four.
Source: Aschbacher--Smith 5.1.13, printed p.636, refs/quasithin.pdf.
-/
public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.LinearFiveFour
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 5)
private theorem independent (x : M) (hx : ¬ ∃ c : ZMod 5, x = c • 1)
    (u v : ZMod 5) (he : u • (1 : M) + v • x = 0) : u = 0 ∧ v = 0 := by
  have hv : v = 0 := by
    by_contra hn
    apply hx
    have hs : v • x = (-u) • (1 : M) := by
      rw [neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using he)
    refine ⟨v⁻¹ * (-u), ?_⟩
    calc x = v⁻¹ • (v • x) := (inv_smul_smul₀ hn x).symm
         _ = (v⁻¹ * (-u)) • (1 : M) := by rw [hs,smul_smul]
  refine ⟨?_,hv⟩
  simp only [hv,zero_smul,add_zero] at he
  exact (smul_eq_zero.mp he).resolve_right one_ne_zero

private theorem scalar_check : ∀ c d : ZMod 5,
    c^3 + 3*c*d^2 = 1 → 3*c^2*d+d^3 = 0 → c=1 ∧ d=0 := by
  decide +kernel

private theorem matrix_check (a x : M) (ha : a^3 = 1) (ha1 : a ≠ 1)
    (hx : x^2=1) (hax : a*x=x*a) : x=1 ∨ x=-1 := by
  by_cases hscalar : ∃ c : ZMod 5, x=c • 1
  · obtain ⟨c,rfl⟩ := hscalar
    have hc : c^2=1 := by
      have hh := congrArg (fun y : M => y 0 0) hx
      simpa [pow_two,smul_mul_assoc,mul_smul_comm,smul_smul] using hh
    rcases (sq_eq_one_iff).mp hc with hh | hh
    · simp [hh]
    · simp [hh]
  obtain ⟨c,d,rfl⟩ := exists_eq_smul_one_add_smul_of_commute_two x a hscalar hax.symm
  have hx' : x*x=1 := by simpa only [pow_two] using hx
  have hsq : (c • (1 : M) + d • x)^2 = (c^2+d^2) • (1 : M) + (2*c*d) • x := by
    simp only [pow_two,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      one_mul,mul_one,hx']
    module
  have hcub : (c • (1 : M) + d • x)^3 =
      (c^3+3*c*d^2) • (1 : M) + (3*c^2*d+d^3) • x := by
    rw [pow_succ,hsq]
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      one_mul,mul_one,hx']
    module
  rw [hcub] at ha
  have he : (c^3+3*c*d^2-1) • (1 : M) + (3*c^2*d+d^3) • x = 0 := by
    calc
      _ = ((c^3+3*c*d^2) • (1 : M) + (3*c^2*d+d^3) • x) - 1 := by module
      _ = 0 := sub_eq_zero.mpr ha
  obtain ⟨he1,he2⟩ := independent x hscalar _ _ he
  obtain ⟨hc,hd⟩ := scalar_check c d (sub_eq_zero.mp he1) he2
  exact (ha1 (by simp [hc,hd])).elim

private theorem cubic_centralizer_no_four
    {G : Type*} [Group G] [Finite G]
    (f : G →* GL (Fin 2) (ZMod 5)) (hf : Function.Injective f)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (b : G) (hb : orderOf b = 3) (hc : b ∈ centralizer (E : Set G)) : False := by
  classical
  have hb3 : (f b).val ^ 3 = 1 := by
    have hp : b ^ 3 = 1 := by simpa only [hb] using pow_orderOf_eq_one b
    simpa only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val (congrArg f hp)
  have hb1 : (f b).val ≠ 1 := by
    intro he
    have hb1 : b = 1 := hf ((Units.ext he).trans (map_one f).symm)
    simp [hb1] at hb
  let K := E.map f
  have hK : (K : Set (GL (Fin 2) (ZMod 5))) ⊆ {1,-1} := by
    rintro x ⟨y,hy,rfl⟩
    have hy2 : y^2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hy
    have hfx2 : (f y).val ^ 2 = 1 := by
      simpa only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val (congrArg f hy2)
    have hxy : (f b).val * (f y).val = (f y).val * (f b).val := by
      exact congrArg Units.val ((map_mul f b y).symm.trans
        ((congrArg f (hc y hy).symm).trans (map_mul f y b)))
    rcases matrix_check (f b).val (f y).val hb3 hb1 hfx2 hxy with hh | hh
    · exact Or.inl (Units.ext hh)
    · exact Or.inr (Units.ext hh)
  have hp : ({(1 : GL (Fin 2) (ZMod 5)), -1} : Set (GL (Fin 2) (ZMod 5))).ncard ≤ 2 := by
    simpa only [Set.ncard_singleton] using Set.ncard_insert_le (1 : GL (Fin 2) (ZMod 5)) {-1}
  have hh := (Set.ncard_mono hK).trans hp
  rw [←Nat.card_coe_set_eq] at hh
  change Nat.card (E.map f) ≤ 2 at hh
  rw [card_map_of_injective hf,hE] at hh
  omega

private theorem odd_normalizer_centralizes_four
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (hE : Nat.card E = 4)
    (z : G) (hz : z ∈ E) (hz1 : z ≠ 1)
    (b : G) (hb : Odd (orderOf b)) (hbn : b ∈ normalizer (E : Set G))
    (hbz : b*z=z*b) : b ∈ centralizer (E : Set G) := by
  let a := E.normalizerMonoidHom ⟨b,hbn⟩
  have haodd : Odd (orderOf a) := hb.of_dvd_nat (by
    simpa only [←Subgroup.orderOf_coe] using orderOf_map_dvd E.normalizerMonoidHom ⟨b,hbn⟩)
  have ha : a = 1 := by
    by_contra hne
    apply Theory.GroupAction.odd_aut_card_four_fixed_point_free hE a haodd hne
      (⟨z,hz⟩ : E) (fun he => hz1 (congrArg Subtype.val he))
    apply Subtype.ext
    change b*z*b⁻¹=z
    exact mul_inv_eq_iff_eq_mul.mpr hbz
  intro x hx
  have hh := congrArg (fun u : MulAut E => ((u ⟨x,hx⟩ : E) : G)) ha
  change b*x*b⁻¹=x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- In a marked SL₃(5), no cubic centralizing an involution normalizes
an elementary four-group containing that involution. -/
theorem cubic_not_normalizes_four
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (e : G ≃* SL(3,F)) (hF : Nat.card F = 5)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (z : G) (hz : z ∈ E) (hz2 : orderOf z = 2)
    (b : G) (hb3 : orderOf b = 3) (hbz : b*z=z*b) :
    b ∉ normalizer (E : Set G) := by
  intro hbn
  have hbE := odd_normalizer_centralizes_four E hE z hz
    (fun he => by simp [he] at hz2) b (by rw [hb3]; decide) hbn hbz
  let Z := centralizer ({z} : Set G)
  have hEZ : E ≤ Z := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : E) ⟨z,hz⟩))
  let E' := E.subgroupOf Z
  have hE' : Nat.card E' = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEZ).toEquiv,hE]
  let : IsElementaryAbelian 2 E' :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hEZ).toMonoidHom
      (subgroupOfEquivOfLe hEZ).injective
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  have h2 : (2 : F) ≠ 0 := by
    intro he
    have hh := congrArg ef he
    exact (by decide : (2 : ZMod 5) ≠ 0) (by simpa only [map_ofNat,map_zero] using hh)
  let ec := (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e z).trans
    (SL3.involutionCentralizerEquiv F (e z) ((e.orderOf_eq z).trans hz2) h2)
  let eg : GL (Fin 2) F ≃* GL (Fin 2) (ZMod 5) := Units.mapEquiv ef.mapMatrix.toMulEquiv
  let b' : Z := ⟨b,mem_centralizer_singleton_iff.mpr hbz⟩
  apply cubic_centralizer_no_four (ec.trans eg).toMonoidHom (ec.trans eg).injective E' hE' b'
    ((orderOf_coe b').symm.trans hb3)
  intro x hx
  exact Subtype.ext (hbE x hx)
end Theory.SpecificGroups.Classical.LinearFiveFour

namespace Theory.SpecificGroups.Classical.LinearFiveFour
/-- The calculation applies inside a marked ambient component, without
quotienting out any of its centralizer in the ambient group. -/
theorem cubic_subgroup_not_normalizes_four
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (K E B : Subgroup G) (eK : K ≃* SL(3,F)) (hF : Nat.card F = 5)
    (hEK : E ≤ K) (hBK : B ≤ K)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) (hB : Nat.card B = 3)
    (z : G) (hz : z ∈ E) (hz2 : orderOf z = 2)
    (hBz : B ≤ centralizer ({z} : Set G)) : ¬ B ≤ normalizer (E : Set G) := by
  intro hn
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hB])
  let E' := E.subgroupOf K
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hEK).toMonoidHom (subgroupOfEquivOfLe hEK).injective
  let z' : K := ⟨z,hEK hz⟩
  let b' : K := ⟨b,hBK b.property⟩
  apply cubic_not_normalizes_four eK hF E'
    ((Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv).trans hE)
    z' hz ((orderOf_coe z').symm.trans hz2) b'
    ((orderOf_coe b').symm.trans ((orderOf_coe b).trans hb))
    (Subtype.ext (mem_centralizer_singleton_iff.mp (hBz b.property)))
  rw [←subgroupOf_normalizer_eq hEK]
  exact hn b.property
end Theory.SpecificGroups.Classical.LinearFiveFour

namespace Theory.SpecificGroups.Classical.LinearFiveFour
/-- Every elementary four in the wreathed Sylow contains its central
involution; normality of the four is unnecessary. -/
theorem central_involution_mem_four_of_wreathed
    {S : Type*} [Group S] [Finite S]
    (e : S ≃* Theory.GroupTheory.WreathedThirtyTwo)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (z : S) (hz : orderOf z = 2) (hc : z ∈ center S) : z ∈ E := by
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation
    (ABG.wreathed_equiv e.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
  let : IsCyclic (center S) := P.center_cyclic
  have he : (⟨z,hc⟩ : center S) = ⟨P.x,P.x_mem_center⟩ :=
    IsCyclic.eq_of_orderOf_eq_two ((orderOf_coe _).symm.trans hz)
      ((orderOf_coe _).symm.trans P.x_orderOf)
  have hzP : z = P.x := congrArg Subtype.val he
  rw [hzP]
  exact P.noncyclic_contains_x E
    (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (by simpa using hE))
end Theory.SpecificGroups.Classical.LinearFiveFour
