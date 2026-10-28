module
public import Theory.Representation.RankOne.QuadraticRecognition.ElementFixedSpaces
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiElementBounds
public import Theory.SpecificGroups.Suzuki.OmegaGeneration
public import Theory.Representation.RankOne.QuadraticRecognition.SylowPlacement

/-!
# Odd-element fixed spaces from Suzuki complementary omega fixed spaces

Generation by a Sylow omega subgroup and an outside involution identifies
individual involution fixed spaces with the corresponding omega fixed spaces.
An odd-order element belongs to an odd torus and is inverted by an involution.
The inverter and its conjugate have disjoint fixed spaces, forcing the
odd-order element to fix only zero.

For Sz(2), the normal subgroup of order five has cyclic quotient of order
four. All involutions have the same image in that quotient; its action on
the five-fixed vectors and complementarity force that fixed space to vanish.

This proves the full Suzuki clause of DGS85, *Groups and Graphs*,
(5.11), printed p.112. All subgroups belong to the actual matrix model.
CriticalSupporting applies the result to the original critical quotient.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
open BenderSuzuki BenderSuzuki.PFAppendixIII Theory.GroupTheory
namespace Representation.RankOne.QuadraticRecognition

private theorem fixed_uniform_of_complement {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A B : Subgroup G)
    (hc : IsCompl (fixedSpace ρ A) (fixedSpace ρ B))
    {t : G} (ht : t∈A) (hgen : B ⊔ zpowers t = ⊤) :
    fixedSpace ρ (zpowers t) = fixedSpace ρ A := by
  apply le_antisymm ?_ (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  intro v hv
  have hvtop : v ∈ fixedSpace ρ A ⊔ fixedSpace ρ B := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hvtop
  have hbt : b∈fixedSpace ρ (zpowers t) := by
    simpa only [add_sub_cancel_left] using (fixedSpace ρ (zpowers t)).sub_mem hv
      (fixedSpace_antitone ρ (zpowers_le.mpr ht) ha)
  have hbtop : b∈fixedSpace ρ ⊤ := by
    rw [←hgen,show fixedSpace ρ (B ⊔ zpowers t)=fixedSpace ρ B ⊓ fixedSpace ρ (zpowers t)
      from ρ.invariants_comp_sup _ _]
    exact ⟨hb,hbt⟩
  have hb0 : b=0 := hc.disjoint.le_bot ⟨fixedSpace_antitone ρ le_top hbtop,hb⟩
  simpa only [hb0,add_zero] using ha

private theorem odd_fixed_eq_bot_of_inverter_pair {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (t y : G) (ht : t*t=1)
    (hi : t*y*t⁻¹=y⁻¹)
    (hd : Disjoint (fixedSpace ρ (zpowers t)) (fixedSpace ρ (zpowers (y*t*y⁻¹)))) :
    fixedSpace ρ (zpowers y)=⊥ := by
  have hyti : y*t=t*y⁻¹ := by
    have h := congrArg (fun g : G => t⁻¹*g*t) hi
    have h' : y=t⁻¹*y⁻¹*t := by simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using h
    have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht
    rw [hti] at h'
    calc
      y*t = (t*y⁻¹*t)*t := by rw [←h']
      _ = t*y⁻¹ := by rw [mul_assoc _ t t,ht,mul_one]
  have common (v : V) (hvy : ρ y v=v) (hvt : ρ t v=v) : v=0 := by
    have hvyi : ρ y⁻¹ v=v := by
      have h := congrArg (ρ y⁻¹) hvy
      simpa only [ρ.inv_self_apply] using h.symm
    exact hd.le_bot ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr hvt,
      (mem_fixedSpace_zpowers_iff _ _ _).mpr (by
        simp only [map_mul,Module.End.mul_apply,hvyi,hvt,hvy])⟩
  apply bot_unique
  intro v hv
  have hvy := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
  have hvyi : ρ y⁻¹ v=v := by
    have h := congrArg (ρ y⁻¹) hvy
    simpa only [ρ.inv_self_apply] using h.symm
  have hty : ρ y (ρ t v)=ρ t v := by
    rw [←Module.End.mul_apply,←map_mul,hyti,map_mul,Module.End.mul_apply,hvyi]
  have hdt : ρ t (ρ t v-v)=ρ t v-v := involution_fixes_displacement ρ ht v
  have hdy : ρ y (ρ t v-v)=ρ t v-v := by rw [map_sub,hty,hvy]
  have hz := common _ hdy hdt
  exact common v hvy (sub_eq_zero.mp hz)

private theorem suzuki_sylow_disjoint {m : ℕ} (hm : 0<m)
    (S T : Sylow 2 (SuzukiMatrixGroup m)) (hST : S≠T) :
    Disjoint (S : Subgroup (SuzukiMatrixGroup m)) (T : Subgroup (SuzukiMatrixGroup m)) := by
  obtain ⟨R,hR⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) R S
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) R T
  have hS : (S : Subgroup (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom := by
    rw [←hg,←hR]; rfl
  have hT : (T : Subgroup (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m).map (MulAut.conj h).toMonoidHom := by
    rw [←hh,←hR]; rfl
  rw [hS,hT]
  exact suzukiRootSubgroup_conjugates_disjoint m hm g h (fun he =>
    hST (Sylow.ext (hS.trans (he.trans hT.symm))))

private theorem suzuki_omega_involution_generates {m : ℕ} (hm : 0<m)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (t : SuzukiMatrixGroup m)
    (ht : t^2=1) (htS : t∉S) :
    omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m)) ⊔ zpowers t=⊤ := by
  obtain ⟨e,hS,hB⟩ := suzukiSylow_aligned_equiv hm (MulEquiv.refl _) S
  have htin : e.symm t ∉ SuzukiBorelSubgroup m := by
    intro hh
    have hp : BenderSuzuki.PFAppendixIII.IsInvolution (⟨e.symm t,hh⟩ : SuzukiBorelSubgroup m) := by
      constructor
      · intro he
        apply htS
        change t ∈ (S : Subgroup (SuzukiMatrixGroup m))
        have he1 : t=1 := e.symm.injective (by simpa using congrArg Subtype.val he)
        simpa only [he1] using (S : Subgroup (SuzukiMatrixGroup m)).one_mem
      · apply Subtype.ext
        change (e.symm t)^2=1
        rw [←map_pow,ht,map_one]
    have hx : e.symm t ∈ (involutionCore (SuzukiBorelSubgroup m)).map (SuzukiBorelSubgroup m).subtype :=
      ⟨⟨e.symm t,hh⟩,by rw [involutionCore_eq_closure]; exact subset_closure hp,rfl⟩
    rw [suzukiBorel_involutionCore_image m hm] at hx
    apply htS
    change t ∈ (S : Subgroup (SuzukiMatrixGroup m))
    rw [←hS]
    exact ⟨e.symm t,omegaOneAmbient_le _ hx,e.apply_symm_apply t⟩
  have hg := congrArg (fun H : Subgroup (SuzukiMatrixGroup m) => H.map e.toMonoidHom)
    (suzukiRootSubgroup_omega_sup_zpowers_eq_top m hm (e.symm t) htin)
  simpa only [Subgroup.map_sup,map_omegaOneAmbient_injective e.toMonoidHom e.injective,hS,
    MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,e.apply_symm_apply,Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hg

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem suzuki_uniform_of_complement {m : ℕ} (hm : 0<m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (S T : Sylow 2 (SuzukiMatrixGroup m)) (hST : S≠T)
    (hc : IsCompl (fixedSpace ρ (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))))
      (fixedSpace ρ (omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m)))))
    (P : Sylow 2 (SuzukiMatrixGroup m)) (t : SuzukiMatrixGroup m)
    (ht : t∈omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup m))) (ht1 : t≠1) :
    fixedSpace ρ (zpowers t)=fixedSpace ρ (omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup m))) := by
  have hstart (r : SuzukiMatrixGroup m) (hr : r∈omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))) (hr1 : r≠1) :
      fixedSpace ρ (zpowers r)=fixedSpace ρ (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))) := by
    have hrT : r∉T := fun h => hr1 (disjoint_def.mp (suzuki_sylow_disjoint hm S T hST)
      (omegaOneAmbient_le _ hr) h)
    let : IsElementaryAbelian 2 (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))) :=
      suzukiSylow_omega_elementary hm (MulEquiv.refl _) S
    exact fixed_uniform_of_complement ρ _ _ hc hr
      (suzuki_omega_involution_generates hm T r (elemPow_eq_one_of_isElementaryAbelian r hr) hrT)
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S P
  have hmap : omegaOneAmbient ((g • S : Sylow 2 (SuzukiMatrixGroup m)) : Subgroup (SuzukiMatrixGroup m)) =
      (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))).map (MulAut.conj g).toMonoidHom :=
    (map_omegaOneAmbient_injective _ (MulAut.conj g).injective _).symm
  rw [hmap] at ht ⊢
  obtain ⟨r,hr,rfl⟩ := ht
  have hr1 : r≠1 := fun he => ht1 (by simp only [he,map_one])
  rw [←MonoidHom.map_zpowers,SL2SylowFixedRecognition.fixedSpace_conjugate,
    SL2SylowFixedRecognition.fixedSpace_conjugate,hstart r hr hr1]
/-- The nondegenerate Suzuki case of DGS (5.11), with the actual Sylow
omega subgroups and the source complementary fixed spaces. -/
theorem suzuki_odd_fixed_eq_bot_of_complement {m : ℕ} (hm : 0<m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (S T : Sylow 2 (SuzukiMatrixGroup m)) (hST : S≠T)
    (hc : IsCompl (fixedSpace ρ (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))))
      (fixedSpace ρ (omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m)))))
    (y : SuzukiMatrixGroup m) (ho : Odd (orderOf y)) (hy1 : y≠1) :
    fixedSpace ρ (zpowers y)=⊥ := by
  obtain ⟨U,hyU,hU⟩ := suzukiOddSubgroup_exists_torus hm (zpowers y)
    (by simpa only [Nat.card_zpowers] using ho)
  obtain ⟨t,ht,hi⟩ := suzuki_torus_inverting_involution hm U hU
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [←pow_two,←ht] using pow_orderOf_eq_one t)
  have ht2 : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
  have hyinv := hi y (hyU (mem_zpowers y))
  let P := (IsPGroup.of_card (p := 2) (n := 1) (G := zpowers t)
    (by simp only [Nat.card_zpowers,ht,pow_one])).exists_le_sylow.choose
  have htP : t∈P := (IsPGroup.of_card (p := 2) (n := 1) (G := zpowers t)
    (by simp only [Nat.card_zpowers,ht,pow_one])).exists_le_sylow.choose_spec (mem_zpowers t)
  have htO : t∈omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup m)) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl t htP ht2
  have ht1 : t≠1 := fun he => by simp only [he,orderOf_one] at ht; omega
  have hfix := suzuki_uniform_of_complement hm ρ S T hST hc P t htO ht1
  have hprod : t*(y*t*y⁻¹)=y⁻¹^2 := by
    calc
      t*(y*t*y⁻¹) = (t*y*t⁻¹)*y⁻¹ := by rw [hti]; group
      _ = y⁻¹^2 := by rw [hyinv,pow_two]
  have hnot : y*t*y⁻¹ ∉ P := by
    intro hu
    have hmem : t*(y*t*y⁻¹)∈P := P.toSubgroup.mul_mem htP hu
    have hd : orderOf (t*(y*t*y⁻¹)) ∣ orderOf y := by
      rw [hprod,←orderOf_inv y]
      exact orderOf_pow_dvd _
    have hcop := P.isPGroup'.orderOf_coprime ho.coprime_two_left ⟨_,hmem⟩
    rw [←Subgroup.orderOf_coe] at hcop
    change (orderOf (t*(y*t*y⁻¹))).Coprime (orderOf y) at hcop
    have he := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd)
    rw [hprod] at he
    have hy2 : orderOf y ∣ 2 := by
      have hd2 := orderOf_dvd_of_pow_eq_one he
      simpa only [orderOf_inv] using hd2
    exact hy1 (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes ho.coprime_two_right dvd_rfl hy2))
  have hu2 : (y*t*y⁻¹)^2=1 := by
    change (MulAut.conj y t)^2=1
    rw [←map_pow,ht2,map_one]
  have hgen := suzuki_omega_involution_generates hm P (y*t*y⁻¹) hu2 hnot
  have hglobal : fixedSpace ρ ⊤=⊥ := by
    apply bot_unique
    exact (le_inf (fixedSpace_antitone ρ le_top) (fixedSpace_antitone ρ le_top)).trans hc.disjoint.le_bot
  have hd : Disjoint (fixedSpace ρ (zpowers t)) (fixedSpace ρ (zpowers (y*t*y⁻¹))) := by
    apply disjoint_iff.mpr
    rw [hfix,←show fixedSpace ρ (omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup m)) ⊔ zpowers (y*t*y⁻¹)) =
      fixedSpace ρ (omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup m))) ⊓ fixedSpace ρ (zpowers (y*t*y⁻¹))
      from ρ.invariants_comp_sup _ _,hgen,hglobal]
  exact odd_fixed_eq_bot_of_inverter_pair ρ t y (by simpa only [pow_two] using ht2) hyinv hd

private theorem small_sylow_cyclic (S : Sylow 2 (SuzukiMatrixGroup 0)) : IsCyclic S := by
  let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
    rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
    rw [show (20 : ℕ) = 2^2 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization (by decide : Nat.Prime 5)])
  let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  exact (Sylow.equiv P S).isCyclic.mp inferInstance

private theorem small_sylow_card (S : Sylow 2 (SuzukiMatrixGroup 0)) : Nat.card S=4 := by
  rw [S.card_eq_multiplicity,suzukiZero_card]
  rw [show (20:ℕ)=2^2*5 from rfl,
    Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,Nat.prime_five.factorization]

private theorem small_odd_zpowers_normal (y : SuzukiMatrixGroup 0)
    (hy : Odd (orderOf y)) (hy1 : y≠1) :
    orderOf y=5 ∧ (zpowers y).Normal := by
  have hd := orderOf_dvd_natCard y
  rw [suzukiZero_card] at hd
  have ho1 : orderOf y≠1 := fun he => hy1 (orderOf_eq_one_iff.mp he)
  have ho : orderOf y=5 := by
    have h5 : orderOf y ∣ 5 := (hy.coprime_two_right.pow_right 2).dvd_of_dvd_mul_left hd
    exact (Nat.prime_five.eq_one_or_self_of_dvd _ h5).resolve_left ho1
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers y) (by
    rw [Nat.card_zpowers,ho,suzukiZero_card]
    rw [show (20:ℕ)=2^2*5 from rfl,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_five.factorization])
  have hindex : (P : Subgroup (SuzukiMatrixGroup 0)).index=4 := by
    have h := (P : Subgroup (SuzukiMatrixGroup 0)).card_mul_index
    change Nat.card (zpowers y) * _ = _ at h
    rw [Nat.card_zpowers,ho,suzukiZero_card] at h
    omega
  have hcount : Nat.card (Sylow 5 (SuzukiMatrixGroup 0))=1 := by
    have hd := P.card_dvd_index
    rw [hindex] at hd
    have hb := Nat.le_of_dvd (by decide : 0<4) hd
    have hm := card_sylow_modEq_one 5 (SuzukiMatrixGroup 0)
    change Nat.card (Sylow 5 (SuzukiMatrixGroup 0))%5=1%5 at hm
    omega
  let : Subsingleton (Sylow 5 (SuzukiMatrixGroup 0)) := (Nat.card_eq_one_iff_unique.mp hcount).1
  exact ⟨ho,P.normal_of_subsingleton⟩


/-- The small source parameter Sz(2) also satisfies the odd-element
fixed-space conclusion of (5.11). -/
theorem suzukiZero_odd_fixed_eq_bot_of_complement
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 0) V)
    (S T : Sylow 2 (SuzukiMatrixGroup 0))
    (hc : IsCompl (fixedSpace ρ (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup 0))))
      (fixedSpace ρ (omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup 0)))))
    (y : SuzukiMatrixGroup 0) (hy : Odd (orderOf y)) (hy1 : y≠1) :
    fixedSpace ρ (zpowers y)=⊥ := by
  obtain ⟨ho,hn⟩ := small_odd_zpowers_normal y hy hy1
  let N := zpowers y
  let : N.Normal := hn
  let q := QuotientGroup.mk' N
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk',Nat.card_zpowers,ho]
    decide
  have hi := injective_comp_subtype_of_coprime_ker q hker (S : Subgroup _) S.isPGroup'
  have hcard : Nat.card (SuzukiMatrixGroup 0 ⧸ N)=4 := by
    have h := N.card_mul_index
    rw [show Nat.card N=5 from (Nat.card_zpowers y).trans ho,suzukiZero_card] at h
    change N.index=4
    omega
  have hbij := hi.bijective_of_nat_card_le (by rw [hcard,small_sylow_card S])
  let : IsCyclic S := small_sylow_cyclic S
  let : IsCyclic (SuzukiMatrixGroup 0 ⧸ N) := isCyclic_of_surjective (q.comp (S : Subgroup _).subtype) hbij.2
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [small_sylow_card S]; decide)
  have ht2 : (t : SuzukiMatrixGroup 0)^2=1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    exact congrArg Subtype.val h
  have hqt : orderOf (q (t : SuzukiMatrixGroup 0))=2 := by
    have he := orderOf_injective (q.comp (S : Subgroup (SuzukiMatrixGroup 0)).subtype) hi t
    change orderOf (q (t : SuzukiMatrixGroup 0))=orderOf t at he
    exact he.trans ht
  have hstable (v : V) (hv : v∈fixedSpace ρ N) : ρ t v∈fixedSpace ρ N := by
    intro a
    have hx : (t : SuzukiMatrixGroup 0)⁻¹*a*t∈N := by
      simpa only [inv_inv] using hn.conj_mem a a.property (t : SuzukiMatrixGroup 0)⁻¹
    have he : a.val*(t : SuzukiMatrixGroup 0) =
        (t : SuzukiMatrixGroup 0)*((t : SuzukiMatrixGroup 0)⁻¹*a*(t : SuzukiMatrixGroup 0)) := by group
    change ρ a (ρ t v)=ρ t v
    rw [←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply]
    congr 1
    exact hv ⟨_,hx⟩
  have hcommon (v : V) (hv : v∈fixedSpace ρ N) (htv : ρ t v=v) : v=0 := by
    have hevery (P : Sylow 2 (SuzukiMatrixGroup 0)) : v∈fixedSpace ρ (omegaOneAmbient (P : Subgroup _)) := by
      let K : Subgroup (SuzukiMatrixGroup 0) := {
        carrier := {a | ρ a v=v}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          change ρ a v=v at ha
          change ρ b v=v at hb
          change ρ (a*b) v=v
          rw [map_mul,Module.End.mul_apply,hb,ha]
        inv_mem' := by
          intro a ha
          change ρ a v=v at ha
          change ρ a⁻¹ v=v
          have h := congrArg (ρ a⁻¹) ha
          simpa only [ρ.inv_self_apply] using h.symm }
      have hfix : omegaOneAmbient (P : Subgroup _) ≤ K := by
        apply (omegaOneAmbient_le_iff _ _).mpr
        intro a ha ha2
        change ρ a v=v
        by_cases ha1 : a=1
        · simp [ha1]
        have hiP := injective_comp_subtype_of_coprime_ker q hker (P : Subgroup _) P.isPGroup'
        have hqa : orderOf (q a)=2 := by
          have he := orderOf_injective (q.comp (P : Subgroup (SuzukiMatrixGroup 0)).subtype) hiP ⟨a,ha⟩
          change orderOf (q a)=orderOf (⟨a,ha⟩ : P) at he
          exact he.trans (orderOf_eq_prime (Subtype.ext ha2) (fun he => ha1 (congrArg Subtype.val he)))
        have heq := IsCyclic.eq_of_orderOf_eq_two hqa hqt
        have hN : a*(t : SuzukiMatrixGroup 0)⁻¹ ∈ N := by
          apply (QuotientGroup.eq_one_iff _).mp
          change q (a*(t : SuzukiMatrixGroup 0)⁻¹)=1
          rw [map_mul,map_inv,heq,mul_inv_cancel]
        have hx : ρ (a*(t : SuzukiMatrixGroup 0)⁻¹) v=v := hv ⟨_,hN⟩
        have hti : ρ (t : SuzukiMatrixGroup 0)⁻¹ v=v := by
          have h := congrArg (ρ (t : SuzukiMatrixGroup 0)⁻¹) htv
          simpa only [ρ.inv_self_apply] using h.symm
        simpa only [map_mul,Module.End.mul_apply,hti] using hx
      intro a
      exact hfix a.property
    exact hc.disjoint.le_bot ⟨hevery S,hevery T⟩
  apply bot_unique
  intro v hv
  have hd : ρ t v-v∈fixedSpace ρ N := (fixedSpace ρ N).sub_mem (hstable v hv) hv
  have hd0 := hcommon (ρ t v-v) hd
    (involution_fixes_displacement ρ (by simpa only [pow_two] using ht2) v)
  exact hcommon v hv (sub_eq_zero.mp hd0)

/-- DGS (5.11) for every actual Suzuki parameter, including Sz(2). -/
theorem suzuki_all_odd_fixed_eq_bot_of_complement (m : ℕ)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (S T : Sylow 2 (SuzukiMatrixGroup m)) (hST : S≠T)
    (hc : IsCompl (fixedSpace ρ (omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m))))
      (fixedSpace ρ (omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m)))))
    (y : SuzukiMatrixGroup m) (ho : Odd (orderOf y)) (hy1 : y≠1) :
    fixedSpace ρ (zpowers y)=⊥ := by
  rcases Nat.eq_zero_or_pos m with rfl|hm
  · exact suzukiZero_odd_fixed_eq_bot_of_complement ρ S T hc y ho hy1
  · exact suzuki_odd_fixed_eq_bot_of_complement hm ρ S T hST hc y ho hy1

/-- The source Suzuki omega-center equals the Sylow omega subgroup at
all parameters, including the cyclic Sylow of Sz(2). -/
theorem suzuki_omega_center_eq (m : ℕ) (S : Sylow 2 (SuzukiMatrixGroup m)) :
    omegaOneAmbient ((center S).map (S : Subgroup (SuzukiMatrixGroup m)).subtype) =
      omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m)) := by
  apply le_antisymm
  · exact omegaOneAmbient_mono (by rintro _ ⟨x,_,rfl⟩; exact x.property)
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    have hxO := (omegaOneAmbient_le_iff _ _).mp le_rfl x hx hx2
    have hxC := binaryRankOne_omega_le_center (.suzuki m (MulEquiv.refl _)) S hxO
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hxC hx2

/-- DGS (5.11) with the literal source omega-center and its prescribed
conjugate outside the original Sylow normalizer. -/
theorem suzuki_source_odd_fixed_eq_bot (m : ℕ)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (g : SuzukiMatrixGroup m)
    (hg : g ∉ normalizer (S : Set (SuzukiMatrixGroup m)))
    (hc : IsCompl
      (fixedSpace ρ (omegaOneAmbient ((center S).map (S : Subgroup (SuzukiMatrixGroup m)).subtype)))
      (fixedSpace ρ ((omegaOneAmbient ((center S).map (S : Subgroup (SuzukiMatrixGroup m)).subtype)).map
        (MulAut.conj g).toMonoidHom)))
    (y : SuzukiMatrixGroup m) (ho : Odd (orderOf y)) (hy1 : y≠1) :
    fixedSpace ρ (zpowers y)=⊥ := by
  rw [suzuki_omega_center_eq] at hc
  rw [map_omegaOneAmbient_injective _ (MulAut.conj g).injective] at hc
  exact suzuki_all_odd_fixed_eq_bot_of_complement m ρ S (g • S)
    (fun h => hg (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)) hc y ho hy1

end Representation.RankOne.QuadraticRecognition
