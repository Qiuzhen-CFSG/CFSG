module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveCubicCore
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# An ambient lifting criterion for the original cubic core orbit

Let t be the original core involution and a conjugation by the chosen
cubic. Its norm v = t a(t) a²(t) belongs to the full span-action kernel.
We prove that v belongs to the natural-layer span only if v = 1:
a(v) = t v t⁻¹, core displacements lie in Z_S, and the cubic is fixed-free
on both the span and its quotient by Z_S.

If v = 1, the three involutions generate an actual elementary four-group,
and its order-four action image makes the action faithful. Otherwise v
is a specified element of the original action kernel outside the whole
span. The same-witness consumer retains the complete kernel, cubic orbit,
Sylow placement, and original even-seed alternative.

The four-group is inside O2(K); it does not give an even plane in the S5
quotient. Eliminating the remaining norm obstruction, S5 parabolic escape,
initial 6.1.4–5, exact omega escape and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural. The Chapter12 application retains
the independent mixed-size premise.
Source: Aschbacher–Smith 6.1.17(4), 6.1.19, printed pp.672–675
(`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem cubic_norm_mem
    {X : Type*} [Group X] [IsElementaryAbelian 2 X]
    (a : MulAut X) (ha : a^3=1) (hfree : ∀ x, a x=x → x=1)
    (Z : Subgroup X) (hZ : ∀ z ∈ Z, a z ∈ Z)
    (x : X) (hx : a x / x ∈ Z) : x ∈ Z := by
  let : CommGroup X := IsMulCommutative.instCommGroup
  have ha3 (y : X) : a (a (a y))=y := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      DFunLike.congr_fun ha y
  have hn : x*a x*a (a x)=1 := by
    apply hfree
    rw [map_mul,map_mul,ha3]
    ac_rfl
  have hi (y : X) : y⁻¹=y := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) y)
  have he : a (a x / x)=x := by
    rw [map_div,div_eq_mul_inv,hi]
    have hh : a (a x)=(x*a x)⁻¹ := eq_inv_of_mul_eq_one_right hn
    rw [hh,mul_inv_rev,hi,hi]
    calc
      _ = (a x*a x)*x := by ac_rfl
      _ = x := by rw [←pow_two]; simp only [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 X) (a x),one_mul]
  exact he ▸ hZ _ hx

private theorem cubic_orbit_lift
    {X Y : Type*} [Group X] [Finite X] [Group Y]
    (a : MulAut X) (t : X) (ht : orderOf t=2)
    (f : X →* Y)
    (hn : t*a t*a (a t)=1)
    (hcard : Nat.card (((zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t))).map f)=4) :
    let D := (zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t))
    IsElementaryAbelian 2 D ∧ Nat.card D=4 ∧ Function.Injective (f.subgroupMap D) := by
  have hpow (i : ℕ) : ((a^i) t)^2=1 := by
    have hh : orderOf ((a^i : MulAut X) t)=2 := ((a^i : MulAut X).orderOf_eq t).trans ht
    rw [←hh,pow_orderOf_eq_one]
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_zero,MulAut.one_apply,pow_two] using hpow 0)
  have hai : (a t)⁻¹=a t := inv_eq_of_mul_eq_one_right (by simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply,pow_two] using hpow 1)
  have haai : (a (a t))⁻¹=a (a t) := inv_eq_of_mul_eq_one_right (by simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply,pow_two] using hpow 2)
  have he : t*a t=a (a t) := (mul_eq_one_iff_eq_inv.mp hn).trans haai
  have hcomm : Commute t (a t) := by
    change t*a t=a t*t
    calc
      _ = (a (a t))⁻¹ := he.trans haai.symm
      _ = a t*t := by rw [←he,mul_inv_rev,hai,hti]
  let B := zpowers t ⊔ zpowers (a t)
  have hD : (zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t)) = B :=
    sup_eq_left.mpr (zpowers_le.mpr (he ▸ mul_mem_sup (mem_zpowers t) (mem_zpowers (a t))))
  rw [hD] at hcard ⊢
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa using hpow 0)
  let : IsElementaryAbelian 2 (zpowers (a t)) := IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa using hpow 1)
  have hc : zpowers (a t) ≤ centralizer (zpowers t : Set X) := by
    apply zpowers_le.mpr
    rintro x ⟨m,rfl⟩
    exact (hcomm.zpow_left m).eq
  have hbound : Nat.card B ≤ 4 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (zpowers t) (zpowers (a t))
      (hc.trans (Subgroup.centralizer_le_normalizer _))
    rw [Nat.card_zpowers,Nat.card_zpowers,a.orderOf_eq,ht] at hh
    have hp : 0 < Nat.card (zpowers t ⊓ zpowers (a t) : Subgroup X) := Nat.card_pos
    dsimp only [B]
    nlinarith
  have hb := (f.subgroupMap_surjective B).bijective_of_nat_card_le (hcard ▸ hbound)
  exact ⟨IsElementaryAbelian.sup_of_le_centralizer hc,
    (Nat.card_eq_of_bijective _ hb).trans hcard,hb.1⟩

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The cubic orbit norm can lie in the natural span only when it is
trivial. The full centralizer kernel is not identified with that span. -/
theorem natural_five_cubic_norm_mem_span_iff
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) (t : K) (ht : t ∈ pCore 2 K) (ht2 : orderOf t=2) :
    let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
    ((t*a t*a (a t) : K) : G) ∈ conjugateSpanBy (layer L R) K ↔
      t*a t*a (a t)=1 := by
  let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
  let S := conjugateSpanBy (layer L R) K
  let Z := ZS (T : Subgroup G) L R
  let v := t*a t*a (a t)
  have hSU : S ≤ Escape.U (T : Subgroup G) L R := by
    have he : conjugateSpanBy (layer L R) (Escape.I (T : Subgroup G) L R) =
        Escape.U (T : Subgroup G) L R := by
      rw [conjugateSpanBy_eq_iSup_conj]
      rfl
    rw [←he]
    exact conjugateSpanBy_mono le_rfl hKI
  let := h.layer_elementary
  let : IsMulCommutative S := le_centralizer_iff_isMulCommutative.mp
    (hSU.trans (hab.trans (centralizer_le hSU)))
  let : IsElementaryAbelian 2 S := conjugateSpanBy_elementary_of_commutative _ _
  have hcS : c ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hcL),
      mem_normalizer_iff_map_conj_eq.mp (hNK hcN)]
  let b := S.normalizerMonoidHom ⟨c,hcS⟩
  have hb3 : b^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hcS⟩ : normalizer (S : Set G))^3=1 :=
      Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
    rw [hh,map_one]
  have hfree (x : S) (hx : b x=x) : x=1 := by
    apply Subtype.ext
    apply mem_bot.mp
    rw [←natural_five_span_cubic_fixed_eq_bot h hnat K hKI hNK e hab hcL hcN hc3]
    refine ⟨x.property,?_⟩
    have hh : Commute c (x : G) :=
      mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hx)
    rintro y ⟨m,rfl⟩
    exact (hh.zpow_left m).eq
  have ha3 : a^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hNK hcN⟩ : normalizer (K : Set G))^3=1 :=
      Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
    rw [hh,map_one]
  have haaa : a (a (a t))=t := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      DFunLike.congr_fun ha3 t
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (show t^2=1 from ht2 ▸ pow_orderOf_eq_one t))
  have hvcyc : a v=t*v*t⁻¹ := by
    dsimp only [v]
    rw [map_mul,map_mul,haaa]
    symm
    calc
      _ = (t*t)*(a t*a (a t))*t⁻¹ := by group
      _ = a t*a (a t)*t := by
        rw [←pow_two,show t^2=1 from ht2 ▸ pow_orderOf_eq_one t,one_mul,hti]
  change (v : G) ∈ S ↔ v=1
  refine ⟨?_,fun hv => hv ▸ S.one_mem⟩
  intro hv
  let x : S := ⟨v,hv⟩
  have hQKI : K.pCoreIn 2 ≤ (Escape.I (T : Subgroup G) L R).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hKI ((Subgroup.centralizer_le_normalizer _).trans hNK)
  have hcomm : ⁅K.pCoreIn 2,S⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono hSU hQKI).trans (natural_escape_core h hnat).2
  have hxstep : b x / x ∈ Z.subgroupOf S := by
    have he : (b x : G)=(t : G)*(v : G)*(t : G)⁻¹ := congrArg Subtype.val hvcyc
    change (b x : G)/(x : G) ∈ Z
    rw [he]
    simpa only [x,div_eq_mul_inv,commutatorElement_def] using
      commutator_le.mp hcomm t (mem_map_of_mem K.subtype ht) v hv
  have hxZ : x ∈ Z.subgroupOf S := cubic_norm_mem b hb3 hfree (Z.subgroupOf S)
    (fun z hz => (mem_normalizer_iff.mp hcN z).mp hz) x hxstep
  have hbx : b x=x := by
    apply Subtype.ext
    change (a v : G)=(v : G)
    rw [hvcyc]
    exact mul_inv_eq_iff_eq_mul.mpr ((hKI t.property) v hxZ).symm
  exact Subtype.ext (congrArg (fun y : S => (y : G)) (hfree x hbx))


/-- The original cubic orbit either is an actual elementary four-group
acting faithfully, or its norm is a specified element of the full action
kernel outside the entire natural span. -/
@[expose] def NaturalFiveCubicLiftData (T : Sylow 2 G) (L R E K : Subgroup G) : Prop :=
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
  ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
    ∃ hcK : c ∈ normalizer (K : Set G),
      let a := K.normalizerMonoidHom ⟨c,hcK⟩
      let ρ := naturalFiveCoverAction L R K
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
      (∃ t : K, (t : G) ∈ E ∧ orderOf t=2 ∧
        q t ∈ alternatingGroup (Fin 5) ∧ q t ≠ 1) ∨
      (∃ t : K, t ∈ pCore 2 K ∧ orderOf t=2 ∧
        ⁅layer L R,zpowers (t : G)⁆ = ZS (T : Subgroup G) L R ∧
        let D := (zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t))
        let v := t*a t*a (a t)
        D ≤ pCore 2 K ∧ D.map a.toMonoidHom=D ∧
        IsElementaryAbelian 2 (D.map ρ) ∧ Nat.card (D.map ρ)=4 ∧
        D.map K.subtype ≤ (T : Subgroup G) ∧
        (∀ x : K, x ∈ D → (ρ x=1 ↔
          (x : G) ∈ centralizer (conjugateSpanBy (layer L R) K : Set G))) ∧
        ((IsElementaryAbelian 2 D ∧ Nat.card D=4 ∧
            Function.Injective (ρ.subgroupMap D) ∧ v=1) ∨
          (v ∈ ρ.ker ∧ (v : G) ∉ conjugateSpanBy (layer L R) K ∧
            a v=t*v*t⁻¹)))

/-- Apply the ambient norm criterion to the very involution and cubic
orbit supplied by the original even-seed alternative. The remaining
obstruction is outside the span, not merely nontrivial in its cover. -/
theorem natural_five_cubic_lift_data
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (E : Subgroup G) (hd : NaturalFiveCubicCoreData T L R E K)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    NaturalFiveCubicLiftData T L R E K := by
  intro e c hcL hcN hc3
  obtain ⟨hcK,hd⟩ := hd e c hcL hcN hc3
  refine ⟨hcK,?_⟩
  rcases hd with heven | ⟨t,ht,ht2,htcomm,hDQ,hDa,_,_,hDel,hDcard,hDT,hvker,hker⟩
  · exact Or.inl heven
  right
  refine ⟨t,ht,ht2,htcomm,hDQ,hDa,hDel,hDcard,hDT,hker,?_⟩
  let a := K.normalizerMonoidHom ⟨c,hcK⟩
  let v := t*a t*a (a t)
  change _ ∨ (v ∈ (naturalFiveCoverAction L R K).ker ∧
    (v : G) ∉ conjugateSpanBy (layer L R) K ∧ a v=t*v*t⁻¹)
  by_cases hv : v=1
  · have hh := cubic_orbit_lift a t ht2 (naturalFiveCoverAction L R K) hv hDcard
    exact Or.inl ⟨hh.1,hh.2.1,hh.2.2,hv⟩
  · right
    refine ⟨hvker,?_,?_⟩
    · exact fun hm => hv ((natural_five_cubic_norm_mem_span_iff h hnat K hKI hNK e hab
        hcL hcN hc3 t ht ht2).mp hm)
    · have ha : a^3=1 := by
        rw [←map_pow]
        have hh : (⟨c,hcK⟩ : normalizer (K : Set G))^3=1 :=
          Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
        rw [hh,map_one]
      have ha3 : a (a (a t))=t := by
        simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
          DFunLike.congr_fun ha t
      have hi : t⁻¹=t := inv_eq_of_mul_eq_one_right (by
        simpa only [pow_two] using (show t^2=1 from ht2 ▸ pow_orderOf_eq_one t))
      dsimp only [v]
      rw [map_mul,map_mul,ha3]
      symm
      calc
        _ = (t*t)*(a t*a (a t))*t⁻¹ := by group
        _ = a t*a (a t)*t := by
          rw [←pow_two,show t^2=1 from ht2 ▸ pow_orderOf_eq_one t,one_mul,hi]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
