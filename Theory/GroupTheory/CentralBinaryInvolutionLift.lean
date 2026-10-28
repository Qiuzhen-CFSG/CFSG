module

public import Theory.GroupTheory.PResidual.CentralSylowFrattini
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion

/-!
# Central binary kernels detected by involution lifts

For a finite two-perfect group with central elementary binary kernel, if every
involution downstairs lifts to an involution and its Sylow images have exponent
two, then the kernel is trivial. Every Sylow element upstairs has square one;
central Sylow transfer puts the kernel in its now trivial Frattini subgroup.

For an A₅ quotient one noncentral involution suffices, since all its involutions
are conjugate. This avoids a classification of central covers in the original
J.4.4(3) group argument of Aschbacher–Smith, printed p.441.
-/

public section
noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CentralBinaryInvolutionLift
variable {E B : Type*} [Group E] [Finite E] [Group B] [Finite B]

omit [Finite B] in
theorem kernel_eq_bot (f : E →* B) (hp : IsPPerfect 2 E)
    (hk : f.ker ≤ center E) [IsElementaryAbelian 2 f.ker]
    (hs : ∀P:Sylow 2 E, ∀x:P, (f x)^2=1)
    (hlift : ∀b:B, b^2=1 → ∃a:E, a^2=1 ∧ f a=b) : f.ker=⊥ := by
  let P : Sylow 2 E := Classical.choice inferInstance
  have hx2 (x:P) : x^2=1 := by
    obtain ⟨a,ha,hfa⟩ := hlift (f x) (hs P x)
    have hm : (x:E)*a⁻¹∈f.ker := by
      change f ((x:E)*a⁻¹)=1
      rw [map_mul,map_inv,hfa,mul_inv_cancel]
    have hm2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) _ hm
    have hc : Commute ((x:E)*a⁻¹) a :=
      (mem_center_iff.mp (hk hm) a).symm
    apply Subtype.ext
    change (x:E)^2=1
    calc
      _ = (((x:E)*a⁻¹)*a)^2 := by group
      _ = 1 := by rw [hc.mul_pow,hm2,ha,mul_one]
  let : IsElementaryAbelian 2 P := {
    toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hx2 z)) x y⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hx2 }
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  have hF : frattini P=⊥ := frattini_eq_bot_of_isElementaryAbelian (p:=2)
  have hKP : f.ker ≤ (P:Subgroup E) :=
    (IsElementaryAbelian.isPGroup 2 f.ker).le_sylow_of_normal P
  have hC : f.ker.subgroupOf (P:Subgroup E) ≤ frattini P :=
    central_subgroup_le_frattini_sylow_of_isPPerfect hp P _ (by
      rintro _ ⟨x,hx,rfl⟩
      exact hk hx)
  apply eq_bot_iff.mpr
  intro x hx
  have hh := hC (show (⟨x,hKP hx⟩:P)∈f.ker.subgroupOf (P:Subgroup E) from hx)
  rw [hF] at hh
  exact congrArg Subtype.val hh

private theorem five_powers : ∀b:alternatingGroup (Fin 5),
    b^2=1 ∨ b^3=1 ∨ b^5=1 := by decide +kernel

theorem alternating_five_kernel_eq_bot
    (f : E →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 E) (hk : f.ker ≤ center E) [IsElementaryAbelian 2 f.ker]
    (v:E) (hv:v^2=1) (hfv:f v≠1) : f.ker=⊥ := by
  apply kernel_eq_bot f hp hk
  · intro P x
    let S := P.mapSurjective hf
    let y:S := ⟨f x,mem_map_of_mem f x.property⟩
    rcases five_powers (f x) with h | h | h
    · exact h
    · have hy : y^3=1 := Subtype.ext h
      have he : y=1 := (S.isPGroup'.powEquiv' (by decide : ¬2∣3)).injective (by simpa using hy)
      have hf1 : f x=1 := congrArg Subtype.val he
      rw [hf1,one_pow]
    · have hy : y^5=1 := Subtype.ext h
      have he : y=1 := (S.isPGroup'.powEquiv' (by decide : ¬2∣5)).injective (by simpa using hy)
      have hf1 : f x=1 := congrArg Subtype.val he
      rw [hf1,one_pow]
  · intro b hb
    by_cases h1 : b=1
    · exact ⟨1,one_pow _,by simpa using h1.symm⟩
    have ho : orderOf b=2 := orderOf_eq_prime hb h1
    have hvo : orderOf (f v)=2 := orderOf_eq_prime (by rw [←map_pow,hv,map_one]) hfv
    obtain ⟨a,ha⟩ := isConj_iff.mp (alternatingGroup.five_involutions_isConj (f v) b hvo ho)
    obtain ⟨g,rfl⟩ := hf a
    refine ⟨g*v*g⁻¹,?_,?_⟩
    · rw [conj_pow,hv,mul_one,mul_inv_cancel]
    · simpa only [map_mul,map_inv] using ha

/-- In a two-perfect A₅ extension, an involution lift and elementary central
coinvariant kernel force the full kernel to be commutator-generated. -/
theorem alternating_five_commutator_kernel
    (f : E →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 E)
    (hsq : ∀ x:E, x∈f.ker → x^2∈⁅f.ker,(⊤:Subgroup E)⁆)
    (v:E) (hv:v^2=1) (hfv:f v≠1) : ⁅f.ker,(⊤:Subgroup E)⁆=f.ker := by
  let N := ⁅f.ker,(⊤:Subgroup E)⁆
  have hN : N≤f.ker := commutator_le_left _ _
  let q := QuotientGroup.mk' N
  let fbar : E⧸N →* alternatingGroup (Fin 5) := QuotientGroup.lift N f hN
  have hfb : Function.Surjective fbar := by
    intro b
    obtain ⟨x,rfl⟩ := hf b
    exact ⟨q x,rfl⟩
  have hk : fbar.ker=f.ker.map q := QuotientGroup.ker_lift N f hN
  have hc : fbar.ker≤center (E⧸N) := by
    rw [hk]
    rintro _ ⟨r,hr,rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [←commutatorElement_eq_one_iff_mul_comm,←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅a,r⁆∈⁅f.ker,(⊤:Subgroup E)⁆
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_top a) hr
  have hpow (x:fbar.ker) : x^2=1 := by
    have hx := hk.le x.property
    obtain ⟨r,hr,he⟩ := hx
    apply Subtype.ext
    change (x:E⧸N)^2=1
    rw [←he,←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq r hr)
  let : IsElementaryAbelian 2 fbar.ker := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (hc y.property) x)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hz := alternating_five_kernel_eq_bot fbar hfb
    (hp.of_surjective q (QuotientGroup.mk'_surjective N)) hc (q v)
    (by rw [←map_pow,hv,map_one]) hfv
  apply le_antisymm hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  have hh : q x∈fbar.ker := hx
  rwa [hz] at hh


end CentralBinaryInvolutionLift
