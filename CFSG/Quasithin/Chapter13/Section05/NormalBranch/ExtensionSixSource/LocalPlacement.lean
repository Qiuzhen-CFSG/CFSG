module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.Fusion
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixBlock
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.InvolutionFree
public import Theory.GroupTheory.QuaternionProductOrderFourCentralizer

/-!
# Involution placement in the original A₆ local group

An involution outside V has the same quotient conjugacy class as an
involution of the actual quaternion subgroup U_H. The natural A₆ module
has fixed space equal to displacement space for each involution. This
corrects the quotient conjugator by an element of V and places the
original involution in U_H with its conjugator still inside L.

Transitivity on the nonidentity elements of V handles the remaining
involutions. The original U_H fusion theorem then places every involution
of L, and hence of T ∩ L, in the ambient class of the chosen nonidentity
point z. These are the literal fusion inputs to the transfer argument.

Source: Aschbacher–Smith, Proposition 13.5.16, printed p.921.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.LocalPlacement
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
  (b : NormalBranch.Conclusions D M 6 g)

include d h e hseed hn hU b in
private theorem core_eq_module : D.L.pCoreIn 2 = D.V := by
  apply SourceCoreIntersection.local_core_eq_module d h e hseed hn hU
  rw [←b.seven.1]
  exact b.seven.2.symm

include d h e hseed hn hU b in
private theorem actor_eq_one_iff (x : D.L) :
    SourceSixBlock.actor d x = 1 ↔ (x : G) ∈ D.V := by
  rw [←MonoidHom.mem_ker, SourceSixBlock.actor_ker d e]
  rw [←core_eq_module d h e hseed hn hU b]
  exact (mem_map_iff_mem D.L.subtype_injective).symm

include d in
private theorem fixed_is_displacement (a : D.L)
    (ha : orderOf (SourceSixBlock.actor d a) = 2) (c : D.V)
    (hc : (a : G) * (c : G) * (a : G)⁻¹ = c) :
    ∃ w : D.V, (a : G) * (w : G) * (a : G)⁻¹ * w = c := by
  let α : MulAut D.V := D.V.normalizerMonoidHom
    ⟨a.val, d.normalizes_V (mem_sup_left a.property)⟩
  have hα (v : D.V) :
      (d.coordinate (α v)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (SourceSixBlock.actor d a).val
          (d.coordinate v).toAdd := d.conjugation a v
  have hfix : BinaryPermutation.naturalRepresentation (Fin 6)
      (SourceSixBlock.actor d a).val (d.coordinate c).toAdd = (d.coordinate c).toAdd := by
    rw [←hα]
    exact congrArg (fun v : D.V => (d.coordinate v).toAdd) (Subtype.ext hc)
  obtain ⟨w, hw⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.InvolutionFree.fixed_is_displacement
    (SourceSixBlock.actor d a) ha (d.coordinate c).toAdd hfix
  let wV : D.V := d.coordinate.symm (Multiplicative.ofAdd w)
  have he : α wV * wV = c := by
    apply d.coordinate.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, hα]
    simpa only [wV, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hw
  exact ⟨wV, congrArg Subtype.val he⟩

include d h e hseed hn hU b in
private theorem fiber_conjugate (a x : D.L) (ha : (a : G)^2=1) (hx : (x : G)^2=1)
    (haV : (a : G) ∉ D.V) (he : SourceSixBlock.actor d x = SourceSixBlock.actor d a) :
    ∃ w : D.V, (w : G) * (a : G) * (w : G)⁻¹ = x := by
  have hq : orderOf (SourceSixBlock.actor d a) = 2 := orderOf_eq_prime
    (by rw [←map_pow]; simpa only [map_one] using congrArg (SourceSixBlock.actor d) (show a^2=1 from Subtype.ext ha))
    (fun hh => haV ((actor_eq_one_iff d h e hseed hn hU b a).mp hh))
  have hcV : (x : G) * (a : G)⁻¹ ∈ D.V :=
    (actor_eq_one_iff d h e hseed hn hU b (x*a⁻¹)).mp (by simp only [map_mul,map_inv,he,mul_inv_cancel])
  let c : D.V := ⟨(x : G)*(a : G)⁻¹,hcV⟩
  have hci : (c : G)⁻¹ = c := by
    let := h.elementary
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (G:=G) (A:=D.V) (c : G) c.property
  have hai : (a : G)⁻¹ = a := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using ha)
  have hxi : (x : G)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hx)
  have hca : (c : G) * a = (a : G) * c := by
    calc
      (c : G) * a = x := by simp only [c,inv_mul_cancel_right]
      _ = (x : G)⁻¹ := hxi.symm
      _ = ((c : G) * a)⁻¹ := by simp only [c,inv_mul_cancel_right]
      _ = (a : G) * c := by rw [mul_inv_rev,hci,hai]
  obtain ⟨w,hw⟩ := fixed_is_displacement d a hq c (by rw [←hca,mul_inv_cancel_right])
  have hwcomm : (w : G) * ((a : G)*w*(a : G)⁻¹) = ((a : G)*w*(a : G)⁻¹) * w := by
    let := h.elementary
    exact congrArg Subtype.val (mul_comm w
      (D.V.normalizerMonoidHom ⟨a.val,d.normalizes_V (mem_sup_left a.property)⟩ w))
  have hwi : (w : G)⁻¹ = w := by
    let := h.elementary
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (G:=G) (A:=D.V) (w : G) w.property
  refine ⟨w, ?_⟩
  have hh := congrArg (fun y : G => y*(a : G)) (hwcomm.trans hw)
  change (w : G)*((a : G)*w*(a : G)⁻¹)*(a : G) = ((x : G)*(a : G)⁻¹)*(a : G) at hh
  simpa only [hwi,mul_assoc,inv_mul_cancel,mul_one] using hh

include d h e hseed hn hU b in
/-- Every involution outside the original module is conjugate into the original quaternion core. -/
theorem outside_module_conjugate (t : G) (ht : t ∈ D.L)
    (hto : orderOf t = 2) (htV : t ∉ D.V) :
    ∃ l ∈ D.L, l * t * l⁻¹ ∈ D.UH := by
  have hproper : ¬ D.UH ≤ D.V := by
    intro hle
    let := h.elementary
    exact hU (IsElementaryAbelian.of_le (p:=2) hle).toIsMulCommutative
  obtain ⟨u,huU,huV,hu2⟩ := exists_involution_outside_of_quaternion_core D.V D.UH
    (SourceOrthogonal.quaternion d h e hseed hn hU) hproper
  let uL : D.L := ⟨u,b.one.2.1 huU⟩
  let tL : D.L := ⟨t,ht⟩
  let f := SourceSixBlock.actor d
  have huq : orderOf (f uL) = 2 := orderOf_eq_prime
    (by rw [←map_pow]; simpa only [map_one] using congrArg f (show uL^2=1 from Subtype.ext hu2))
    (fun hh => huV ((actor_eq_one_iff d h e hseed hn hU b uL).mp hh))
  have ht2 : t^2=1 := hto ▸ pow_orderOf_eq_one t
  have htq : orderOf (f tL) = 2 := orderOf_eq_prime
    (by rw [←map_pow]; simpa only [map_one] using congrArg f (show tL^2=1 from Subtype.ext ht2))
    (fun hh => htV ((actor_eq_one_iff d h e hseed hn hU b tL).mp hh))
  obtain ⟨a,ha⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj (f uL) (f tL) huq htq)
  obtain ⟨k,rfl⟩ := SourceSixBlock.actor_surjective d a
  change f k * f uL * (f k)⁻¹ = f tL at ha
  let x : D.L := k⁻¹ * tL * k
  have hx2 : (x : G)^2=1 := by
    change ((k : G)⁻¹*t*k)^2=1
    calc
      _ = (k : G)⁻¹*t^2*k := by simp only [pow_two]; group
      _ = 1 := by rw [ht2]; group
  have he : f x = f uL := by
    change f (k⁻¹*tL*k)=f uL
    rw [map_mul,map_mul,map_inv,←ha]
    group
  obtain ⟨w,hw⟩ := fiber_conjugate d h e hseed hn hU b uL x hu2 hx2 huV he
  have hVL : D.V ≤ D.L := (core_eq_module d h e hseed hn hU b).symm.le.trans (pCoreIn_le 2 D.L)
  refine ⟨(w : G)⁻¹*(k : G)⁻¹,D.L.mul_mem (D.L.inv_mem (hVL w.property)) (D.L.inv_mem k.property),?_⟩
  have hh : (w : G)⁻¹*((k : G)⁻¹*t*k)*w = u := by
    change (w : G)*u*(w : G)⁻¹=(k : G)⁻¹*t*k at hw
    rw [←hw]
    group
  convert hh.symm ▸ huU using 1
  group


include d h e hseed hn hU b in
/-- The placement assertion in 13.5.16 retains a conjugating element of L. -/
theorem involutions_placed (t : G) (ht : t ∈ D.L) (hto : orderOf t = 2) :
    ∃ l ∈ D.L, l*t*l⁻¹ ∈ D.UH := by
  by_cases htV : t ∈ D.V
  · obtain ⟨v,hv,hvZ⟩ := SetLike.exists_of_lt h.point_lt
    have hv1 : v ≠ 1 := fun he => hvZ (he.symm ▸ D.V₁.one_mem)
    have ht1 : t ≠ 1 := by intro he; simp [he] at hto
    obtain ⟨l,hl,hconj⟩ := module_nonidentity_conjugate d t v htV (h.plus_le hv) ht1 hv1
    exact ⟨l,hl,hconj.symm ▸ le_conjugateSpanBy D.Vplus D.H hv⟩
  · exact outside_module_conjugate d h e hseed hn hU b t ht hto htV

include d h e hseed hn hU b in
/-- The actual local-group consumer: every involution of L lies in the class of z. -/
theorem local_involutions_fused (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (t : G) (ht : t ∈ D.L) (hto : orderOf t = 2) : IsConj z t := by
  obtain ⟨l,_,hl⟩ := involutions_placed d h e hseed hn hU b t ht hto
  have hto' : orderOf (l*t*l⁻¹) = 2 := ((MulAut.conj l).orderOf_eq t).trans hto
  exact (core_involutions_fused d h e hseed hn hU b z hz hz1 _ hl hto').trans
    (isConj_iff.mpr ⟨l,rfl⟩).symm

include d h e hseed hn hU b in
/-- The Sylow-intersection input used by the original transfer argument. -/
theorem local_sylow_involutions_fused (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (t : G) (ht : t ∈ (D.T : Subgroup G) ⊓ D.L) (hto : orderOf t = 2) : IsConj z t :=
  local_involutions_fused d h e hseed hn hU b z hz hz1 t ht.2 hto

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.LocalPlacement
