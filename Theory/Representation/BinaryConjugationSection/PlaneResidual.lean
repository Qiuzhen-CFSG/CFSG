module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.GroupTheory.PResidual.CentralModuleFixed
public import Theory.GroupTheory.PResidual.Restriction

/-!
# Residuals of literal binary plane stabilizers

For a binary section U/Z with a central denominator, a normalizer of a
subgroup with two-element section image fixes that image pointwise.
Its two-residual therefore centralizes the subgroup: commutator
idempotence removes the central errors in Z. Thus the embedded
residuals of the relative normalizer and centralizer agree.

If the subgroup contains Z, fixation of its nonzero image vector also
detects its exact normalizer. These statements retain the specified
section map and need no splitting of U over Z.

Source application: the reciprocal plane and L_Y in Aschbacher–Smith,
proof of 14.7.32, printed p.1058, refs/quasithin.pdf.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W]
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A two-element image leaves only central errors, which the two-residual kills. -/
theorem residual_normalizer_eq_centralizer
    (s : BinaryConjugationSection H U Z ρ)
    (hU : IsPGroup 2 U) (hcent : H ≤ centralizer (Z : Set G))
    (A P : Subgroup G) (hAH : A ≤ H) (hPU : P ≤ U)
    (hc : Nat.card (s.imageSpace P) = 2) :
    (pResidual 2 (A ⊓ normalizer (P : Set G) : Subgroup G)).map
        (A ⊓ normalizer (P : Set G)).subtype =
      (pResidual 2 (A ⊓ centralizer (P : Set G) : Subgroup G)).map
        (A ⊓ centralizer (P : Set G)).subtype := by
  let N := A ⊓ normalizer (P : Set G)
  let R := (pResidual 2 N).map N.subtype
  have hRN : R ≤ N := map_subtype_le _
  have hRH : R ≤ H := hRN.trans (inf_le_left.trans hAH)
  have hfix (x : H) (hx : (x : G) ∈ normalizer (P : Set G))
      (v : W) (hv : v ∈ s.imageSpace P) : ρ x v = v := by
    have hmem := s.imageSpace_apply_mem P x hx v hv
    by_cases hz : v = 0
    · rw [hz,map_zero]
    have hne : ρ x v ≠ 0 := by
      intro hh
      have hi := congrArg (fun f : Module.End (ZMod 2) W => f v) (ρ.map_mul x⁻¹ x)
      rw [inv_mul_cancel,ρ.map_one] at hi
      change v = ρ x⁻¹ (ρ x v) at hi
      rw [hh,map_zero] at hi
      exact hz hi
    obtain ⟨_,_,hu⟩ := (Nat.card_eq_two_iff' (0 : s.imageSpace P)).mp hc
    exact congrArg Subtype.val ((hu ⟨ρ x v,hmem⟩ (fun hh => hne (congrArg Subtype.val hh))).trans
      (hu ⟨v,hv⟩ (fun hh => hz (congrArg Subtype.val hh))).symm)
  have hcomm : ⁅P,R⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx v hv
    let xH : H := ⟨x,hRH hx⟩
    let vU : U := ⟨v,hPU hv⟩
    let v' : U := ⟨x*v*x⁻¹,(mem_normalizer_iff.mp (s.normalized xH.property) v).mp vU.property⟩
    have he : s.coordinates v' = s.coordinates vU := by
      apply Multiplicative.toAdd.injective
      exact (s.equivariant xH vU).trans
        (hfix xH (hRN hx).2 _ ((s.mem_imageSpace_iff P _).mpr ⟨vU,hv,rfl⟩))
    have hh := (s.coordinates_eq_one_iff (v'*vU⁻¹)).mp (by
      rw [map_mul,map_inv,he,mul_inv_cancel])
    exact hh
  have hUZ : U ≤ normalizer (Z : Set G) := by
    let := s.kernel_normal
    exact (normal_subgroupOf_iff_le_normalizer s.kernel_le).mp inferInstance
  have hRC : R ≤ centralizer (P : Set G) := le_centralizer_iff.mp
    (centralizes_of_isPPerfect_central_displacement R U P Z
      (isPPerfect_embedded_pResidual 2 N) hU (hRH.trans s.normalized) hUZ
      (le_centralizer_iff.mp (hRH.trans hcent)) hPU hcomm)
  exact (embedded_pResidual_eq_of_le_of_residual_le 2
    (inf_le_inf_left A (Subgroup.centralizer_le_normalizer _))
    (le_inf (hRN.trans inf_le_left) hRC)).symm
omit [Finite G] in
/-- The nonzero point of a two-element image detects the exact normalizer
when the original subgroup contains the section kernel. -/
theorem mem_normalizer_iff_fixed_of_image_card_two
    (s : BinaryConjugationSection H U Z ρ)
    (P : Subgroup G) (hPU : P ≤ U) (hZP : Z ≤ P)
    (hc : Nat.card (s.imageSpace P) = 2)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0) (x : H) :
    (x : G) ∈ normalizer (P : Set G) ↔ ρ x w = w := by
  have hsmall (v : W) (hv : v ∈ s.imageSpace P) : v = 0 ∨ v = w := by
    by_cases hz : v = 0
    · exact Or.inl hz
    obtain ⟨_,_,hu⟩ := (Nat.card_eq_two_iff' (0 : s.imageSpace P)).mp hc
    exact Or.inr (congrArg Subtype.val
      ((hu ⟨v,hv⟩ (fun he => hz (congrArg Subtype.val he))).trans
        (hu ⟨w,hw⟩ (fun he => hw0 (congrArg Subtype.val he))).symm))
  have hinv (y : H) (v : W) : ρ y⁻¹ (ρ y v) = v := by
    have hh := congrArg (fun f : Module.End (ZMod 2) W => f v) (ρ.map_mul y⁻¹ y)
    rw [inv_mul_cancel,ρ.map_one] at hh
    exact hh.symm
  have hpres (y : H) (hy : ρ y w = w) (v : G) (hv : v ∈ P) :
      (y : G)*v*(y : G)⁻¹ ∈ P := by
    let u : U := ⟨v,hPU hv⟩
    have hu : (s.coordinates u).toAdd ∈ s.imageSpace P :=
      (s.mem_imageSpace_iff _ _).mpr ⟨u,hv,rfl⟩
    have hf : ρ y (s.coordinates u).toAdd = (s.coordinates u).toAdd := by
      rcases hsmall _ hu with he | he
      · rw [he,map_zero]
      · rw [he,hy]
    let u' : U := ⟨(y:G)*v*(y:G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized y.property) v).mp u.property⟩
    apply (s.coordinates_mem_imageSpace_iff_of_kernel_le P hZP u').mp
    change (s.coordinates ⟨(y:G)*u*(y:G)⁻¹,_⟩).toAdd ∈ _
    rw [s.equivariant,hf]
    exact hu
  constructor
  · intro hx
    rcases hsmall _ (s.imageSpace_apply_mem P x hx w hw) with he | he
    · have hh := hinv x w
      rw [he,map_zero] at hh
      exact (hw0 hh.symm).elim
    · exact he
  · intro hx
    have hi : ρ x⁻¹ w = w := by
      conv_lhs => rw [←hx]
      exact hinv x w
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · exact hpres x hx v
    · intro hv
      have hh := hpres x⁻¹ hi ((x:G)*v*(x:G)⁻¹) hv
      simpa only [Subgroup.coe_inv,inv_inv,inv_mul_cancel_left,mul_assoc,
        inv_mul_cancel,mul_one] using hh

end Representation.BinaryConjugationSection
