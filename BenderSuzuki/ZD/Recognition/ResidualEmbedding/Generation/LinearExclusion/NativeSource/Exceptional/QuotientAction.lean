module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.ActionAlgebra
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection.Elementary
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion

/-!
# Faithful action of the actual two-core quotient

The square-coordinate action kills V because V/A has exponent two and V
centralizes A. Conversely an element fixing every coordinate first fixes
the base point, so its translation is trivial; it therefore centralizes A
and belongs to V. The action consequently descends faithfully to M/V.
The source fusion of the involution coset, lifted inside M by Sylow fusion
control, proves transitivity on the original square-coordinate set A.

Source: GLS IV, Chapter 2, Lemma 15.7, exceptional equality branch.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.Exceptional
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (s : ExceptionalLocalStructure Z M z t n)
  (d : Context Z M z t n)
  (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
  (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
  (hRV : linearCentralizerClosure M z t = pCore 2 M)
local notation "A" => Subgroup.subgroupOf (closure (Z ∩ (M : Set G))) M
local notation "V" => pCore 2 M

include d hJ hR hRV in
private theorem squares_mem (v : M) (hv : v ∈ V) : v ^ 2 ∈ A :=
  linear_involutionBase_elementary_quotient_of_centralizerClosure d.minimal d.reduction
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.parameter d.model hJ hR
    d.distinguished_le (fun _ hu hi => d.centralizer_closure hu hi) v (hRV.symm ▸ hv)

include d hJ in
public theorem translation_eq_one_of_mem_core {v : M} (hv : v ∈ V) :
    translation s hR hRV v = 1 := by
  let : (A).Normal := distinguishedClosure_normal d.minimal.disconnected
  let q := QuotientGroup.mk' (A)
  have hsq (x : M) (hx : x ∈ V) : q x ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (squares_mem d hJ hR hRV x hx)
  have huV : s.u ∈ V := hRV ▸ s.u_mem_closure
  have hvq := hsq v hv
  have huq := hsq s.u huV
  have hvuq := hsq (v*s.u) ((V).mul_mem hv huV)
  have hcomm : Commute (q v) (q s.u) := by
    change q v * q s.u = q s.u * q v
    have hi1 : (q v)⁻¹ = q v := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hvq)
    have hi2 : (q s.u)⁻¹ = q s.u := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using huq)
    have hi : (q (v*s.u))⁻¹ = q (v*s.u) :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hvuq)
    simpa only [map_mul, mul_inv_rev, hi1, hi2] using hi.symm
  have hdelta : v * s.u * v⁻¹ * s.u⁻¹ ∈ A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (v*s.u*v⁻¹*s.u⁻¹)=1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm.eq]
    group
  apply Subtype.ext
  change (v * s.u * v⁻¹ * s.u⁻¹) ^ 2 = 1
  exact congrArg Subtype.val ((s.omega ⟨_, displacement_mem s hR hRV v⟩).mpr hdelta)

include hJ in
public theorem pointAction_fixed_iff (m : M) :
    let := pointAction s d hR hRV
    (∀ a : A, m • a = a) ↔ m ∈ V := by
  let := pointAction s d hR hRV
  constructor
  · intro hm
    have htr : translation s hR hRV m = 1 := by
      have hh := hm 1
      apply Subtype.ext
      have he := congrArg Subtype.val hh
      change m * 1 * m⁻¹ * (translation s hR hRV m : M) = 1 at he
      simpa using he
    rw [← d.distinguished_centralizer_eq_twoCore hJ]
    intro a ha
    have hh := congrArg Subtype.val (hm ⟨a, ha⟩)
    change m * a * m⁻¹ * (translation s hR hRV m : M) = a at hh
    rw [htr, OneMemClass.coe_one, mul_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hm a
    apply Subtype.ext
    change m * (a:M) * m⁻¹ * (translation s hR hRV m:M) = a
    rw [translation_eq_one_of_mem_core s d hJ hR hRV hm, OneMemClass.coe_one, mul_one]
    have hc := mem_centralizer_iff.mp
      ((linear_twoCore_le_distinguished_centralizer d.minimal.disconnected d.reduction) hm) a a.property
    rw [← hc]
    group

/-- The actual quotient permutation homomorphism; its source is M/O₂(M). -/
@[expose] public def quotientPermutation : (M ⧸ V) →* Equiv.Perm A := by
  let := pointAction s d hR hRV
  exact QuotientGroup.lift V (MulAction.toPermHom M A) (by
    intro m hm
    apply Equiv.ext
    intro a
    change m • a = a
    exact (pointAction_fixed_iff s d hJ hR hRV m).mpr hm a)

public theorem quotientPermutation_injective :
    Function.Injective (quotientPermutation s d hJ hR hRV) := by
  let := pointAction s d hR hRV
  have hker : V ≤ (MulAction.toPermHom M A).ker := by
    intro m hm
    apply Equiv.ext
    exact (pointAction_fixed_iff s d hJ hR hRV m).mpr hm
  apply (QuotientGroup.injective_lift_iff V _ hker).mpr
  ext m
  change m ∈ V ↔ MulAction.toPermHom M A m = 1
  rw [Equiv.Perm.ext_iff]
  exact (pointAction_fixed_iff s d hJ hR hRV m).symm

/-- The faithful descended action keeps the square-coordinate formula
on every image of an original element of M. -/
@[expose, instance_reducible] public def quotientAction : MulAction (M ⧸ V) A :=
  MulAction.compHom A (quotientPermutation s d hJ hR hRV)

public theorem quotientAction_faithful :
    let := quotientAction s d hJ hR hRV
    FaithfulSMul (M ⧸ V) A := by
  let := quotientAction s d hJ hR hRV
  constructor
  intro g k he
  apply quotientPermutation_injective s d hJ hR hRV
  exact Equiv.ext he

include hJ in
public theorem pointAction_exists_one_smul (a : A) :
    let := pointAction s d hR hRV
    ∃ m : M, m • (1:A) = a := by
  let := pointAction s d hR hRV
  obtain ⟨b, hb⟩ := exists_square s a
  have hbu : (b:M) * s.u ∈ linearCentralizerClosure M z t :=
    (linearCentralizerClosure M z t).mul_mem (s.kernel_le_closure b.property) s.u_mem_closure
  have hbun : (b:M) * s.u ∉ s.kernel := by
    intro he
    exact s.u_not_mem ((s.kernel.mul_mem_cancel_left b.property).mp he)
  have hconj := s.fusion ((b:M)*s.u) hbu hbun
  have hu : PFAppendixIII.IsInvolution (s.u : G) :=
    ⟨s.u_ne_one, congrArg Subtype.val (u_square s hJ)⟩
  have hv : PFAppendixIII.IsInvolution (((b:M)*s.u : M):G) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
    rw [← hg]
    exact BenderSuzuki.IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  obtain ⟨S, hSM, hf⟩ := d.reduction.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hu hv
    s.u.property (((b:M)*s.u).property) hconj.symm
  have hm' : m * s.u * m⁻¹ = (b:M) * s.u := Subtype.ext hm
  refine ⟨m, Subtype.ext ?_⟩
  change m * 1 * m⁻¹ * (m * s.u * m⁻¹ * s.u⁻¹)^2 = (a:M)
  rw [hm', mul_inv_cancel_right]
  simpa using hb

public theorem quotientAction_pretransitive :
    let := quotientAction s d hJ hR hRV
    MulAction.IsPretransitive (M ⧸ V) A := by
  let := quotientAction s d hJ hR hRV
  constructor
  intro a b
  obtain ⟨m, hm⟩ := pointAction_exists_one_smul s d hJ hR hRV a
  obtain ⟨k, hk⟩ := pointAction_exists_one_smul s d hJ hR hRV b
  refine ⟨QuotientGroup.mk' V (k*m⁻¹), ?_⟩
  let := pointAction s d hR hRV
  change (k*m⁻¹) • a = b
  rw [mul_smul, ← hm, inv_smul_smul, hk]

end BenderSuzuki.ZD.LinearExclusion.Exceptional
