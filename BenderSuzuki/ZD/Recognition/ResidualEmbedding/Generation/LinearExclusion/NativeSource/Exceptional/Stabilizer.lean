module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.QuotientAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional.Nonsquare

/-!
# The zero stabilizer in the exceptional action

If m fixes the base coset uA, its displacement lies in A. Every element
of A is a square in R₀; a square root corrects m to an element centralizing
u and having the same action on A. That centralizer normalizes the original
local group L, whose root coordinates give the required semilinearity.
Every element of the original torus fixes the base coset, since it commutes
with the centralizer involution u.

Source: GLS IV, Chapter 2, Lemma 15.7, application of Chapter 1, Theorem 3.2.
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

omit [Finite G] in
include hJ in
public theorem u_inverts_kernel (b : s.kernel) :
    s.u * (b:M) * s.u⁻¹ = (b:M)⁻¹ := by
  have hbR := s.kernel_le_closure b.property
  have hxR := (linearCentralizerClosure M z t).mul_mem hbR s.u_mem_closure
  have hxnot : (b:M)*s.u ∉ s.kernel := fun hx =>
    s.u_not_mem ((s.kernel.mul_mem_cancel_left b.property).mp hx)
  have hc := (s.fusion ((b:M)*s.u) hxR hxnot).pow 2
  have hu2 : (s.u:G)^2 = 1 := congrArg Subtype.val (u_square s hJ)
  rw [hu2] at hc
  have hx2 : ((b:M)*s.u)^2 = 1 := Subtype.ext (isConj_one_left.mp hc)
  have huinv : s.u⁻¹ = s.u := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using u_square s hJ)
  apply eq_inv_iff_mul_eq_one.mpr
  rw [huinv]
  have hh := congrArg (fun x : M => (b:M)⁻¹ * x * b) hx2
  simpa only [pow_two, mul_assoc, inv_mul_cancel_left, one_mul, inv_mul_cancel] using hh

include d hJ in
/-- Correcting an element of the zero stabilizer preserves its action on A
and yields an actual normalizer of L. -/
public theorem stabilizer_correction (m : M)
    (hm : translation s hR hRV m = 1) :
    ∃ c : M, (c:G) ∈ normalizer (residualGenerated M z t : Set G) ∧
      ∀ a : A, m * (a:M) * m⁻¹ = c * (a:M) * c⁻¹ := by
  let w : s.kernel := ⟨m * s.u * m⁻¹ * s.u⁻¹, displacement_mem s hR hRV m⟩
  have hw2 : w ^ 2 = 1 := by
    apply Subtype.ext
    change (m * s.u * m⁻¹ * s.u⁻¹)^2 = 1
    exact congrArg Subtype.val hm
  have hwA : (w:M) ∈ A := (s.omega w).mp hw2
  obtain ⟨b, hb⟩ := exists_square s ⟨w,hwA⟩
  let c : M := (b:M)⁻¹*m
  have hbu : (b:M) * s.u * (b:M)⁻¹ = (b:M)^2 * s.u := by
    have hbi : s.u * (b:M)⁻¹ = (b:M) * s.u := by
      have hi := u_inverts_kernel s hJ b⁻¹
      simpa only [Subgroup.coe_inv, inv_inv] using mul_inv_eq_iff_eq_mul.mp hi
    calc
      (b:M)*s.u*(b:M)⁻¹ = (b:M)*(s.u*(b:M)⁻¹) := mul_assoc _ _ _
      _ = (b:M)^2*s.u := by rw [hbi,pow_two,mul_assoc]
  have hcu : c*s.u*c⁻¹=s.u := by
    have hmu : m*s.u*m⁻¹=(b:M)*s.u*(b:M)⁻¹ := by
      rw [hbu,hb]
      dsimp [w]
      group
    dsimp [c]
    calc
      (b:M)⁻¹*m*s.u*((b:M)⁻¹*m)⁻¹ = (b:M)⁻¹*(m*s.u*m⁻¹)*b := by group
      _ = s.u := by rw [hmu]; group
  have hci : (c:G) ∈ centralizer ({(s.u:G)} : Set G) :=
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hcu))
  have huD : (s.u:G) ∈ residualPairStabilizer M t :=
    centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M s.u_mem
  have hu : PFAppendixIII.IsInvolution (s.u:G) :=
    ⟨s.u_ne_one, congrArg Subtype.val (u_square s hJ)⟩
  have hcN := centralizer_le_normalizer_centralizerClosure d.minimal.disconnected (s.u:G) hci
  rw [d.centralizer_closure huD hu] at hcN
  refine ⟨c,hcN,?_⟩
  intro a
  have hbV : (b:M) ∈ pCore 2 M := hRV ▸ s.kernel_le_closure b.property
  have hc := mem_centralizer_iff.mp
    ((linear_twoCore_le_distinguished_centralizer d.minimal.disconnected d.reduction) hbV)
    (m*(a:M)*m⁻¹) ((distinguishedClosure_normal d.minimal.disconnected).conj_mem _ a.property m)
  dsimp [c]
  calc
    m*(a:M)*m⁻¹ = (b:M)⁻¹ * ((m*(a:M)*m⁻¹)*(b:M)) := by rw [hc]; group
    _ = ((b:M)⁻¹*m)*(a:M)*((b:M)⁻¹*m)⁻¹ := by group

/-- Every original torus element fixes the chosen zero coset. -/
public theorem torus_translation_eq_one
    (k : (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) :
    translation s hR hRV (k:M) = 1 := by
  have hc : (k:M) * s.u = s.u * (k:M) := Subtype.ext
    (mem_centralizer_iff.mp s.u_mem (k:M) k.property.2)
  apply Subtype.ext
  change ((k:M) * s.u * (k:M)⁻¹ * s.u⁻¹)^2 = 1
  rw [hc]
  simp

end BenderSuzuki.ZD.LinearExclusion.Exceptional
