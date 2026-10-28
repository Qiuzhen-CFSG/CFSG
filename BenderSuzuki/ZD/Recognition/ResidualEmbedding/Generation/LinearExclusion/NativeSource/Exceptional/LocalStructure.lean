module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.ElementaryRank
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional.MarkedQuotient.LocalData
public import Theory.GroupTheory.PGroup.HomocyclicFourRecognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.NormalizerGeometry
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# The original homocyclic kernel in the exceptional linear branch

The order formulas |J| = 2 and |⟨Jᴹ⟩| = 2q², with q = 2ⁿ, suffice to
construct the local structure at the start of GLS IV, Chapter 2, Lemma 15.7.
The already proved normalizer index supplies exactly q² M-conjugates of
J's nonidentity element. Localization gives C_{O₂(M)}(K) = J; coprime action
then gives the literal section [⟨Jᴹ⟩, K]/A and its transitive torus action.
The involution census makes the kernel abelian, with square-one subgroup A,
and makes every outside element an involution conjugate to the element of J.
The square map has kernel and image of order q, giving genuine C₄ⁿ coordinates.
The noninvolutions characterize the kernel and prove normality in M.

All subgroups remain the original subgroups of M. Neither the proper-core
supplement nor equality with O₂(M) is needed. The exceptional action assembly
can therefore apply the exported structure in either branch; its later
quotient calculations use the separate equality with O₂(M).

Source: refs/KGroup/GLS4/Chapter2.tex, lines 2738–2745; the normalizer index
and involution census are the earlier Lemma 15.6 conclusions used there.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
universe u

private theorem omega_of_transitive_section
    {H : Type*} [Group H] (B A K : Subgroup H)
    (hAB : A ≤ B) (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hnon : ∃ x ∈ B, x ^ 2 ≠ 1)
    (htrans : ∀ x ∈ B, x ∉ A → ∀ y ∈ B, y ∉ A →
      ∃ k ∈ K, ∃ a ∈ A, y = k * x * k⁻¹ * a) :
    ∀ x : B, x ^ 2 = 1 ↔ (x : H) ∈ A := by
  obtain ⟨b, hb, hb2⟩ := hnon
  have hbA : b ∉ A := fun he => hb2 (hAsq b he)
  intro x
  refine ⟨?_, fun hx => Subtype.ext (hAsq x hx)⟩
  intro hx
  by_contra hxA
  obtain ⟨k, _, a, ha, he⟩ := htrans b hb hbA x x.property hxA
  have hkB : k * b * k⁻¹ ∈ B := by
    have hh := B.mul_mem x.property (B.inv_mem (hAB ha))
    rw [he, mul_inv_cancel_right] at hh
    exact hh
  have hs : (k * b * k⁻¹) ^ 2 = 1 := by
    have hh := congrArg Subtype.val hx
    change (x : H) ^ 2 = 1 at hh
    rw [he, (hcomm _ hkB a (hAB ha)).mul_pow, hAsq a ha, mul_one] at hh
    exact hh
  apply hb2
  exact (MulAut.conj k).injective (by
    simpa only [map_pow, map_one, MulAut.conj_apply] using hs)

private theorem homocyclic_of_omega
    {H : Type*} [Group H] [Finite H] (B A : Subgroup H) {n : ℕ}
    (hAB : A ≤ B)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hsq : ∀ x ∈ B, x ^ 2 ∈ A)
    (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (homega : ∀ x : B, x ^ 2 = 1 ↔ (x : H) ∈ A)
    (hB : Nat.card B = (2 ^ n) ^ 2) (hA : Nat.card A = 2 ^ n) :
    Nonempty (B ≃* Multiplicative (Fin n → ZMod 4)) := by
  let : IsMulCommutative B := ⟨⟨fun x y =>
    Subtype.ext (hcomm x x.property y y.property).eq⟩⟩
  let sq : B →* A := {
    toFun := fun x => ⟨(x : H) ^ 2, hsq x x.property⟩
    map_one' := Subtype.ext (one_pow 2)
    map_mul' := fun x y => Subtype.ext ((hcomm x x.property y y.property).mul_pow 2) }
  have hker : sq.ker = A.subgroupOf B := by
    ext x
    change sq x = 1 ↔ (x : H) ∈ A
    rw [← homega]
    constructor
    · intro he
      exact Subtype.ext (congrArg (fun a : A => (a : H)) he)
    · intro he
      exact Subtype.ext (congrArg (fun b : B => (b : H)) he)
  have hkcard : Nat.card sq.ker = 2 ^ n := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv, hA]
  have hsur : Function.Surjective sq := sq.surjective_of_card_ker_le_div (by
    rw [hkcard, hB, hA, pow_two, Nat.mul_div_left _ (by positivity)])
  apply homocyclicFour_of_square_roots
  · intro x
    apply Subtype.ext
    change (x : H) ^ 4 = 1
    calc
      (x : H) ^ 4 = ((x : H) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := hAsq _ (hsq x x.property)
  · intro x hx
    obtain ⟨y, hy⟩ := hsur ⟨x, (homega x).mp hx⟩
    exact ⟨y, Subtype.ext (congrArg (fun a : A => (a : H)) hy)⟩
  · rw [hB, pow_right_comm]
    rfl

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

private theorem twoCore_torus_fixed
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2) :
    pCore 2 M ⊓ centralizer
      (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  have hcollapse : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      centralizerClosure Z v = residualGenerated M z t :=
    fun _ hvD hv => d.centralizer_closure hvD hv
  have hlocal := linear_involution_localization_of_centralizerClosure
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model d.distinguished_le hJ hcollapse
  obtain ⟨hKcard, hAfixed⟩ := linear_distinguishedClosure_torus_geometry
    d.minimal d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model d.distinguished_le
  have helement := linear_twoCore_element_centralizer_of_localization
    d.minimal.disconnected d.z_mem d.z_mem_M hJ hR hlocal hAfixed
  have hq : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by norm_num) ▸
    Nat.pow_le_pow_right (by decide) d.parameter
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M)
    rw [hKcard]
    omega)
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hkM : (k : M) ≠ 1 := fun hh => hk (Subtype.ext hh)
  apply le_antisymm
  · intro v hv
    have hvc : v ∈ centralizer ({(k : M)} : Set M) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hv.2 k k.property).symm
    rw [← helement k k.property hkM]
    exact ⟨hv.1, hvc⟩
  · apply le_inf (linearCentralizer_subgroupOf_le_twoCore hR)
    intro j hj k hk
    exact Subtype.ext (mem_centralizer_iff.mp hj k hk.2)

private theorem square_count_of_orbit
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hAR : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCentralizerClosure M z t)
    {u : M} (huJ : u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hu : u ≠ 1)
    (horbit : (2 ^ n) ^ 2 ≤ Nat.card {x : linearCentralizerClosure M z t // IsConj u (x : M)}) :
    (2 ^ n) ^ 2 + 2 ^ n ≤ Nat.card {x : linearCentralizerClosure M z t // x ^ 2 = 1} := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  obtain ⟨hAsq, _, hAcard⟩ := linear_distinguishedClosure_internal_facts
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model d.distinguished_le
  have hu2 : u ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨u, huJ⟩ : centralizer (residualGenerated M z t : Set G)))
    rw [hJ] at hh
    exact Subtype.ext (congrArg (fun a : centralizer (residualGenerated M z t : Set G) => (a : G)) hh)
  have huA : u ∉ A := by
    intro huA
    have huZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected
      d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper (d.distinguished_le huA)).mp
      ⟨fun he => hu (Subtype.ext he), congrArg Subtype.val hu2⟩
    exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected d.t_not_mem_M
      (centralizer_residualGenerated_le_pairStabilizer d.minimal.disconnected d.z_mem d.z_mem_M huJ) huZ
  have hPA (x : R) (hx : IsConj u (x : M)) : (x : M) ∉ A := by
    intro hxA
    obtain ⟨m, hm⟩ := isConj_iff.mp hx
    have hh := (inferInstance : A.Normal).conj_mem (x : M) hxA m⁻¹
    apply huA
    rw [← hm] at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, inv_inv, mul_one] using hh
  let f : {x : R // IsConj u (x : M)} ⊕ A → {x : R // x ^ 2 = 1} :=
    Sum.elim (fun x => ⟨x.val, by
      obtain ⟨m, hm⟩ := isConj_iff.mp x.property
      apply Subtype.ext
      change (x.val : M) ^ 2 = 1
      rw [← hm, ← MulAut.conj_apply, ← map_pow, hu2, map_one]⟩)
      (fun a => ⟨⟨a, hAR a.property⟩, Subtype.ext (hAsq a a.property)⟩)
  have hf : Function.Injective f := by
    intro x y he
    have he' := congrArg (fun a : {x : R // x ^ 2 = 1} => (a.val : M)) he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext (Subtype.ext he'))
      | inr y => exact (hPA x.val x.property (he'.symm ▸ y.property)).elim
    | inr x =>
      cases y with
      | inl y => exact (hPA y.val y.property (he' ▸ x.property)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext he')
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, hAcard] at hc
  exact (Nat.add_le_add_right horbit _).trans hc

private theorem local_structure_of_census
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hcensus : ∃ u : M,
      u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M ∧ u ≠ 1 ∧
      (2 ^ n) ^ 2 ≤ Nat.card {x : linearCentralizerClosure M z t // IsConj u (x : M)}) :
    Nonempty (ExceptionalLocalStructure Z M z t n) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let B := linearCommutatorKernel M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let : R.Normal := normalClosure_normal
  have hcollapse : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      centralizerClosure Z v = residualGenerated M z t :=
    fun _ hvD hv => d.centralizer_closure hvD hv
  have hfixed := twoCore_torus_fixed d hJ hR
  obtain ⟨hAB, hBcard, hsq, htrans⟩ :=
    linear_involutionBase_torus_section_of_centralizerClosure
      d.minimal d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
      d.proper d.parameter d.model hJ hR d.distinguished_le hfixed hcollapse
  have hBR : B ≤ R := linearCommutatorKernel_le_closure
  have hAR := hAB.trans hBR
  obtain ⟨u, huJ, hu, horbit⟩ := hcensus
  have hcount := square_count_of_orbit d hJ hAR huJ hu horbit
  have hbound := linear_elementary_crossing_card_le_of_orbit_card_and_section
    d.minimal d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
    d.parameter d.model d.distinguished_le hJ hR hcollapse hAB hsq ⟨u, huJ, hu, horbit⟩
  obtain ⟨hAsq, hAc, hAcard⟩ := linear_distinguishedClosure_internal_facts
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model d.distinguished_le
  have hcentral : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    intro a ha b hb
    exact (mem_centralizer_iff.mp (hAc ha) b (linearCommutatorKernel_le_twoCore hR hb)).symm
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) d.parameter)
  obtain ⟨hcomm, hnon, hout⟩ := abelian_noninvolution_profile_of_transitive_section
    R B A K hq hBR hAB hR hBcard hAcard hAsq hcentral htrans hcount hbound
  have hnormal : B.Normal := normal_of_noninvolution_profile R B hBR hcomm hnon hout
  have homega := omega_of_transitive_section B A K hAB hAsq hcomm hnon htrans
  obtain ⟨e⟩ := homocyclic_of_omega B A hAB hcomm (fun x hx => hsq x (hBR hx))
    hAsq homega hBcard hAcard
  have huB : u ∉ B := by
    intro huB
    have hu2 : u ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨u, huJ⟩ : centralizer (residualGenerated M z t : Set G)))
      rw [hJ] at hh
      exact Subtype.ext (congrArg (fun a : centralizer (residualGenerated M z t : Set G) => (a : G)) hh)
    have huA : u ∈ A := (homega ⟨u, huB⟩).mp (Subtype.ext hu2)
    have huZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected
      d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper (d.distinguished_le huA)).mp
      ⟨fun he => hu (Subtype.ext he), congrArg Subtype.val hu2⟩
    exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected d.t_not_mem_M
      (centralizer_residualGenerated_le_pairStabilizer d.minimal.disconnected d.z_mem d.z_mem_M huJ) huZ
  have hfusion := linearCentralizerClosure_involution_fusion_of_orbit_card
    d.minimal d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
    d.parameter d.model d.distinguished_le hJ hR hcollapse hAR hsq u huJ hu horbit
  exact ⟨{ kernel := B
           kernel_normal := hnormal
           kernel_eq := rfl
           homocyclic := e
           distinguished_le := hAB
           omega := homega
           u := u
           u_mem := huJ
           u_ne_one := fun he => hu (Subtype.ext he)
           u_not_mem := huB
           fusion := fun v hv hvB => M.subtype.map_isConj
             (hfusion v hv (hout v hv hvB) (fun hvA => hvB (hAB hvA))).symm }⟩

omit [Group G] [Finite G] d in
private theorem centralizer_singleton_eq_normalizer_of_card_two
    {H : Type*} [Group H] (W : Subgroup H) (hW : Nat.card W = 2)
    {u : H} (hu : u ∈ W) (hu1 : u ≠ 1) :
    centralizer ({u} : Set H) = normalizer (W : Set H) := by
  obtain ⟨v, _, hv⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hW
  have hchoices (w : H) (hw : w ∈ W) : w = 1 ∨ w = u := by
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val
        ((hv ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))).trans
          (hv ⟨u, hu⟩ (fun he => hu1 (congrArg Subtype.val he))).symm))
  apply le_antisymm
  · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro g hg w hw
    rcases hchoices w hw with rfl | rfl
    · simp
    · exact (mem_centralizer_singleton_iff.mp hg).symm
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (normalizer_le_centralizer_of_card_two W hW hg) u hu).symm

/-- The nonidentity element of J has q² M-conjugates. The original normalizer
index supplies this count even when the centralizer closure is all of O₂(M). -/
public theorem Context.centralizer_involution_class_card
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    {u : M} (huJ : u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hu : u ≠ 1) : Nat.card (ConjClasses.mk u).carrier = (2 ^ n) ^ 2 := by
  have hJM : centralizer (residualGenerated M z t : Set G) ≤ M :=
    (centralizer_residualGenerated_le_pairStabilizer d.minimal.disconnected
      d.z_mem d.z_mem_M).trans inf_le_left
  have hJcard := linearCentralizer_subgroupOf_card d.minimal.disconnected d.z_mem d.z_mem_M hJ
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer,
    centralizer_singleton_eq_normalizer_of_card_two _ hJcard huJ hu,
    ← subgroupOf_normalizer_eq hJM]
  change (normalizer (centralizer (residualGenerated M z t : Set G) : Set G)).relIndex M = _
  rw [d.centralizer_normalizer_eq, ← inf_relIndex_left]
  exact d.point_normalizer_index

/-- The actual order-two centralizer supplies the literal orbit in its
normal closure. No supplement or involution-fusion conclusion is assumed. -/
public theorem Context.centralizer_involution_census
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2) :
    ∃ u : M,
      u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M ∧ u ≠ 1 ∧
      (2 ^ n) ^ 2 ≤ Nat.card {x : linearCentralizerClosure M z t // IsConj u (x : M)} := by
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let R := linearCentralizerClosure M z t
  let : R.Normal := normalClosure_normal
  have hJcard : Nat.card J = 2 :=
    linearCentralizer_subgroupOf_card d.minimal.disconnected d.z_mem d.z_mem_M hJ
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJcard
  have huM : (u : M) ≠ 1 := fun he => hu (Subtype.ext he)
  have hc := d.centralizer_involution_class_card hJ u.property huM
  have hclass (x : M) (hx : x ∈ (ConjClasses.mk (u : M)).carrier) :
      x ∈ R ∧ IsConj (u : M) x := by
    have hconj : IsConj (u : M) x :=
      (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hx)).symm
    refine ⟨?_, hconj⟩
    obtain ⟨m, rfl⟩ := isConj_iff.mp hconj
    exact (inferInstance : R.Normal).conj_mem u (subset_normalClosure u.property) m
  let f : (ConjClasses.mk (u : M)).carrier → {x : R // IsConj (u : M) (x : M)} :=
    fun x => ⟨⟨x, (hclass x x.property).1⟩, (hclass x x.property).2⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg
      (fun a : {x : R // IsConj (u : M) (x : M)} => (a.val : M)) he)
  exact ⟨u, u.property, huM, hc ▸ Nat.card_le_card_of_injective f hf⟩

/-- The first paragraph of GLS IV, 15.7, on the original selected PSL₂
configuration. The two earlier order formulas suffice for all of its local
structure conclusions, including literal kernel normality and full fusion. -/
public theorem Context.exceptionalLocalStructure
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2) :
    Nonempty (ExceptionalLocalStructure Z M z t n) :=
  local_structure_of_census d hJ hR (d.centralizer_involution_census hJ)

end BenderSuzuki.ZD.LinearExclusion
