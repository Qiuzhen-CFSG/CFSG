module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SectionTransport

/-!
# The actual central section in the L₄ critical pair

A surjective homomorphism with kernel V₁ identifies the source section with a
binary representation. Its equivariance is an identity for actual conjugation
in the ambient group. Faithfulness then identifies Dγ with Uγ ∩ O₂(H), and
centrality of V₁ proves V₁ ≤ D_H. These identities justify the relative-index
and dimension comparisons; no normality in the ambient group is used.

The image of A₁ means the image of A₁ ∩ U_H. It has dimension at most one even
when A₁ is outside U_H. The defining commutator bound for D_H gives the actual
line-valued displacement. If A₁ is outside U_H this image vanishes. The final
lemma uses the centralizer bound of 13.7.3(7) to fix I ∩ D_H under Vγ.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979),
using F.9.12–13 and 13.7.3(7). The marked-plane construction, application of
13.8.9, lower bound on I/(I ∩ D_H), and critical-pair reversal are separate
source obligations. The lemmas here do not assert those consequences.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Representation.BinaryOffender
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- A concrete model of U_H/V₁ with the actual H/O₂(H) conjugation action.
The kernel and equivariance fields concern the displayed homomorphism, not
only an abstract group-family identification. -/
structure ConjugationSection (H UH Z : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U) where
  le : UH ≤ H
  normalizes : H ≤ normalizer (UH : Set G)
  centralizes : H ≤ centralizer (Z : Set G)
  line_le : Z ≤ UH
  quotient : UH →* Multiplicative U
  surjective : Function.Surjective quotient
  kernel : quotient.ker = Z.subgroupOf UH
  conjugates : ∀ (a : H) (u : UH),
    ρ (QuotientGroup.mk' (pCore 2 H) a) (quotient u).toAdd =
      (quotient ⟨(a : G) * (u : G) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (normalizes a.property) u).mp u.property⟩).toAdd

namespace ConjugationSection
variable {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}
variable (s : ConjugationSection H UH Z ρ)
include s

/-- The image of X ∩ U_H in the central section, whether or not X ≤ U_H. -/
def image (X : Subgroup G) : Submodule (ZMod 2) U :=
  AddSubgroup.toZModSubmodule 2 ((X.subgroupOf UH).map s.quotient).toAddSubgroup'

theorem mem_image (X : Subgroup G) (u : U) :
    u ∈ s.image X ↔ ∃ x : UH, (x : G) ∈ X ∧ (s.quotient x).toAdd = u := Iff.rfl

/-- The literal central quotient is isomorphic to the given binary carrier. -/
noncomputable def sectionEquiv [(Z.subgroupOf UH).Normal] :
    (UH ⧸ Z.subgroupOf UH) ≃* Multiplicative U :=
  (QuotientGroup.quotientMulEquivOfEq s.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective s.quotient s.surjective)

theorem quotient_eq_zero_iff (u : UH) :
    (s.quotient u).toAdd = 0 ↔ (u : G) ∈ Z := by
  change u ∈ s.quotient.ker ↔ _
  rw [s.kernel]
  rfl

theorem image_mono {X Y : Subgroup G} (h : X ≤ Y) : s.image X ≤ s.image Y := by
  rintro u ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- H centralizes V₁, so the critical denominator contains the quotient kernel. -/
theorem line_le_DH (Ug A : Subgroup G) (hUg : Ug ≤ H) : Z ≤ Source.DH UH Ug A := by
  apply le_commutatorPreimage s.line_le
  have hc : Ug ≤ centralizer (Z : Set G) := hUg.trans s.centralizes
  rw [commutator_comm]
  exact (commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le

theorem commutator_mem (a : H) (u : UH) : ⁅(a : G), (u : G)⁆ ∈ UH :=
  commutator_le.mp (le_normalizer_iff_commutator_le_right.mp s.normalizes)
    a a.property u u.property

/-- Linear displacement is the image of the ambient group commutator. -/
theorem displacement (a : H) (u : UH) :
    ρ (QuotientGroup.mk' (pCore 2 H) a) (s.quotient u).toAdd - (s.quotient u).toAdd =
      (s.quotient ⟨⁅(a : G), (u : G)⁆, s.commutator_mem a u⟩).toAdd := by
  rw [s.conjugates]
  have he : (⟨⁅(a : G), (u : G)⁆, s.commutator_mem a u⟩ : UH) =
      ⟨(a : G) * (u : G) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes a.property) u).mp u.property⟩ * u⁻¹ := rfl
  rw [he, map_mul, map_inv]
  exact sub_eq_add_neg _ _

theorem displacement_mem (X A S : Subgroup G)
    (hc : ⁅A, X⁆ ≤ S) :
    ∀ a ∈ Source.starImage H A, ∀ u ∈ s.image X, ρ a u - u ∈ s.image S := by
  rintro _ ⟨a, ha, rfl⟩ v hv
  obtain ⟨u, hu, rfl⟩ := (s.mem_image X v).mp hv
  rw [s.displacement]
  exact ⟨⟨⁅(a : G), (u : G)⁆, s.commutator_mem a u⟩,
    commutator_le.mp hc a ha u hu, rfl⟩

theorem quotient_mem_image_iff (X : Subgroup G) (hZX : Z ≤ X) (u : UH) :
    (s.quotient u).toAdd ∈ s.image X ↔ (u : G) ∈ X := by
  change u ∈ ((X.subgroupOf UH).map s.quotient).comap s.quotient ↔ _
  rw [Subgroup.comap_map_eq]
  have hk : s.quotient.ker ≤ X.subgroupOf UH := by
    rw [s.kernel]
    exact fun x hx => hZX hx
  rw [sup_eq_left.mpr hk]
  rfl

/-- Instantiate section transport after checking its kernel containment. -/
theorem relativeIndex_image (I D : Subgroup G) (hIU : I ≤ UH) (hZD : Z ≤ D) :
    ((D.subgroupOf UH).map s.quotient).relIndex ((I.subgroupOf UH).map s.quotient) =
      D.relIndex I := by
  have hk : s.quotient.ker ≤ D.subgroupOf UH := by
    rw [s.kernel]
    exact fun x hx => hZD hx
  rw [relIndex_image_of_kernel_le s.quotient (I.subgroupOf UH) (D.subgroupOf UH) hk]
  exact Subgroup.relIndex_subgroupOf hIU

/-- Invariance of the image lifts because I contains the entire kernel. -/
theorem normalizes_of_image_invariant (I : Subgroup G) (hZI : Z ≤ I) (hIU : I ≤ UH)
    (hI : ∀ a : H, ∀ u ∈ s.image I,
      ρ (QuotientGroup.mk' (pCore 2 H) a) u ∈ s.image I) :
    H ≤ normalizer (I : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  let u : UH := ⟨x, hIU hx⟩
  have hu : (s.quotient u).toAdd ∈ s.image I := (s.quotient_mem_image_iff I hZI u).mpr hx
  have hc := hI ⟨a, ha⟩ (s.quotient u).toAdd hu
  rw [s.conjugates] at hc
  exact (s.quotient_mem_image_iff I hZI _).mp hc

/-- Intersection commutes with passage to the section when its denominator
contains the quotient kernel. -/
theorem image_inf (I D : Subgroup G) (hZD : Z ≤ D) :
    s.image (I ⊓ D) = s.image I ⊓ s.image D := by
  apply le_antisymm
  · exact le_inf (s.image_mono inf_le_left) (s.image_mono inf_le_right)
  · intro v hv
    obtain ⟨x, hx, he⟩ := (s.mem_image I v).mp hv.1
    obtain ⟨d, hd, hde⟩ := (s.mem_image D v).mp hv.2
    have hk : x * d⁻¹ ∈ s.quotient.ker := by
      change s.quotient (x * d⁻¹) = 1
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr (Multiplicative.toAdd.injective (he.trans hde.symm))
    rw [s.kernel] at hk
    have hxd : (x : G) ∈ D := by
      have ht := D.mul_mem (hZD hk) hd
      change ((x : G) * (d : G)⁻¹) * (d : G) ∈ D at ht
      simpa only [inv_mul_cancel_right] using ht
    exact (s.mem_image (I ⊓ D) v).mpr ⟨x, ⟨hx, hxd⟩, he⟩

/-- Centrality is transported by the specified ambient conjugator. -/
theorem centralizes_conjugate_line (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤
      centralizer ((Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g)
    ((mem_centralizer_iff.mp (s.centralizes ha)) z hz)

/-- Faithfulness identifies the critical kernel with the actual two-core
intersection. This proves the equality rather than assuming it. -/
theorem Dgamma_eq_inf_core (Ug : Subgroup G) (hUg : Ug ≤ H)
    (hfaith : Function.Injective ρ) :
    Source.Dgamma Ug UH Z = Ug ⊓ Source.QH H := by
  have hn : Ug ≤ normalizer (Z : Set G) :=
    hUg.trans (s.centralizes.trans (centralizer_le_normalizer _))
  have hcore (a : H) : (a : G) ∈ Source.QH H ↔
      QuotientGroup.mk' (pCore 2 H) a = 1 := by
    change (a : G) ∈ (pCore 2 H).map H.subtype ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, he⟩
      have he' : b = a := Subtype.ext he
      subst b
      exact (QuotientGroup.eq_one_iff a).mpr hb
    · intro ha
      exact ⟨a, (QuotientGroup.eq_one_iff a).mp ha, rfl⟩
  apply le_antisymm
  · intro x hx
    have hxUg := commutatorPreimage_le Ug UH Z hx
    refine ⟨hxUg, (hcore ⟨x, hUg hxUg⟩).mpr ?_⟩
    apply hfaith
    ext v
    obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
    have he : (s.quotient u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [← he]
    change ρ (QuotientGroup.mk' (pCore 2 H) ⟨x, hUg hxUg⟩) (s.quotient u).toAdd =
      ρ 1 (s.quotient u).toAdd
    rw [map_one]
    apply sub_eq_zero.mp
    change ρ (QuotientGroup.mk' (pCore 2 H) ⟨x, hUg hxUg⟩) (s.quotient u).toAdd - (s.quotient u).toAdd = 0
    rw [s.displacement]
    exact (s.quotient_eq_zero_iff _).mpr
      (commutator_le.mp (commutator_commutatorPreimage_le Ug UH Z hn) x hx u u.property)
  · apply le_commutatorPreimage inf_le_left
    apply commutator_le.mpr
    intro x hx u hu
    have he := (hcore ⟨x, hUg hx.1⟩).mp hx.2
    apply (s.quotient_eq_zero_iff ⟨⁅x,u⁆, s.commutator_mem ⟨x,hUg hx.1⟩ ⟨u,hu⟩⟩).mp
    rw [← s.displacement ⟨x,hUg hx.1⟩ ⟨u,hu⟩, he, map_one]
    exact sub_self _

/-- The actor rank is the logarithm of the actual critical relative index. -/
theorem Dgamma_relIndex (Ug : Subgroup G) (hUg : Ug ≤ H)
    (hfaith : Function.Injective ρ) :
    (Source.Dgamma Ug UH Z).relIndex Ug = Nat.card (Source.starImage H Ug) := by
  rw [s.Dgamma_eq_inf_core Ug hUg hfaith, inf_relIndex_left]
  rw [← Subgroup.relIndex_subgroupOf (H := Source.QH H) hUg]
  have he : (Source.QH H).subgroupOf H = pCore 2 H := by
    change ((pCore 2 H).map H.subtype).comap H.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [he]
  simpa only [QuotientGroup.ker_mk', Source.starImage] using
    Subgroup.relIndex_ker (Ug.subgroupOf H) (QuotientGroup.mk' (pCore 2 H))

variable [Finite G] [FiniteDimensional (ZMod 2) U]

theorem image_finrank_le (X : Subgroup G) :
    Module.finrank (ZMod 2) (s.image X) ≤ Nat.log 2 (Nat.card X) := by
  have hsurj : Function.Surjective
      (fun x : X.subgroupOf UH => (⟨(s.quotient x.val).toAdd,
        ⟨x.val, x.property, rfl⟩⟩ : s.image X)) := by
    intro u
    obtain ⟨x, hx, he⟩ := (s.mem_image X u).mp u.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hi : Function.Injective (fun x : X.subgroupOf UH => (⟨x.val.val, x.property⟩ : X)) := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : X => (z : G)) h))
  have hc := (Nat.card_le_card_of_surjective _ hsurj).trans
    (Nat.card_le_card_of_injective _ hi)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have := Nat.log_monotone (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using this

omit [Finite G] in
/-- The first isomorphism theorem gives the dimension of the displayed
quotient, with the containment of V₁ in its denominator checked explicitly. -/
theorem quotient_finrank (D : Subgroup G) (hZD : Z ≤ D) :
    Module.finrank (ZMod 2) (U ⧸ s.image D) = Nat.log 2 (D.relIndex UH) := by
  let q : UH →* Multiplicative (U ⧸ s.image D) :=
    (s.image D).mkQ.toAddMonoidHom.toMultiplicative.comp s.quotient
  have hq : Function.Surjective q := by
    intro u
    obtain ⟨v, hv⟩ := (s.image D).mkQ_surjective u.toAdd
    obtain ⟨x, hx⟩ := s.surjective (Multiplicative.ofAdd v)
    exact ⟨x, by change (s.image D).mkQ (s.quotient x).toAdd = u.toAdd; rw [hx]; exact hv⟩
  have hk : q.ker = D.subgroupOf UH := by
    ext x
    change (s.image D).mkQ (s.quotient x).toAdd = 0 ↔ (x : G) ∈ D
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change x ∈ ((D.subgroupOf UH).map s.quotient).comap s.quotient ↔ _
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr (show s.quotient.ker ≤ D.subgroupOf UH from ?_)]
    · rfl
    · rw [s.kernel]
      exact fun x hx => hZD hx
  have hc : D.relIndex UH = Nat.card (U ⧸ s.image D) := by
    change (D.subgroupOf UH).index = _
    rw [← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hq, Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rfl
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

omit [Finite G] in
/-- Transfer the subgroup-index comparison of F.9.16 / 13.8.8(2) to the
linear inequality required by the noncyclic endgame. -/
theorem critical_bound (Ug A : Subgroup G) (hUg : Ug ≤ H)
    (hfaith : Function.Injective ρ)
    (hcritical : Nat.log 2 ((Source.DH UH Ug A).relIndex UH) ≤
      Nat.log 2 ((Source.Dgamma Ug UH Z).relIndex Ug)) :
    Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH Ug A)) ≤
      rank (Source.starImage H Ug) := by
  rw [s.quotient_finrank _ (s.line_le_DH Ug A hUg)]
  simpa only [s.Dgamma_relIndex Ug hUg hfaith, rank] using hcritical

/-- The defining commutator bound for D_H yields a line-valued displacement
on its image. Local normalization, not ambient normality, suffices. -/
theorem critical_line_displacement (Ug A : Subgroup G)
    (hUA : UH ≤ normalizer (A : Set G)) (hA : Nat.card A = 2) :
    Module.finrank (ZMod 2) (s.image A) ≤ 1 ∧
      ∀ a ∈ Source.starImage H Ug, ∀ d ∈ s.image (Source.DH UH Ug A),
        ρ a d - d ∈ s.image A := by
  refine ⟨?_, s.displacement_mem _ _ _ ?_⟩
  · have hc := s.image_finrank_le A
    simpa only [hA, show Nat.log 2 2 = 1 from by decide] using hc
  · rw [commutator_comm]
    exact commutator_commutatorPreimage_le UH Ug A hUA


omit [FiniteDimensional (ZMod 2) U] in
/-- An order-two subgroup outside U_H has zero image in its central section. -/
theorem image_eq_bot_of_not_le (A : Subgroup G) (hA : Nat.card A = 2)
    (hnot : ¬ A ≤ UH) : s.image A = ⊥ := by
  have hi : A ⊓ UH = ⊥ := by
    have hd : Nat.card (A ⊓ UH : Subgroup G) ∣ 2 := by
      rw [← hA]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact card_eq_one.mp h1
    · have he : A ⊓ UH = A := eq_of_le_of_card_ge inf_le_left (by rw [hA, h2])
      exact (hnot (he.symm.le.trans inf_le_right)).elim
  apply le_bot_iff.mp
  intro v hv
  obtain ⟨x, hx, he⟩ := (s.mem_image A v).mp hv
  have hx1 : (x : G) = 1 := by
    have hm : (x : G) ∈ A ⊓ UH := ⟨hx, x.property⟩
    rw [hi] at hm
    exact hm
  have he1 : x = 1 := Subtype.ext hx1
  rw [he1, map_one] at he
  exact he.symm

/-- The consequence needed after the source reversal argument establishes
A₁ ≰ U_H. This theorem does not assert that reversal argument. -/
theorem critical_fixed_of_line_not_le (Ug A : Subgroup G)
    (hUA : UH ≤ normalizer (A : Set G)) (hA : Nat.card A = 2)
    (hnot : ¬ A ≤ UH) :
    s.image (Source.DH UH Ug A) ≤ fixedSpace ρ (Source.starImage H Ug) := by
  intro d hd a
  have hc := (s.critical_line_displacement Ug A hUA hA).2 a a.property d hd
  rw [s.image_eq_bot_of_not_le A hA hnot] at hc
  exact sub_eq_zero.mp hc

/-- The source conjugator also supplies normalization of A₁ and its order. -/
theorem critical_line_displacement_of_conjugate (Ug : Subgroup G) (g : G)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom) (hZ : Nat.card Z = 2) :
    Module.finrank (ZMod 2) (s.image (Z.map (MulAut.conj g).toMonoidHom)) ≤ 1 ∧
      ∀ a ∈ Source.starImage H Ug,
        ∀ d ∈ s.image (Source.DH UH Ug (Z.map (MulAut.conj g).toMonoidHom)),
        ρ a d - d ∈ s.image (Z.map (MulAut.conj g).toMonoidHom) := by
  apply s.critical_line_displacement
  · exact hreverse.trans ((s.centralizes_conjugate_line g).trans (centralizer_le_normalizer _))
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ]

omit [FiniteDimensional (ZMod 2) U] in
/-- From A₁ ≰ I and the conjugate of 13.7.3(7), the actual intersection
I ∩ D_H centralizes both actors. Image invariance supplies the needed relative
normality of I, and the kernel containment justifies the image intersection. -/
theorem critical_intersection_centralizes (I J Ug Vg A : Subgroup G)
    (hZI : Z ≤ I) (hIU : I ≤ UH) (N : Subrepresentation ρ)
    (hN : s.image I = N.toSubmodule)
    (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H) (hUJ : UH ≤ J)
    (hUA : UH ≤ normalizer (A : Set G))
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A)
    (hA : Nat.card A = 2) (hnot : ¬ A ≤ I) :
    ⁅I ⊓ Source.DH UH Ug A, Ug⁆ = ⊥ ∧
      ⁅I ⊓ Source.DH UH Ug A, Vg⁆ = ⊥ ∧
      s.image I ⊓ s.image (Source.DH UH Ug A) ≤
        fixedSpace ρ (Source.starImage H Vg) := by
  have hAI : A ⊓ I = ⊥ := by
    have hd : Nat.card (A ⊓ I : Subgroup G) ∣ 2 := by
      rw [← hA]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact card_eq_one.mp h1
    · have he : A ⊓ I = A := eq_of_le_of_card_ge inf_le_left (by rw [hA, h2])
      exact (hnot (he.symm.le.trans inf_le_right)).elim
  have hHI : H ≤ normalizer (I : Set G) := by
    apply s.normalizes_of_image_invariant I hZI hIU
    intro a u hu
    rw [hN] at hu ⊢
    exact N.apply_mem_toSubmodule _ hu
  have hVI : ⁅I ⊓ Source.DH UH Ug A, Vg⁆ ≤ I :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hVgH.trans hHI))
  have hUI : ⁅I ⊓ Source.DH UH Ug A, Ug⁆ ≤ I :=
    (commutator_mono le_rfl hUgVg).trans hVI
  have hUA' : ⁅I ⊓ Source.DH UH Ug A, Ug⁆ ≤ A :=
    (commutator_mono inf_le_right le_rfl).trans
      (commutator_commutatorPreimage_le UH Ug A hUA)
  have hU : ⁅I ⊓ Source.DH UH Ug A, Ug⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hAI]
    exact le_inf hUA' hUI
  have hVA : ⁅I ⊓ Source.DH UH Ug A, Vg⁆ ≤ A := by
    apply (commutator_mono (le_inf (inf_le_left.trans (hIU.trans hUJ))
      (commutator_eq_bot_iff_le_centralizer.mp hU)) le_rfl).trans hcentralizer
  have hV : ⁅I ⊓ Source.DH UH Ug A, Vg⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hAI]
    exact le_inf hVA hVI
  refine ⟨hU, hV, ?_⟩
  rw [← s.image_inf I _ (s.line_le_DH Ug A (hUgVg.trans hVgH))]
  intro v hv a
  have hc := s.displacement_mem (I ⊓ Source.DH UH Ug A) Vg ⊥
    (by rw [commutator_comm, hV]) a a.property v hv
  obtain ⟨x, hx, he⟩ := (s.mem_image ⊥ _).mp hc
  have hx1 : x = 1 := Subtype.ext hx
  rw [hx1, map_one] at he
  exact sub_eq_zero.mp he.symm

end ConjugationSection
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
