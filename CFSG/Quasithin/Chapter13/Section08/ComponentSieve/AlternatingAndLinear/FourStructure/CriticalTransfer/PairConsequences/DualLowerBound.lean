module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.NaturalLowerBound
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.PlaneSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.UpperSection
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# The dual irreducible-section lower bound

The source intersection centralizes Vγ, but this alone does not give
codimension two on a contragredient irreducible. Nor does excluding a common
transvection center: that bounds the commutator dimension, not fixed
codimension.

This module supplies two additional arguments. First, V₁ outside Uγ makes
fixed vectors lift through the actual central quotient, identifying the
critical denominator with both fixed spaces. Second, faithful quadratic
actors fixing a hyperplane are determined by their commutator spaces.
Consequently the forward commutator equality and strict Uγ* < Vγ* give
the desired bound, for the dual action through the specified identification.

The final theorem discharges strict inclusion using the upper-section
argument of 13.8.11(1). The index-two seed and its marked plane-parabolic
normalizer construct the permutation-module input on the actual V_H/U_H;
the same ambient conjugator transports it to Vγ/Uγ. Equality of star
images would then give a nonidentity transvection, which the intrinsic
plane-permutation theorem excludes. The earlier source generation and
edge-centrality conclusions and the forward commutator equality remain
explicit inputs. No fixed-hyperplane exclusion on dual I is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed p.962 (PDF p.979), together with
13.8.4(5–6), 13.8.9, 13.8.11(1), and 13.7.3(7). The nonsplitting conclusions
from B.4.9(1) alone do not provide the missing fixed-codimension bound.
-/

public section

open Representation Representation.BinaryOffender Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

section Linear
variable {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Evaluation outside a fixed hyperplane identifies a quadratic binary
actor with its entire commutator space. Equal commutator spaces therefore
force equal nested actors when the representation is faithful. -/
private theorem actors_eq_of_fixed_codim_le_one
    (ρ : Representation (ZMod 2) K U) (hfaith : Function.Injective ρ)
    (A B : Subgroup K) (hAB : A ≤ B) (hquad : IsQuadratic ρ B)
    (D : Submodule (ZMod 2) U) (hfix : D ≤ fixedSpace ρ B)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ 1)
    (hcomm : Coinvariants.ker (ρ.comp A.subtype) =
      Coinvariants.ker (ρ.comp B.subtype)) : A = B := by
  obtain ⟨q, hq⟩ := (finrank_le_one_iff (K := ZMod 2) (V := U ⧸ D)).mp hdim
  obtain ⟨v, rfl⟩ := D.mkQ_surjective q
  have hdisp (a : K) (ha : a ∈ B) (w : U) :
      ∃ c : ZMod 2, ρ a w - w = c • (ρ a v - v) := by
    obtain ⟨c, hc⟩ := hq (D.mkQ w)
    have hd : w - c • v ∈ D := by
      apply (Submodule.Quotient.mk_eq_zero D).mp
      change D.mkQ (w - c • v) = 0
      rw [map_sub, map_smul, hc, sub_self]
    have hf : ρ a (w - c • v) = w - c • v := hfix hd ⟨a, ha⟩
    refine ⟨c, ?_⟩
    calc
      ρ a w - w = ρ a (w - c • v) + c • ρ a v - ((w - c • v) + c • v) := by
        rw [map_sub, map_smul]
        abel
      _ = c • (ρ a v - v) := by rw [hf, smul_sub]; abel
  have hmul (a b : K) (ha : a ∈ B) (hb : b ∈ B) :
      ρ (a * b) v - v = (ρ a v - v) + (ρ b v - v) := by
    calc
      ρ (a * b) v - v = ρ a (ρ b v - v) + (ρ a v - v) := by
        rw [map_mul, Module.End.mul_apply, map_sub]
        abel
      _ = (ρ a v - v) + (ρ b v - v) := by rw [hquad a ha b hb v]; abel
  let S : Submodule (ZMod 2) U := {
    carrier := {w | ∃ a ∈ A, ρ a v - v = w}
    zero_mem' := ⟨1, A.one_mem, by simp⟩
    add_mem' := by
      rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a * b, A.mul_mem ha hb, hmul a b (hAB ha) (hAB hb)⟩
    smul_mem' := by
      intro c w hw
      fin_cases c
      · change ∃ a ∈ A, ρ a v - v = (0 : ZMod 2) • w
        exact ⟨1, A.one_mem, by simp⟩
      · change ∃ a ∈ A, ρ a v - v = (1 : ZMod 2) • w
        simpa using hw }
  have hS : Coinvariants.ker (ρ.comp A.subtype) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, w⟩, rfl⟩
    obtain ⟨c, hc⟩ := hdisp a (hAB a.property) w
    change ρ a w - w ∈ S
    rw [hc]
    exact S.smul_mem c ⟨a, a.property, rfl⟩
  apply le_antisymm hAB
  intro b hb
  have hm := Coinvariants.sub_mem_ker (ρ := ρ.comp B.subtype) ⟨b, hb⟩ v
  rw [← hcomm] at hm
  obtain ⟨a, ha, he⟩ := hS hm
  have hab : a = b := by
    apply hfaith
    ext w
    obtain ⟨c, hc⟩ := hq (D.mkQ w)
    have hd : w - c • v ∈ D := by
      apply (Submodule.Quotient.mk_eq_zero D).mp
      change D.mkQ (w - c • v) = 0
      rw [map_sub, map_smul, hc, sub_self]
    have hfa : ρ a (w - c • v) = w - c • v := hfix hd ⟨a, hAB ha⟩
    have hfb : ρ b (w - c • v) = w - c • v := hfix hd ⟨b, hb⟩
    have he' : ρ a v = ρ b v := sub_left_injective he
    have hdw : w = (w - c • v) + c • v := by abel
    rw [hdw, map_add, map_add, hfa, hfb, map_smul, map_smul, he']
  exact hab ▸ ha

end Linear

section Source
variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

omit [FiniteDimensional (ZMod 2) U] in
/-- A fixed vector lifts to an actual centralizing element: its commutators
lie both in the quotient kernel V₁ and in Uγ, whose intersection is trivial.
This checks the extra kernel containment needed to recover the denominator. -/
theorem fixedSpace_le_critical_denominator
    (s : ConjugationSection H UH Z ρ) (I Ug A : Subgroup G)
    (hUgH : Ug ≤ H) (hIU : I ≤ UH) (hIUg : I ≤ normalizer (Ug : Set G))
    (hZ : Nat.card Z = 2) (hnotZ : ¬ Z ≤ Ug)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule) :
    fixedSpace N.toRepresentation (Source.starImage H Ug) ≤
      (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype := by
  have hzUg : Z ⊓ Ug = ⊥ := by
    have hd : Nat.card (Z ⊓ Ug : Subgroup G) ∣ 2 := by
      rw [← hZ]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact card_eq_one.mp h1
    · have he : Z ⊓ Ug = Z := eq_of_le_of_card_ge inf_le_left (by rw [hZ, h2])
      exact (hnotZ (he.symm.le.trans inf_le_right)).elim
  intro v hv
  obtain ⟨x, hx, he⟩ := (s.mem_image I v).mp (hN.symm ▸ v.property)
  have hxc : (x : G) ∈ centralizer (Ug : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    let aH : H := ⟨a, hUgH ha⟩
    have hf := congrArg Subtype.val
      (hv ⟨QuotientGroup.mk' (pCore 2 H) aH, mem_map_of_mem _ ha⟩)
    change ρ (QuotientGroup.mk' (pCore 2 H) aH) (v : U) = v at hf
    rw [← he] at hf
    have hcz : ⁅a, (x : G)⁆ ∈ Z := by
      apply (s.quotient_eq_zero_iff ⟨⁅a, (x : G)⁆, s.commutator_mem aH x⟩).mp
      rw [← s.displacement aH x]
      exact sub_eq_zero.mpr hf
    have hcu : ⁅a, (x : G)⁆ ∈ Ug :=
      commutator_le.mp (le_normalizer_iff_commutator_le_left.mp hIUg) a ha x hx
    have hc : ⁅a, (x : G)⁆ = 1 := by
      have hm : ⁅a, (x : G)⁆ ∈ Z ⊓ Ug := ⟨hcz, hcu⟩
      rwa [hzUg] at hm
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  have hcd : UH ⊓ centralizer (Ug : Set G) ≤ Source.DH UH Ug A := by
    apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
  exact (s.mem_image _ _).mpr ⟨x, hcd ⟨hIU hx, hxc⟩, he⟩

omit [FiniteDimensional (ZMod 2) U] in
/-- With V₁ outside Uγ, the actual critical denominator on I/V₁ is exactly
the fixed space for either actor. The forward containment uses the source
intersection-centralizer argument; the reverse one uses the trivial kernel
intersection, rather than an identification of quotient and group centralizers. -/
theorem critical_denominator_eq_fixedSpace
    (s : ConjugationSection H UH Z ρ)
    (I J Ug Vg A : Subgroup G) (hZI : Z ≤ I) (hIU : I ≤ UH)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H) (hUJ : UH ≤ J)
    (hUA : UH ≤ normalizer (A : Set G))
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A)
    (hA : Nat.card A = 2) (hnot : ¬ A ≤ I)
    (hIUg : I ≤ normalizer (Ug : Set G))
    (hZ : Nat.card Z = 2) (hnotZ : ¬ Z ≤ Ug) :
    (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype =
        fixedSpace N.toRepresentation (Source.starImage H Ug) ∧
      fixedSpace N.toRepresentation (Source.starImage H Ug) =
        fixedSpace N.toRepresentation (Source.starImage H Vg) := by
  have hfix := (s.critical_intersection_centralizes I J Ug Vg A hZI hIU N hN
    hUgVg hVgH hUJ hUA hcentralizer hA hnot).2.2
  rw [hN] at hfix
  have hDB : (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype ≤
      fixedSpace N.toRepresentation (Source.starImage H Vg) := by
    intro v hv a
    exact Subtype.ext (hfix ⟨v.property, hv⟩ a)
  have hBA : fixedSpace N.toRepresentation (Source.starImage H Vg) ≤
      fixedSpace N.toRepresentation (Source.starImage H Ug) := by
    intro v hv a
    have hAB : Source.starImage H Ug ≤ Source.starImage H Vg :=
      map_mono (show Ug.subgroupOf H ≤ Vg.subgroupOf H from fun x hx => hUgVg hx)
    exact hv ⟨a, hAB a.property⟩
  have hAD := fixedSpace_le_critical_denominator s I Ug A
    (hUgVg.trans hVgH) hIU hIUg hZ hnotZ N hN
  exact ⟨le_antisymm (hDB.trans hBA) hAD, le_antisymm (hAD.trans hDB) hBA⟩

omit [Finite G] [FiniteDimensional (ZMod 2) U] in
private theorem dual_subrepresentation_faithful
    (N : Subrepresentation ρ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : N.toSubmodule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (N.toRepresentation g u) = (ChiefFactors.naturalAction eH).dual g (e u)) :
    Function.Injective N.toRepresentation := by
  intro g k hgk
  apply inv_injective
  apply eH.injective
  apply LinearEquiv.ext
  intro v
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
  intro f
  obtain ⟨u, rfl⟩ := e.surjective f
  have ht := (he g u).symm.trans ((congrArg e (LinearMap.congr_fun hgk u)).trans (he k u))
  have hv := LinearMap.congr_fun ht v
  change e u (eH g⁻¹ v) = e u (eH k⁻¹ v) at hv
  rw [map_sub, hv, sub_self]

/-- The dual branch once strict inclusion of the actual star images is
established. A centralized hyperplane and the forward commutator equality
would force the two faithful quadratic actors to coincide. The strictness
premise is additional: it must be discharged before this lemma supplies the
source lower bound. No hyperplane exclusion on dual I is assumed. -/
theorem critical_section_codimension_ge_two_of_dual_strict_actors
    (s : ConjugationSection H UH Z ρ)
    (I J Ug Vg A : Subgroup G) (hZI : Z ≤ I) (hIU : I ≤ UH)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H) (hUJ : UH ≤ J)
    (hUA : UH ≤ normalizer (A : Set G))
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A)
    (hA : Nat.card A = 2) (hnot : ¬ A ≤ I)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : N.toSubmodule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (N.toRepresentation g u) = (ChiefFactors.naturalAction eH).dual g (e u))
    (hquad : IsQuadratic ρ (Source.starImage H Vg))
    (hcomm : Coinvariants.ker (N.toRepresentation.comp (Source.starImage H Ug).subtype) =
      Coinvariants.ker (N.toRepresentation.comp (Source.starImage H Vg).subtype))
    (hstrict : Source.starImage H Ug < Source.starImage H Vg) :
    2 ≤ Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype) := by
  have hfix := (s.critical_intersection_centralizes I J Ug Vg A hZI hIU N hN
    hUgVg hVgH hUJ hUA hcentralizer hA hnot).2.2
  rw [hN] at hfix
  have hDB : (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype ≤
      fixedSpace N.toRepresentation (Source.starImage H Vg) := by
    intro v hv a
    exact Subtype.ext (hfix ⟨v.property, hv⟩ a)
  by_contra! hsmall
  apply hstrict.ne
  apply actors_eq_of_fixed_codim_le_one N.toRepresentation
    (dual_subrepresentation_faithful N eH e he) _ _ hstrict.le
    (fun a ha b hb v => Subtype.ext (hquad a ha b hb v)) _ hDB (by omega) hcomm

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The dual irreducible-section bound from the actual source setup and
complete earlier local inputs. The dual identification and marked plane
use the same eH. The upper quotient is linked by its quotient map and
conjugation formula, and all endpoint subgroups use the same conjugator.

The seed X is source V, P is the natural plane stabilized by (H ∩ M)*,
and B is the terminal edge group. Its index-two image and conjugate span
are 13.8.4(5); hgen is the allowed 13.8.18(2) generation statement.
The commutator equality is the forward marked-radical input. Strict actor
inclusion is proved, rather than assumed. The nonsplitting restrictions
and rank(Uγ*)>1 used earlier in the source are not needed again once
these forward inputs and the dual identification have been established. -/
theorem critical_section_codimension_ge_two_of_dual
    (s : ConjugationSection H UH Z ρ)
    (I J Ug Vg A : Subgroup G) (hZI : Z ≤ I) (hIU : I ≤ UH)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hVgH : Vg ≤ H) (hUJ : UH ≤ J)
    (hUA : UH ≤ normalizer (A : Set G))
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A)
    (hA : Nat.card A = 2) (hnot : ¬ A ≤ I)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : N.toSubmodule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (N.toRepresentation g u) = (ChiefFactors.naturalAction eH).dual g (e u))
    (hquad : IsQuadratic ρ (Source.starImage H Vg))
    (hcomm : Coinvariants.ker (N.toRepresentation.comp (Source.starImage H Ug).subtype) =
      Coinvariants.ker (N.toRepresentation.comp (Source.starImage H Vg).subtype))
    (VH : Subgroup G) (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H VH UH τ)
    (X : Subgroup G) (hXV : X ≤ VH) (hspan : VH = conjugateSpanBy X H)
    (hindex : UH.relIndex X = 2)
    (P : Submodule (ZMod 2) ChiefFactors.NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hparabolic : ∀ a : H, eH (QuotientGroup.mk' (pCore 2 H) a) ∈
      BinaryLinear.parabolic P → (a : G) ∈ normalizer (X : Set G))
    (g : G) (B : Subgroup G)
    (hJ : J = H.map (MulAut.conj g).toMonoidHom)
    (hUg : Ug = UH.map (MulAut.conj g).toMonoidHom)
    (hVg : Vg = VH.map (MulAut.conj g).toMonoidHom)
    (hZ : Nat.card Z = 2)
    (hgen : J = conjugateSpanBy UH J ⊔ B)
    (hedge : ⁅B, X.map (MulAut.conj g).toMonoidHom⁆ ≤ Ug)
    (hnoncentral : ¬ ⁅H, VH⁆ ≤ UH) :
    2 ≤ Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype) := by
  have hstrict := starImage_lt_of_plane_seed s VH τ t eH X hXV hspan hindex
    P hP hparabolic g J Ug Vg B hJ hUg hVg hVgH hUJ hZ hgen hedge hnoncentral
  have hUgVg : Ug ≤ Vg := by
    rw [hUg, hVg]
    exact map_mono t.kernel_le
  exact critical_section_codimension_ge_two_of_dual_strict_actors s I J Ug Vg A
    hZI hIU N hN hUgVg hVgH hUJ hUA hcentralizer hA hnot eH e he hquad hcomm hstrict

end Source

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
