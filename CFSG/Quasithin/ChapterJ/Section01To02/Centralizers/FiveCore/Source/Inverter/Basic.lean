module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Inverter.SeedDefs
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.FixedPlane
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic


/-!
# Quaternion fusion for the geometric five-inverter

The literal two-conjugator seed lies in K: its L-conjugate lies in S,
S lies in K, and H normalizes K. Elementary abelianness and the earlier
J.2.6 fusion give its square and its z-class. Inversion normalizes B₅,
and relative normality of Q then makes CQ invariant.

K acts trivially on HC/U. Since CQ lies in HC and CQ ∩ U = Z, each
commutator of the seed with CQ belongs to Z. If the action is nontrivial,
a nonidentity commutator is the marked generator z; the same quaternion
element conjugates i to zi. Thus quaternion fusion is proved from the
noncentral-action premise, which remains the separate geometric obligation.

Source: Aschbacher–Smith, J.2.7(5), printed p.436 (PDF p.447), using
J.2.2(1,3) and J.2.6(4). No later centralizer recognition is used.
-/

public section
noncomputable section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  {B5 : Sylow 5 d.toTypeRuSetup.H}

namespace FiveInverterSeed
variable (v : FiveInverterSeed B5)

theorem ne_one : v.i ≠ 1 := fun he => v.not_mem_Q (he ▸ d.toTypeRuSetup.Q.one_mem)

theorem mem_K : v.i ∈ d.toTypeRuSetup.K := by
  obtain ⟨u, hu, he⟩ := v.mem_conjugate
  have hS : (v.l : G) * u * (v.l : G)⁻¹ ∈ d.toTypeRuSetup.S :=
    ConjugateIntersections.conjugateU_le_S d v.l v.l.property
      (mem_map.mpr ⟨u, hu, rfl⟩)
  have hK : (v.l : G) * u * (v.l : G)⁻¹ ∈ d.toTypeRuSetup.K :=
    (d.S_le_L₁.trans (embedded_pResidual_mono 2 inf_le_right)) hS
  have hnorm := le_normalizer_embedded_pResidual 2 d.toTypeRuSetup.H v.h.property
  have hm := (mem_normalizer_iff.mp hnorm _).mp hK
  have hi : v.i = (v.h : G) * ((v.l : G) * u * (v.l : G)⁻¹) * (v.h : G)⁻¹ := by
    rw [← he]
    change ((v.h : G) * v.l) * u * ((v.h : G) * v.l)⁻¹ = _
    group
  rwa [hi]

theorem mem_H : v.i ∈ d.toTypeRuSetup.H := d.toTypeRuSetup.K_le_H v.mem_K

theorem square : v.i ^ 2 = 1 := by
  obtain ⟨u, hu, he⟩ := v.mem_conjugate
  have hs : (⟨u, hu⟩ : d.toTypeRuSetup.U) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp d.elementary_U.exponent_dvd_p _
  have hs' : u ^ 2 = 1 := congrArg Subtype.val hs
  rw [← he, ← map_pow, hs', map_one]

theorem z_class (c : Choices d) (earlier : EarlierJ27Inputs c) : IsConj v.i c.z := by
  obtain ⟨u, hu, he⟩ := v.mem_conjugate
  have hu1 : u ≠ 1 := by
    intro h
    apply v.ne_one
    rw [← he, h, map_one]
  have hz := earlier.j26.2.2.2.2.2 u hu hu1
  exact (isConj_iff.mpr ⟨(v.h : G) * (v.l : G), he⟩).symm.trans hz

theorem normalizes_B5Image : v.i ∈ normalizer (B5Image B5 : Set G) := by
  have hf (x : G) (hx : x ∈ B5Image B5) : v.i*x*v.i⁻¹ ∈ B5Image B5 := by
    rw [v.inverts x hx]
    exact (B5Image B5).inv_mem hx
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  have hh := hf _ hx
  have hs : v.i * v.i = 1 := by simpa only [pow_two] using v.square
  have he : v.i * (v.i * x * v.i⁻¹) * v.i⁻¹ = x := by
    calc
      _ = (v.i*v.i) * x * (v.i*v.i)⁻¹ := by group
      _ = x := by rw [hs]; simp
  rwa [he] at hh

theorem normalizes_CQ : v.i ∈ normalizer (CQ B5 : Set G) := by
  have hQ := d.ru2.six.normalized v.mem_H
  have hN : normalizer (B5Image B5 : Set G) ≤ normalizer (G5 B5 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hC := hN v.normalizes_B5Image
  intro x
  exact and_congr (mem_normalizer_iff.mp hQ x) (mem_normalizer_iff.mp hC x)

/-- K acts trivially on HC/U, so every quaternion commutator lies in Z. -/
theorem commutator_mem_Z (q : FiveQuaternionData B5) (t : CQ B5) :
    ⁅(t : G), v.i⁆ ∈ d.toTypeRuSetup.Z := by
  have hU : ⁅(t : G), v.i⁆ ∈ d.toTypeRuSetup.U := by
    simpa only [commutatorElement_inv] using d.toTypeRuSetup.U.inv_mem
      (d.HC_commutator_K_mem_U ⟨t, q.le_HC t.property⟩ ⟨v.i, v.mem_K⟩)
  have hQ : ⁅(t : G), v.i⁆ ∈ CQ B5 := by
    have hh := (mem_normalizer_iff.mp v.normalizes_CQ ((t : G)⁻¹)).mp
      ((CQ B5).inv_mem t.property)
    simpa only [commutatorElement_def, mul_assoc] using (CQ B5).mul_mem t.property hh
  rw [← q.inf_U]
  exact ⟨hQ, hU⟩

/-- Nontrivial action yields the actual quaternion conjugator, not just ambient fusion. -/
theorem fused (c : Choices d) (q : FiveQuaternionData B5)
    (hn : v.i ∉ centralizer (CQ B5 : Set G)) :
    ∃ t : CQ B5, (t : G) * v.i * (t : G)⁻¹ = c.z * v.i := by
  classical
  change ¬ ∀ t ∈ CQ B5, t * v.i = v.i * t at hn
  push Not at hn
  obtain ⟨t, ht, hne⟩ := hn
  have hc := v.commutator_mem_Z q ⟨t, ht⟩
  have hc1 : ⁅t, v.i⁆ ≠ 1 := fun he => hne
    (commutatorElement_eq_one_iff_mul_comm.mp he)
  have hz1 : c.z ≠ 1 := by
    intro he
    have hcard := d.card_Z
    simp only [c.z_generator, he, zpowers_one_eq_bot, card_bot] at hcard
    omega
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : d.toTypeRuSetup.Z)).mp d.card_Z
  have he : (⟨⁅t, v.i⁆, hc⟩ : d.toTypeRuSetup.Z) = ⟨c.z, c.z_mem_Z⟩ :=
    (hw _ (fun h => hc1 (congrArg Subtype.val h))).trans
      (hw _ (fun h => hz1 (congrArg Subtype.val h))).symm
  refine ⟨⟨t, ht⟩, ?_⟩
  have he' : ⁅t, v.i⁆ = c.z := congrArg Subtype.val he
  calc
    t * v.i * t⁻¹ = ⁅t, v.i⁆ * v.i := by rw [commutatorElement_def]; group
    _ = c.z * v.i := by rw [he']

end FiveInverterSeed
end CFSG.Quasithin.ChapterJ.Centralizers.Choices
