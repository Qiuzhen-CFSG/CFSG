module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.MarkedFusion
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Involutions.Roots
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Involutions.Checks
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Outside-core involutions in the literal Rudvalis max4

Sylow conjugacy inside max4 moves an involution into the fixed local Sylow.
Its binary normal forms admit a checked conjugacy forest. Twelve roots
centralize the marked eight-group and hence belong to the intrinsic core;
explicit ambient words conjugate the other three roots to its first
nonidentity generator. Normality of the core inside max4 removes the former
branch. The marked-eight theorem then supplies actual ambient Sylow-center
witnesses.

This proves the assertion of Aschbacher--Smith J.2.6(2), printed pp.434--435,
for the literal degree-4060 model, as required by I.2.2(7), printed p.413.
The source proof assumes both (Ru1) and (Ru2) and their compatible embeddings.
Here the checked word calculation proves the required fusion directly. It
uses neither a global involution table nor an assumed special-group structure.
ATLAS attribution and permutation conventions are preserved in the certificate
source directory. Conjugate-max4 transport remains in `Max4Geometry.Transport`.
-/

namespace Rudvalis.CoveringIncidence
open Subgroup SylowOvergroups SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate Max4InvolutionCertificate
open Theory.GroupTheory.DoubleCoverCentralizer

private theorem core_conj_mem (g : Model) (hg : g ∈ max4) (y : Model)
    (hy : y ∈ max4Core) : g * y * g⁻¹ ∈ max4Core :=
  (mem_normalizer_iff.mp (max4_le_normalizer_core hg) y).mp hy

private theorem normal_zero : normalForm 0 = 1 := by
  simp [normalForm]

private theorem normal_form_alternative (n : Fin 16384) (hsq : normalForm n ^ 2 = 1) :
    normalForm n ∈ max4Core ∨ IsConj (normalForm n) (elementaryGenerator 0) := by
  have aux (k : Nat) : ∀ n : Fin 16384, height n = k → normalForm n ^ 2 = 1 →
      normalForm n ∈ max4Core ∨ IsConj (normalForm n) (elementaryGenerator 0) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hn hsq
      rcases tests n with hzero | hbad | hroot | ⟨hheight, hpoints⟩
      · subst n
        exact Or.inl (by rw [normal_zero]; exact max4Core.one_mem)
      · apply (hbad _).elim
        have he := congrArg (fun g : Model => g • obstruction n) hsq
        simpa only [pow_two, mul_smul, normal_smul, one_smul] using he
      · exact root_alternative n hroot
      · have he : pcGenerator (letter n) * normalForm (parent n) *
            (pcGenerator (letter n))⁻¹ = normalForm n := by
          apply mul_inv_eq_iff_eq_mul.mpr
          apply eq_of_smul_first_five
          intro i
          simpa only [mul_smul, normal_smul, generator_smul] using (hpoints i).symm
        have hc : IsConj (normalForm (parent n)) (normalForm n) :=
          isConj_iff.mpr ⟨pcGenerator (letter n), he⟩
        have hpsq : normalForm (parent n) ^ 2 = 1 := by
          have hp := hc.pow 2
          rw [hsq] at hp
          exact isConj_one_left.mp hp
        rcases ih (height (parent n)) (hn ▸ hheight) (parent n) rfl hpsq with hp | hp
        · exact Or.inl (he ▸ core_conj_mem _ (localP_le_max4 (pcGenerator_mem _)) _ hp)
        · exact Or.inr (hc.symm.trans hp)
  exact aux (height n) n rfl hsq

/-- Local Sylow involutions outside the core are conjugate in the actual model
 to the first marked-eight generator. -/
public theorem localP_outside_core_isConj_marked (x : Model) (hx : x ∈ localP)
    (hxP : x ∉ max4Core) (hsq : x ^ 2 = 1) : IsConj x (elementaryGenerator 0) := by
  obtain ⟨n, rfl⟩ := normalFormCover x hx
  exact (normal_form_alternative n hsq).resolve_left hxP

/-- The ambient fusion assertion underlying J.2.6(2), with literal max4 and
intrinsic core and without a global involution-table premise. -/
public theorem outside_core_isConj_marked (x : Model) (hx : x ∈ max4)
    (hxP : x ∉ max4Core) (horder : orderOf x = 2) :
    IsConj x (elementaryGenerator 0) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨S, hS⟩ := intrinsicSylow
  let u : max4 := ⟨x, hx⟩
  have hu : orderOf u = 2 ^ 1 := by
    rw [← orderOf_injective max4.subtype max4.subtype_injective u]
    exact horder
  obtain ⟨v, hv⟩ := S.exists_isConj_of_orderOf_eq_prime_pow hu
  let y : Model := ((v : S) : max4)
  have hy : y ∈ localP := by
    rw [← hS]
    exact mem_map_of_mem max4.subtype v.property
  obtain ⟨g, hg⟩ := isConj_iff.mp hv
  have he : (g : Model) * x * (g : Model)⁻¹ = y :=
    congrArg (fun t : max4 => (t : Model)) hg
  have hyP : y ∉ max4Core := by
    intro hyP
    apply hxP
    apply (mem_normalizer_iff.mp (max4_le_normalizer_core g.property) x).mpr
    rwa [he]
  have hxsq : x ^ 2 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one x
  have hysq : y ^ 2 = 1 := by
    rw [← he, conj_pow, hxsq]
    simp
  exact (max4.subtype.map_isConj hv).trans
    (localP_outside_core_isConj_marked y hy hyP hysq)

/-- Explicit ambient conjugators to nonidentity marked-eight elements. -/
public theorem outside_core_conjugate_marked (x : Model) (hx : x ∈ max4)
    (hxP : x ∉ max4Core) (horder : orderOf x = 2) :
    ∃ (g : Model) (z : elementary 2), z ≠ 1 ∧ g * (z : Model) * g⁻¹ = x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (outside_core_isConj_marked x hx hxP horder).symm
  have hne (z : elementary 2) (hz : (z : Model) ≠ 1) : z ≠ 1 := by
    intro h
    exact hz (congrArg (fun z : elementary 2 => (z : Model)) h)
  exact ⟨g, ⟨elementaryGenerator 0, marked_mem⟩, hne _ marked_ne_one, hg⟩

/-- Every max4 involution outside its intrinsic two-core is two-central,
with an actual ambient Sylow and center-membership witness. -/
public theorem outside_core_twoCentral (x : Model) (hx : x ∈ max4)
    (hxP : x ∉ max4Core) (horder : orderOf x = 2) : TwoCentral x := by
  obtain ⟨g, z, hz, rfl⟩ := outside_core_conjugate_marked x hx hxP horder
  exact twoCentral_of_conjugate_marked g z hz

end Rudvalis.CoveringIncidence
