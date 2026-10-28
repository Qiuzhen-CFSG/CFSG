module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.QuotientImages
public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# The actual elementary sections for G.2.5 recognition

Normalization of the three U-conjugates by S makes their intersections
with S normal in S. Commutators between distinct W-groups lie in their
pair intersections. Together with the Frattini square bound this makes
S/S₃ elementary abelian. The same argument inside the three pair
intersections makes S₃/S₂ elementary abelian. These are the literal
quotients, including when either quotient is trivial.

Only the earlier G.2.2 and G.2.5(1–3) inputs are used here. Invariance of
S₃ under the full actor I and the natural/dual module recognition require
the separate projective root-group argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(4,6–7), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Setup
variable {G : Type*} [Group G]

private theorem normalized_sup {P A B : Subgroup G}
    (hA : P ≤ normalizer (A : Set G)) (hB : P ≤ normalizer (B : Set G)) :
    P ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro p hp
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hA hp),
    mem_normalizer_iff_map_conj_eq.mp (hB hp)]

private theorem commutator_join_left_le {P A B C E : Subgroup G}
    (hAP : A ≤ P) (hBP : B ≤ P) (hPE : P ≤ normalizer (E : Set G))
    (hA : ⁅A, C⁆ ≤ E) (hB : ⁅B, C⁆ ≤ E) : ⁅A ⊔ B, C⁆ ≤ E :=
  (commutator_mono (sup_le (le_commutatorPreimage hAP hA)
    (le_commutatorPreimage hBP hB)) le_rfl).trans
      (commutator_commutatorPreimage_le P C E hPE)

private theorem commutator_pair_le {P A B C E : Subgroup G}
    (hAP : A ≤ P) (hBP : B ≤ P) (hCP : C ≤ P)
    (hA : P ≤ normalizer (A : Set G)) (hB : P ≤ normalizer (B : Set G))
    (hC : P ≤ normalizer (C : Set G)) (hE : P ≤ normalizer (E : Set G))
    (hAA : ⁅A, A⁆ ≤ E) (hBB : ⁅B, B⁆ ≤ E)
    (htriple : A ⊓ B ⊓ C ≤ E) : ⁅(A ⊔ B) ⊔ C, A ⊓ B⁆ ≤ E := by
  have hAB : P ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    (le_inf hA hB).trans inf_normalizer_le_normalizer_inf
  apply commutator_join_left_le (sup_le hAP hBP) hCP hE
  · exact commutator_join_left_le hAP hBP hE
      ((commutator_mono le_rfl inf_le_left).trans hAA)
      ((commutator_mono le_rfl inf_le_right).trans hBB)
  · exact (le_inf
      (le_normalizer_iff_commutator_le_right.mp (hCP.trans hAB))
      (le_normalizer_iff_commutator_le_left.mp ((inf_le_left.trans hAP).trans hC))).trans htriple

private theorem elementary_quotient_of_three_factors
    (P E A B C : Subgroup G) [(E.subgroupOf P).Normal]
    (hAP : A ≤ P) (hBP : B ≤ P) (hCP : C ≤ P)
    (hprod : (P : Set G) = (A : Set G) * (B : Set G) * (C : Set G))
    (hAB : ⁅A, B⁆ ≤ E) (hAC : ⁅A, C⁆ ≤ E) (hBC : ⁅B, C⁆ ≤ E)
    (hsA : ∀ a ∈ A, a ^ 2 ∈ E) (hsB : ∀ b ∈ B, b ^ 2 ∈ E)
    (hsC : ∀ c ∈ C, c ^ 2 ∈ E) : IsElementaryAbelian 2 (P ⧸ E.subgroupOf P) := by
  let q := QuotientGroup.mk' (E.subgroupOf P)
  have hsq (v : P ⧸ E.subgroupOf P) : v ^ 2 = 1 := by
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf P) v
    have hp : (p : G) ∈ (A : Set G) * (B : Set G) * (C : Set G) := by
      rw [← hprod]
      exact p.property
    obtain ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, he⟩ := hp
    let aP : P := ⟨a, hAP ha⟩
    let bP : P := ⟨b, hBP hb⟩
    let cP : P := ⟨c, hCP hc⟩
    have he' : aP * bP * cP = p := Subtype.ext he
    have hqa : (q aP) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsA a ha)
    have hqb : (q bP) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsB b hb)
    have hqc : (q cP) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsC c hc)
    have commute_mod (x y : P) (hxy : ⁅(x : G), (y : G)⁆ ∈ E) :
        Commute (q x) (q y) := by
      change q x * q y = q y * q x
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hxy
    have hab := commute_mod aP bP (hAB (commutator_mem_commutator ha hb))
    have hac := commute_mod aP cP (hAC (commutator_mem_commutator ha hc))
    have hbc := commute_mod bP cP (hBC (commutator_mem_commutator hb hc))
    change (q p) ^ 2 = 1
    rw [← he', map_mul, map_mul, (hac.mul_left hbc).mul_pow, hab.mul_pow,
      hqa, hqb, hqc, mul_one, mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

namespace Hypothesis
variable [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

/-- The earlier Frattini conclusion bounds squares in every conjugate
of U by the original natural module V. -/
theorem conjugate_square_le (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (x : G) (hx : x ∈ D.L) :
    ∀ u ∈ conjugate D.U x, u ^ 2 ∈ D.V := by
  let : Fact (IsPGroup 2 D.U) := ⟨d.U_isPGroup hUT⟩
  rintro u ⟨a, ha, rfl⟩
  have ha2 : a ^ 2 ∈ D.V := d.setup.point_le (hf (mem_map_of_mem D.U.subtype
    (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨a, ha⟩ : D.U))))
  have hv := mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom ha2
  have he : D.V.map (MulAut.conj x⁻¹).toMonoidHom = D.V :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.V : Set G)).inv_mem (normalizes_of_span D d.span_eq hx))
  rw [he] at hv
  simpa only [map_pow] using hv

/-- The derived bounds in each conjugate have the same invariant target V. -/
theorem conjugate_derived_le (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (x : G) (hx : x ∈ D.L) :
    ⁅conjugate D.U x, conjugate D.U x⁆ ≤ D.V := by
  have hd := (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans d.setup.point_le
  have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hd
  rw [map_commutator] at hm
  have he : D.V.map (MulAut.conj x⁻¹).toMonoidHom = D.V :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.V : Set G)).inv_mem (normalizes_of_span D d.span_eq hx))
  exact hm.trans he.le

/-- S normalizes S₃ already from the earlier normalization of the three
U-conjugates. This gives the actual upper quotient before I-invariance. -/
theorem core_normalizes_third (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G)) :
    S D g h ≤ normalizer (S₃ D g h : Set G) := by
  have hW : S D g h ≤ normalizer (W D g h : Set G) :=
    (le_inf hU (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hWg : S D g h ≤ normalizer (conjugate (W D g h) g : Set G) := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact (le_inf hUg (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hWh : S D g h ≤ normalizer (conjugate (W D g h) h : Set G) := by
    rw [conjugate_W D g h h (hLI d.h_mem)]
    exact (le_inf hUh (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact normalized_sup
    (normalized_sup
      ((le_inf hW hWg).trans inf_normalizer_le_normalizer_inf)
      ((le_inf hW hWh).trans inf_normalizer_le_normalizer_inf))
    ((le_inf hWg hWh).trans inf_normalizer_le_normalizer_inf)

/-- The actual lower section is elementary abelian, independently of the
subsequent projective recognition and full I-invariance of S₃. -/
theorem lower_elementary (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    letI : ((S₂ D g h).subgroupOf (S₃ D g h)).Normal :=
      normal_subgroupOf_of_le_normalizer
        (((d.series_inclusions hUT hf hLI).2.2.trans (pCoreIn_le 2 (I D g h))).trans
          (le_normalizer_iff_commutator_le_left.mpr
            ((d.intersection hUT hf).2.2.2.1.trans (d.intersection hUT hf).1)))
    IsElementaryAbelian 2 (LowerQuotient D g h) := by
  let A := W D g h ⊓ conjugate (W D g h) g
  let B := W D g h ⊓ conjugate (W D g h) h
  let C := conjugate (W D g h) g ⊓ conjugate (W D g h) h
  have hVE := (d.intersection hUT hf).1
  have hEN : I D g h ≤ normalizer (S₂ D g h : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr ((d.intersection hUT hf).2.2.2.1.trans hVE)
  let : ((S₂ D g h).subgroupOf (S₃ D g h)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (((d.series_inclusions hUT hf hLI).2.2.trans (pCoreIn_le 2 (I D g h))).trans hEN)
  have hWg : conjugate (W D g h) g ≤ conjugate D.U g := map_mono inf_le_left
  have hWh : conjugate (W D g h) h ≤ conjugate D.U h := map_mono inf_le_left
  have hder : ⁅D.U, D.U⁆ ≤ D.V :=
    (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans d.setup.point_le
  have hsq : ∀ u ∈ D.U, u ^ 2 ∈ D.V := by
    simpa [conjugate] using conjugate_square_le d hUT hf 1 D.L.one_mem
  apply elementary_quotient_of_three_factors (S₃ D g h) (S₂ D g h) A B C
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) le_sup_right
    (d.S₃_product hUT hf hLI)
  · exact ((commutator_mono (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_left)).trans hder).trans hVE
  · exact ((commutator_mono (inf_le_right.trans hWg) (inf_le_left.trans hWg)).trans
      (conjugate_derived_le d hUT hf g d.g_mem)).trans hVE
  · exact ((commutator_mono (inf_le_right.trans hWh) (inf_le_right.trans hWh)).trans
      (conjugate_derived_le d hUT hf h d.h_mem)).trans hVE
  · exact fun a ha => hVE (hsq a ha.1.1)
  · exact fun b hb => hVE (hsq b hb.1.1)
  · exact fun c hc => hVE (conjugate_square_le d hUT hf g d.g_mem c (hWg hc.1))

/-- The elementary upper quotient, with precisely the normalization and
product conclusions supplied by the earlier structural branch. -/
theorem upper_elementary (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G)) :
    letI : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
    IsElementaryAbelian 2 (UpperQuotient D g h) := by
  let : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
    normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
  have hW : S D g h ≤ normalizer (W D g h : Set G) :=
    (le_inf hU (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hWg : S D g h ≤ normalizer (conjugate (W D g h) g : Set G) := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact (le_inf hUg (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hWh : S D g h ≤ normalizer (conjugate (W D g h) h : Set G) := by
    rw [conjugate_W D g h h (hLI d.h_mem)]
    exact (le_inf hUh (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hgS : conjugate (W D g h) g ≤ S D g h := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact inf_le_right
  have hhS : conjugate (W D g h) h ≤ S D g h := by
    rw [conjugate_W D g h h (hLI d.h_mem)]
    exact inf_le_right
  have hncomm (A B : Subgroup G) (hAS : A ≤ S D g h) (hBS : B ≤ S D g h)
      (hnA : S D g h ≤ normalizer (A : Set G))
      (hnB : S D g h ≤ normalizer (B : Set G)) : ⁅A, B⁆ ≤ A ⊓ B :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (hBS.trans hnA))
      (le_normalizer_iff_commutator_le_right.mp (hAS.trans hnB))
  have hVP := (d.series_inclusions hUT hf hLI).1.trans (d.series_inclusions hUT hf hLI).2.1
  have hsq : ∀ u ∈ D.U, u ^ 2 ∈ D.V := by
    simpa [conjugate] using conjugate_square_le d hUT hf 1 D.L.one_mem
  apply elementary_quotient_of_three_factors (S D g h) (S₃ D g h)
    (W D g h) (conjugate (W D g h) g) (conjugate (W D g h) h)
    inf_le_right hgS hhS hprod
  · exact (hncomm _ _ inf_le_right hgS hW hWg).trans (le_sup_left.trans le_sup_left)
  · exact (hncomm _ _ inf_le_right hhS hW hWh).trans (le_sup_right.trans le_sup_left)
  · exact (hncomm _ _ hgS hhS hWg hWh).trans le_sup_right
  · exact fun w hw => hVP (hsq w hw.1)
  · exact fun w hw => hVP (conjugate_square_le d hUT hf g d.g_mem w (map_mono inf_le_left hw))
  · exact fun w hw => hVP (conjugate_square_le d hUT hf h d.h_mem w (map_mono inf_le_left hw))

/-- The entire core acts trivially on the lower quotient. Each pair
intersection commutes modulo S₂ with all three generating W-groups. -/
theorem core_centralizes_lower (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h) :
    ⁅S D g h, S₃ D g h⁆ ≤ S₂ D g h := by
  let A := W D g h
  let B := conjugate (W D g h) g
  let C := conjugate (W D g h) h
  have hAS : A ≤ S D g h := inf_le_right
  have hBS : B ≤ S D g h := by
    dsimp only [B]
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact inf_le_right
  have hCS : C ≤ S D g h := by
    dsimp only [C]
    rw [conjugate_W D g h h (hLI d.h_mem)]
    exact inf_le_right
  have hA : S D g h ≤ normalizer (A : Set G) :=
    (le_inf hU (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hB : S D g h ≤ normalizer (B : Set G) := by
    dsimp only [B]
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact (le_inf hUg (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hC : S D g h ≤ normalizer (C : Set G) := by
    dsimp only [C]
    rw [conjugate_W D g h h (hLI d.h_mem)]
    exact (le_inf hUh (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hVE := (d.intersection hUT hf).1
  have hE : S D g h ≤ normalizer (S₂ D g h : Set G) :=
    (pCoreIn_le 2 (I D g h)).trans
      (le_normalizer_iff_commutator_le_left.mpr ((d.intersection hUT hf).2.2.2.1.trans hVE))
  have hAA : ⁅A, A⁆ ≤ S₂ D g h :=
    ((commutator_mono inf_le_left inf_le_left).trans
      (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf)).trans
        (d.setup.point_le.trans hVE)
  have hBB : ⁅B, B⁆ ≤ S₂ D g h :=
    ((commutator_mono (map_mono inf_le_left) (map_mono inf_le_left)).trans
      (conjugate_derived_le d hUT hf g d.g_mem)).trans hVE
  have hCC : ⁅C, C⁆ ≤ S₂ D g h :=
    ((commutator_mono (map_mono inf_le_left) (map_mono inf_le_left)).trans
      (conjugate_derived_le d hUT hf h d.h_mem)).trans hVE
  have he : (A ⊓ B) ⊓ C = S₂ D g h := (d.S₂_eq_triple_W hUT hf hLI).symm
  have hAB : ⁅S D g h, A ⊓ B⁆ ≤ S₂ D g h := by
    rw [hgen]
    exact commutator_pair_le hAS hBS hCS hA hB hC hE hAA hBB he.le
  have hAC : ⁅S D g h, A ⊓ C⁆ ≤ S₂ D g h := by
    have hg' : S D g h = (A ⊔ C) ⊔ B := hgen.trans (by dsimp [A, B, C]; ac_rfl)
    rw [hg']
    apply commutator_pair_le hAS hCS hBS hA hC hB hE hAA hCC
    simpa only [inf_assoc, inf_comm, inf_left_comm] using he.le
  have hBC : ⁅S D g h, B ⊓ C⁆ ≤ S₂ D g h := by
    have hg' : S D g h = (B ⊔ C) ⊔ A := hgen.trans (by dsimp [A, B, C]; ac_rfl)
    rw [hg']
    apply commutator_pair_le hBS hCS hAS hB hC hA hE hBB hCC
    simpa only [inf_assoc, inf_comm, inf_left_comm] using he.le
  rw [commutator_comm] at hAB hAC hBC ⊢
  exact commutator_join_left_le
    (sup_le (inf_le_left.trans hAS) (inf_le_left.trans hAS))
    (inf_le_left.trans hBS) hE
    (commutator_join_left_le (inf_le_left.trans hAS) (inf_le_left.trans hAS) hE hAB hAC)
    hBC

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
