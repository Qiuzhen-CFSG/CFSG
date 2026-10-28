module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local

/-!
# Choosing the Sylow subgroup without changing the marked involutions

After |R| = 2, enlarge N_T(R) to a Sylow P of N_H(R), then put P inside
an H-conjugate S of T. The earlier 16.4.2(1) and 16.4.4(1) results show
P ∩ C_G(L) = ⟨z⟩. The transported central involution belongs to this
intersection, so it equals z. Thus S retains the whole intersection setup,
including the original z, L, R and conjugator g, and N_S(R) is Sylow in
N_H(R). In particular no new assumption on the original T is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1184, the choice preceding E = ⟨r,z⟩.
All conjugations here are left conjugations.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Replace T, keeping z, L, R, g and hence every marked element of R fixed. -/
theorem exists_normalizer_sylow (h : IntersectionSetup T z L g R)
    (hR : Nat.card R = 2) :
    ∃ S : Sylow 2 G, IntersectionSetup S z L g R ∧
      SylowIn ((S : Subgroup G) ⊓ normalizer (R : Set G))
        (normalizer (L : Set G) ⊓ normalizer (R : Set G)) ∧
      ∃ a ∈ normalizer (L : Set G),
        (S : Subgroup G) = (T : Subgroup G).conjBy a ∧ MulAut.conj a z = z := by
  let H := normalizer (L : Set G)
  let N := H ⊓ normalizer (R : Set G)
  let A := (T : Subgroup G) ⊓ normalizer (R : Set G)
  have hAN : A ≤ N := le_inf (inf_le_left.trans h.sylow_normalizes) inf_le_right
  have hpA : IsPGroup 2 A :=
    T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)
  obtain ⟨P₀, hP₀⟩ := (hpA.of_equiv (subgroupOfEquivOfLe hAN).symm).exists_le_sylow
  let P := (P₀ : Subgroup N).map N.subtype
  have hP : SylowIn P N := ⟨P₀, rfl⟩
  have hAP : A ≤ P := by
    rw [← map_subgroupOf_eq_of_le hAN]
    exact map_mono hP₀
  have hTH : SylowIn (T : Subgroup G) H := by
    simpa only [h.normalizers_eq] using h.toStandardSetup.sylowIn_normalizer
  obtain ⟨a, ha, hPS⟩ := hTH.exists_le_conjugate hP.isPGroup (hP.le.trans inf_le_left)
  let S : Sylow 2 G := T.mapSurjective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).surjective
  have hS : (S : Subgroup G) = (T : Subgroup G).conjBy a := rfl
  have hSH : (S : Subgroup G) ≤ H := by
    rintro x ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp (H.le_normalizer ha) y).mp (h.sylow_normalizes hy)
  have hRA : R ≤ A := le_inf h.le_sylow R.le_normalizer
  have hRS : R ≤ (S : Subgroup G) := hRA.trans (hAP.trans hPS)
  have hSP : (S : Subgroup G) ⊓ normalizer (R : Set G) = P :=
    hP.maximal (S.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _))
      (le_inf (inf_le_left.trans hSH) inf_le_right)
      (le_inf hPS (hP.le.trans inf_le_right))
  have hzC : z ∈ centralizer (R : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hx))
  have hzA : z ∈ A := ⟨h.mem_sylow, centralizer_le_normalizer _ hzC⟩
  have hzP : zpowers z ≤ P := zpowers_le.mpr (hAP hzA)
  have hzK : zpowers z ≤ centralizer (L : Set G) :=
    zpowers_le.mpr h.toStandardSetup.z_mem_commutingSylow.2
  have hZ : commutingSylow T L ⊓ normalizer (R : Set G) = zpowers z :=
    h.normalizer_structure.1.trans (h.centralizer_eq_zpowers_of_card_two hR).1
  have hZs : SylowIn (zpowers z) (centralizer (L : Set G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)) := by
    rw [← hZ]
    exact h.normalizer_structure.2.2.1
  have hPK : P ⊓ centralizer (L : Set G) = zpowers z := by
    apply hZs.maximal
      (hP.isPGroup.of_injective (inclusion inf_le_left) (inclusion_injective _))
    · exact le_inf inf_le_right
        (inf_le_left.trans ((hP.le.trans inf_le_right).trans (h.normalizer_le h.ne_bot le_rfl)))
    · exact le_inf hzP hzK
  have hazS : MulAut.conj a z ∈ S := ⟨z, h.mem_sylow, rfl⟩
  have hazC : MulAut.conj a z ∈ centralizer (S : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    have hh := mem_centralizer_singleton_iff.mp (h.sylow_centralizes hy)
    change MulAut.conj a y * MulAut.conj a z = MulAut.conj a z * MulAut.conj a y
    simpa only [map_mul] using congrArg (MulAut.conj a) hh
  have hazN : MulAut.conj a z ∈ normalizer (R : Set G) :=
    centralizer_le_normalizer _ (centralizer_le hRS hazC)
  have hazP : MulAut.conj a z ∈ P := hSP ▸ (show MulAut.conj a z ∈
      (S : Subgroup G) ⊓ normalizer (R : Set G) from ⟨hazS, hazN⟩)
  have hazK : MulAut.conj a z ∈ centralizer (L : Set G) := by
    have haK : a ∈ normalizer (centralizer (L : Set G) : Set G) := by
      rwa [h.normalizers_eq]
    exact (mem_normalizer_iff.mp haK z).mp h.toStandardSetup.z_mem_commutingSylow.2
  have hazZ : MulAut.conj a z ∈ zpowers z :=
    hPK ▸ (show MulAut.conj a z ∈ P ⊓ centralizer (L : Set G) from ⟨hazP, hazK⟩)
  have haz : MulAut.conj a z = z := by
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hazZ
    simp only [Finset.mem_image, Finset.mem_range] at hazZ
    obtain ⟨n, hn, he⟩ := hazZ
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · have hz1 : z = 1 := (MulAut.conj a).injective (by simpa using he.symm)
      have hn := h.involution
      simp [hz1] at hn
    · simpa using he.symm
  have hnew : IntersectionSetup S z L g R := by
    refine ⟨⟨⟨h.involution, haz ▸ hazS, ?_, h.component⟩, hSH, h.tight,
      h.normalizers_eq⟩, h.mem_delta, h.sylow, hRS⟩
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    rw [← haz]
    exact hazC x hx
  refine ⟨S, hnew, ?_, a, ha, hS, haz⟩
  rw [hSP]
  exact hP

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
