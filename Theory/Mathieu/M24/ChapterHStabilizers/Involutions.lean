module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.CentralInvolutions
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Involution classes and two-centrality in the native Mathieu group

The two certified involution classes have respectively an octad and no fixed
points. Sylow conjugacy transports the checked center calculation of the native
order-1024 subgroup: every Sylow-central involution has a nonempty fixed set.
Existence of a central involution in a nontrivial finite two-group then identifies
precisely the octad-fixing class as the two-central class.

All conjugators act in the literal Witt-design carrier. No centralizer order or
abstract group identification is assumed.

Source: Aschbacher–Smith H.14.4(1), printed pp.397–398 (PDF pp.408–409).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24InvolutionCentralizers
open scoped Pointwise
namespace Sporadic.Mathieu.M24ChapterHStabilizers

noncomputable def fixedPoints (x : M24) : Finset (Fin 24) :=
  Finset.univ.filter (fun a => x • a = a)

@[simp] theorem mem_fixedPoints (x : M24) (a : Fin 24) :
    a ∈ fixedPoints x ↔ x • a = a := by simp [fixedPoints]

theorem fixedPoints_conj (g x : M24) :
    fixedPoints (MulAut.conj g x) = g • fixedPoints x := by
  ext a
  rw [mem_fixedPoints, Finset.mem_smul_finset]
  constructor
  · intro ha
    refine ⟨g⁻¹ • a, (mem_fixedPoints _ _).mpr ?_, smul_inv_smul _ _⟩
    have he := congrArg (fun a : Fin 24 => g⁻¹ • a) ha
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using he
  · rintro ⟨b, hb, rfl⟩
    rw [mem_fixedPoints] at hb
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hb]

theorem fixedPoints_card_eq_of_isConj {x y : M24} (h : IsConj x y) :
    (fixedPoints x).card = (fixedPoints y).card := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← show MulAut.conj g x = y from hg, fixedPoints_conj, Finset.card_smul_finset]

private theorem fixedPoints_2A : fixedPoints involution2A = m24BlockAt 0 := by
  decide +kernel

private theorem fixedPoints_2B : fixedPoints involution2B = ∅ := by
  decide +kernel

theorem classes_disjoint : ¬ IsConj involution2A involution2B := by
  intro h
  have hc := fixedPoints_card_eq_of_isConj h
  rw [fixedPoints_2A, fixedPoints_2B, Finset.card_empty] at hc
  have h8 : (m24BlockAt 0).card = 8 := by decide +kernel
  omega

theorem class2A_fixed_octad {x : M24} (hx : IsConj involution2A x) :
    fixedPoints x ∈ m24Blocks := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  rw [← show MulAut.conj g involution2A = x from hg, fixedPoints_conj, fixedPoints_2A]
  have hb : m24BlockAt 0 ∈ m24Blocks := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have h := (mem_M24_iff g.val).mp g.property
  change g.val • m24BlockAt 0 ∈ (m24Blocks : Set (Finset (Fin 24)))
  rw [← h]
  exact Set.smul_mem_smul_set hb

theorem class2B_fixed_empty {x : M24} (hx : IsConj involution2B x) :
    fixedPoints x = ∅ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  rw [← show MulAut.conj g involution2B = x from hg, fixedPoints_conj, fixedPoints_2B]
  rfl

private noncomputable abbrev markedSylow : Sylow 2 M24 :=
  (IsPGroup.of_card (p := 2) (n := 10) SylowNormalizer.candidate_card).toSylow (by
    have h := SylowNormalizer.candidate.card_mul_index
    rw [SylowNormalizer.candidate_card, m24_order] at h
    have hi : SylowNormalizer.candidate.index = 239085 := by omega
    rw [hi]
    decide)

private theorem sylowCentral_fixed_nonempty {x : M24} (hx : IsSylowCentralInvolution x) :
    (fixedPoints x).Nonempty := by
  obtain ⟨hx2, S, hxS, hSC⟩ := hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 S markedSylow
  have hmap : S.toSubgroup.map (MulAut.conj g).toMonoidHom =
      SylowNormalizer.candidate := congrArg Sylow.toSubgroup hg
  let y := MulAut.conj g x
  have hy : y ∈ SylowNormalizer.candidate := by
    rw [← hmap]
    exact ⟨x, hxS, rfl⟩
  have hyC : (⟨y, hy⟩ : SylowNormalizer.candidate) ∈ center SylowNormalizer.candidate := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    obtain ⟨t, ht, hts⟩ := (show s.val ∈ S.toSubgroup.map (MulAut.conj g).toMonoidHom by
      rw [hmap]; exact s.property)
    change (MulAut.conj g) t = s.val at hts
    change s.val * y = y * s.val
    have he := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hSC ht))
    simpa only [map_mul, hts] using he
  have hy2 : orderOf (⟨y,hy⟩ : SylowNormalizer.candidate) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans ((MulEquiv.orderOf_eq _ _).trans hx2)
  have hfixed : fixedPoints y = SylowNormalizer.centralOctad.val := by
    ext a
    exact (mem_fixedPoints _ _).trans
      (SylowNormalizer.central_involution_fixed_iff ⟨y, hy⟩ hyC hy2 a)
  have hcard : (fixedPoints y).card = 8 := by
    rw [hfixed]
    exact m24Blocks_card _ SylowNormalizer.centralOctad.property
  rw [show fixedPoints y = g • fixedPoints x from fixedPoints_conj g x,
    Finset.card_smul_finset] at hcard
  exact Finset.card_pos.mp (by omega)

private theorem exists_sylowCentral : ∃ x : M24, IsSylowCentralInvolution x := by
  let S := markedSylow
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card SylowNormalizer.candidate
    rw [SylowNormalizer.candidate_card]
    decide)
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hc⟩ := (S.isPGroup'.to_subgroup (center S)).nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2
    (hc.symm ▸ dvd_pow_self 2 (Nat.ne_of_gt hn))
  refine ⟨z.val.val, ?_, S, z.val.property, ?_⟩
  · exact (Subgroup.orderOf_coe z.val).trans ((Subgroup.orderOf_coe z).trans hz)
  · intro s hs
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨s, hs⟩)

theorem sylowCentral_class2A {x : M24} (hx : IsSylowCentralInvolution x) :
    IsConj involution2A x := by
  rcases involution_classes x hx.1 with h | h
  · exact h
  · have he := class2B_fixed_empty h
    have hn := sylowCentral_fixed_nonempty hx
    rw [he] at hn
    exact (Finset.not_nonempty_empty hn).elim

theorem involution2A_sylowCentral : IsSylowCentralInvolution involution2A := by
  obtain ⟨x, hx⟩ := exists_sylowCentral
  obtain ⟨g, hg⟩ := isConj_iff.mp (sylowCentral_class2A hx).symm
  exact (show MulAut.conj g x = involution2A from hg) ▸ hx.map (MulAut.conj g)

theorem sylowCentral_iff_class2A (x : M24) :
    IsSylowCentralInvolution x ↔ IsConj involution2A x := by
  refine ⟨sylowCentral_class2A, ?_⟩
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact (show MulAut.conj g involution2A = x from hg) ▸ involution2A_sylowCentral.map (MulAut.conj g)

theorem not_sylowCentral_iff_class2B (x : M24) (hx : orderOf x = 2) :
    ¬ IsSylowCentralInvolution x ↔ IsConj involution2B x := by
  rw [sylowCentral_iff_class2A]
  constructor
  · intro hn
    exact (involution_classes x hx).resolve_left hn
  · intro hB hA
    exact classes_disjoint (hA.trans hB.symm)

theorem sylowCentral_fixed_octad {x : M24} (hx : IsSylowCentralInvolution x) :
    fixedPoints x ∈ m24Blocks := class2A_fixed_octad (sylowCentral_class2A hx)

theorem noncentral_fixed_empty {x : M24} (hx : orderOf x = 2)
    (hn : ¬ IsSylowCentralInvolution x) : fixedPoints x = ∅ :=
  class2B_fixed_empty ((not_sylowCentral_iff_class2B x hx).mp hn)

end Sporadic.Mathieu.M24ChapterHStabilizers
