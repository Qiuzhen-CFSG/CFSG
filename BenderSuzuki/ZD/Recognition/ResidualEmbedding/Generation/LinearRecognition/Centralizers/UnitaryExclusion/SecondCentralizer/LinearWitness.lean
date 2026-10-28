module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Recognizing the second centralizer from one additional linear subgroup

For a cyclic subgroup `B`, choose a generator `b`. The distinguished
centralizer of `B` is exactly `centralizerClosure Z b`, so the supplied
Lemma 12.3 alternative gives its unitary cover as soon as it is larger than
`L`. Its field exponent is forced by the cardinality of the same `A`.

One subgroup `I ≃ PSL₂(q)` centralizing `z*u` and `B`, with `z ∈ I`, suffices
for strict containment. Conjugacy invariance of `Z` and simplicity of `I`
give distinguished generation. If `I ≤ L`, equal orders give `I = L`,
forcing the nonidentity element `z` into the trivial center of `L`.
Thus `I` supplies a distinguished element of `C_G(B)` outside `L`.
This uses Lemma 12.3 in place of the source's conjugate count.

The final conditional assembly still requires the actual torus, this linear
subgroup, and the actual PSL₂ model of the `u`-fixed subgroup. It then proves
the cover, intersection, normalization and noninner clauses of
`SecondCentralizerData`. Noninnerness follows because a hypothetical inner
representative belongs to the fixed group `L`, centralizes `L`, and is
therefore trivial, contradicting proper containment. Construction of the
remaining geometric inputs belongs to the unconditional Lemma 13.2 task.

Source: GLS, Volume 4, Chapter 2, Lemmas 12.3 and 13.2; Chapter 4,
Lemmas 3.4(c) and 3.6(c,d). The latter supplies the additional linear group.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
open _root_.BenderSuzuki.MatrixGroups
universe w
variable {G : Type w} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

omit [Finite G] in
private theorem distinguishedCentralizer_zpowers (b : G) :
    distinguishedCentralizer Z (zpowers b) = centralizerClosure Z b := by
  simp only [distinguishedCentralizer, zpowers_eq_closure, centralizer_closure,
    centralizerClosure]

/-- The existing element-centralizer alternative also recognizes the
distinguished centralizer of a nontrivial cyclic subgroup. -/
public theorem second_cover_of_cyclic_escape
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (B : Subgroup G) (hcyclic : IsCyclic B) (hB : B ≠ ⊥)
    (hBL : B ≤ centralizer (residualGenerated M z t : Set G))
    (hescape : ∃ x ∈ Z, x ∈ centralizer (B : Set G) ∧
      x ∉ residualGenerated M z t) :
    residualGenerated M z t < distinguishedCentralizer Z B ∧
      IsUnitaryCentralizerCoverAt n (distinguishedCentralizer Z B) := by
  obtain ⟨b, hb⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp hcyclic
  have hbB : b ∈ B := hb ▸ mem_zpowers b
  have hb1 : b ≠ 1 := by
    intro he
    subst b
    exact hB (by simpa using hb.symm)
  have hclosure : distinguishedCentralizer Z B = centralizerClosure Z b := by
    rw [← hb, distinguishedCentralizer_zpowers]
  rcases hlocal.centralizing_extension b (hBL hbB) hb1 with he | ⟨k, hk, hc, e, hlt, hcov⟩
  · obtain ⟨x, hxZ, hxB, hxL⟩ := hescape
    have hx : x ∈ distinguishedCentralizer Z B := subset_closure ⟨hxZ, hxB⟩
    exact False.elim (hxL (by simpa only [hclosure, he] using hx))
  · have hkn : k = n := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (hc.symm.trans hcard)
    subst k
    refine ⟨hclosure.symm ▸ hlt, ?_⟩
    have hcongr (F H : Subgroup G) (he : F = H) :
        IsUnitaryCentralizerCoverAt n F ↔ IsUnitaryCentralizerCoverAt n H := by
      subst H
      rfl
    exact (hcongr _ _ hclosure).mpr hcov

omit [Finite G] in
private theorem linear_center_eq_one
    (L : Subgroup G) (eL : L ≃* PSL2BinaryMatrixGroup n)
    {a : G} (ha : a ∈ L) (hac : a ∈ centralizer (L : Set G)) : a = 1 := by
  have hacL : (⟨a, ha⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_iff.mp hac x x.property)
  have hea : eL ⟨a, ha⟩ ∈ center (PSL2BinaryMatrixGroup n) :=
    ((Subgroup.centerCongr eL) ⟨_, hacL⟩).property
  have he1 : eL ⟨a, ha⟩ = 1 := by
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hea
  exact congrArg Subtype.val (eL.injective (he1.trans eL.map_one.symm))

private theorem linear_subgroup_not_le_of_coset_centralizes
    (L I : Subgroup G) (eL : L ≃* PSL2BinaryMatrixGroup n)
    (eI : I ≃* PSL2BinaryMatrixGroup n)
    (hu : u ∈ centralizer (L : Set G)) {a : G} (ha : a ∈ L) (ha1 : a ≠ 1)
    (hI : I ≤ centralizer ({a * u} : Set G)) : ¬ I ≤ L := by
  intro hIL
  have heq : I = L := eq_of_le_of_card_ge hIL
    ((Nat.card_congr eL.toEquiv).trans (Nat.card_congr eI.toEquiv).symm).le
  have hv : a * u ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hI (heq.symm ▸ hx))
  have hac : a ∈ centralizer (L : Set G) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (L : Set G)).mul_mem hv ((centralizer (L : Set G)).inv_mem hu)
  exact ha1 (linear_center_eq_one L eL ha hac)

/-- One additional linear subgroup suffices for recognition: its centralizing
the nontrivial coset element `a*u` prevents it from being the original `L`.
Distinguished generation supplies an element outside `L` centralizing `B`.
This replaces the conjugate count in Lemma 13.2 by the already supplied
Lemma 12.3 alternative, with exactly the same field exponent. -/
public theorem second_cover_of_linear_witness
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (B : Subgroup G) (hcyclic : IsCyclic B) (hB : B ≠ ⊥)
    (hBL : B ≤ centralizer (residualGenerated M z t : Set G))
    (hu : u ∈ centralizer (residualGenerated M z t : Set G))
    {a : G} (ha : a ∈ residualGenerated M z t) (ha1 : a ≠ 1)
    (I : Subgroup G) (eI : I ≃* PSL2BinaryMatrixGroup n)
    (hIgen : closure (Z ∩ (I : Set G)) = I)
    (hIB : I ≤ centralizer (B : Set G))
    (hIv : I ≤ centralizer ({a * u} : Set G)) :
    residualGenerated M z t < distinguishedCentralizer Z B ∧
      IsUnitaryCentralizerCoverAt n (distinguishedCentralizer Z B) := by
  apply second_cover_of_cyclic_escape hlocal hcard B hcyclic hB hBL
  by_contra hescape
  have hIL : I ≤ residualGenerated M z t := by
    rw [← hIgen, closure_le]
    intro x hx
    by_contra hxL
    exact hescape ⟨x, hx.1, hIB hx.2, hxL⟩
  exact linear_subgroup_not_le_of_coset_centralizes _ I eL eI hu ha ha1 hIv hIL

omit [Finite G] in
private theorem noninner_of_proper_linear_fixed
    (L F : Subgroup G) (eL : L ≃* PSL2BinaryMatrixGroup n)
    (hlt : L < F) (hfixed : F ⊓ centralizer ({u} : Set G) = L) :
    ¬ ∃ a ∈ F, ∀ x ∈ F, MulAut.conj u x = MulAut.conj a x := by
  rintro ⟨a, haF, hi⟩
  have hua : u * a * u⁻¹ = a := by
    simpa only [MulAut.conj_apply, mul_inv_cancel_right] using hi a haF
  have haC : a ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hua).symm
  have haL : a ∈ L := hfixed ▸ (show a ∈ F ⊓ centralizer ({u} : Set G) from ⟨haF, haC⟩)
  have haCL : a ∈ centralizer (L : Set G) := by
    intro x hx
    have hxC := (show x ∈ F ⊓ centralizer ({u} : Set G) from hfixed.symm ▸ hx).2
    have hux : MulAut.conj u x = x := by
      rw [MulAut.conj_apply, ← mem_centralizer_singleton_iff.mp hxC, mul_inv_cancel_right]
    have hax : a * x * a⁻¹ = x := (hi x (hlt.le hx)).symm.trans hux
    exact (mul_inv_eq_iff_eq_mul.mp hax).symm
  have ha1 := linear_center_eq_one L eL haL haCL
  subst a
  apply hlt.not_ge
  intro x hx
  rw [← hfixed]
  refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
  have hux : u * x * u⁻¹ = x := by simpa only [MulAut.conj_apply, one_mul, inv_one, mul_one] using hi x hx
  exact (mul_inv_eq_iff_eq_mul.mp hux).symm

private theorem linear_distinguished_generation
    (h : IsProductDisconnected Z M) (hz : z ∈ Z) (hn : 2 ≤ n)
    (I : Subgroup G) (eI : I ≃* PSL2BinaryMatrixGroup n) (hzI : z ∈ I) :
    closure (Z ∩ (I : Set G)) = I := by
  let F := closure (Z ∩ (I : Set G))
  have hFI : F ≤ I := (closure_le _).mpr (fun _ hx => hx.2)
  have hFN : (F.subgroupOf I).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    apply le_normalizer_closure_iff.mpr
    intro g hg x hx
    exact subset_closure ⟨h.invariant g x hx.1,
      I.mul_mem (I.mul_mem hg hx.2) (I.inv_mem hg)⟩
  let : IsSimpleGroup I :=
    (show IsSimpleBenderGroup I from .isPSL2 ⟨n, hn, ⟨eI⟩⟩).isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F.subgroupOf I) hFN with hb | ht
  · have hzF : (⟨z, hzI⟩ : I) ∈ F.subgroupOf I := subset_closure ⟨hz, hzI⟩
    rw [hb, mem_bot] at hzF
    exact False.elim ((h.involutions z hz).ne_one (congrArg Subtype.val hzF))
  · apply le_antisymm hFI
    intro x hx
    have hxF : (⟨x, hx⟩ : I) ∈ F.subgroupOf I := ht ▸ mem_top _
    exact hxF

/-- Containment of a distinguished involution already gives the generation
premise for the additional linear subgroup. This form exposes the recognized
second cover before its involution-fixed subgroup has been identified. -/
public theorem second_cover_of_distinguished_linear_witness
    (h : IsProductDisconnected Z M) (hz : z ∈ Z)
    (hlocal : ResidualCentralizerLocalData Z M z t) (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (B : Subgroup G) (hcyclic : IsCyclic B) (hB : B ≠ ⊥)
    (hBL : B ≤ centralizer (residualGenerated M z t : Set G))
    (hu : u ∈ centralizer (residualGenerated M z t : Set G))
    (I : Subgroup G) (eI : I ≃* PSL2BinaryMatrixGroup n) (hzI : z ∈ I)
    (hIB : I ≤ centralizer (B : Set G))
    (hIv : I ≤ centralizer ({z * u} : Set G)) :
    residualGenerated M z t < distinguishedCentralizer Z B ∧
      IsUnitaryCentralizerCoverAt n (distinguishedCentralizer Z B) := by
  have hzL : z ∈ residualGenerated M z t :=
    (show zpowers z ≤ residualGenerated M z t from le_sup_left.trans le_sup_left) (mem_zpowers z)
  exact second_cover_of_linear_witness hlocal hcard eL B hcyclic hB hBL hu hzL
    (h.involutions z hz).ne_one I eI (linear_distinguished_generation h hz hn I eI hzI) hIB hIv

/-- Conditional assembly of Lemma 13.2 from its remaining geometry. The
independent model work must construct the ambient torus, the linear subgroup
centralizing `z*u`, and the actual fixed-subgroup isomorphism. The cover,
intersection, normalization, and noninner action are proved here; none are
record projections or additional assumptions of this assembly. -/
public theorem secondCentralizerData_of_linear_and_fixed_models
    (h : IsProductDisconnected Z M) (hz : z ∈ Z)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (B : Subgroup G) (hcyclic : IsCyclic B) (hB : B ≠ ⊥)
    (hBcard : Nat.card B = 2 ^ n + 1 ∨ Nat.card B = (2 ^ n + 1) / 3)
    (hBlocal : B ≤ centralizerClosure Z u)
    (hBpair : B ≤ residualPairStabilizer M t)
    (hBL : B ≤ centralizer (residualGenerated M z t : Set G))
    (hCB : centralizerClosure Z u ⊓ centralizer (B : Set G) =
      residualGenerated M z t ⊔ B)
    (I : Subgroup G) (eI : I ≃* PSL2BinaryMatrixGroup n)
    (hzI : z ∈ I)
    (hIB : I ≤ centralizer (B : Set G))
    (hIv : I ≤ centralizer ({z * u} : Set G))
    (efixed : (distinguishedCentralizer Z B ⊓ centralizer ({u} : Set G) : Subgroup G) ≃*
      PSL2BinaryMatrixGroup n) :
    Nonempty (SecondCentralizerData Z M z t u n) := by
  have hLlocal := (hunitary u huD hu).1.le
  have huL : u ∈ centralizer (residualGenerated M z t : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u (hLlocal hx))
  obtain ⟨hlt, hcover⟩ := second_cover_of_distinguished_linear_witness h hz hlocal hn hcard
    eL B hcyclic hB hBL huL I eI hzI hIB hIv
  have hLF : residualGenerated M z t ≤ distinguishedCentralizer Z B ⊓ centralizer ({u} : Set G) :=
    le_inf hlt.le (hLlocal.trans (centralizerClosure_le Z u))
  have hfixed : distinguishedCentralizer Z B ⊓ centralizer ({u} : Set G) =
      residualGenerated M z t := (eq_of_le_of_card_ge hLF
    ((Nat.card_congr efixed.toEquiv).trans (Nat.card_congr eL.toEquiv).symm).le).symm
  have hnorm : centralizer (B : Set G) ≤ normalizer (distinguishedCentralizer Z B : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro g hg x hx
    exact subset_closure ⟨h.invariant g x hx.1,
      (centralizer (B : Set G)).mul_mem
        ((centralizer (B : Set G)).mul_mem hg hx.2)
        ((centralizer (B : Set G)).inv_mem hg)⟩
  refine ⟨{
    torus := B
    cyclic := hcyclic
    card_torus := hBcard
    torus_le_local := hBlocal
    torus_le_pair := hBpair
    torus_centralizes := hBL
    local_torus_centralizer := hCB
    second_cover := hcover
    intersection := ?_
    fixed := hfixed
    normalizes := ?_
    noninner := noninner_of_proper_linear_fixed _ _ eL hlt hfixed }⟩
  · apply le_antisymm _ (le_inf hlt.le hLlocal)
    calc
      distinguishedCentralizer Z B ⊓ centralizerClosure Z u ≤
          distinguishedCentralizer Z B ⊓ centralizer ({u} : Set G) :=
        inf_le_inf_left _ (centralizerClosure_le Z u)
      _ = residualGenerated M z t := hfixed
  · apply hnorm
    intro b hb
    exact mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u (hBlocal hb))

end BenderSuzuki.ZD.UnitaryExclusion
