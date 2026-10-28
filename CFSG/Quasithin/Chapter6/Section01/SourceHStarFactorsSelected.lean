module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarFactorsResidual

/-!
# The selected factor product containing the original H-star residual

Inside the literal Thompson image, retain a direct factor exactly when some
ambient conjugate of the original residual has nontrivial projection to it.
Equivalently, the ambient normal closure is not contained in the other factor.
This explicit support product is normal because ambient conjugation permutes
the two factors, and it contains the original residual image.

That image is nontrivial: if it centralized the enlarged omega orbit, the
Sylow supplement `H = O²(H)T` would make all of `H` centralize the original
omega-center. Thus the selected product is one factor or the full pair, with
no nontrivial-image premise added to the original source hypotheses.

Source: Aschbacher--Smith, 6.1.5, printed pp.667--668.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.ThompsonImage

/-- Retain precisely the factors with nontrivial projection from `N`. -/
@[expose] def pairSupport {D : Type*} [Group D] (A B N : Subgroup D) : Subgroup D := by
  classical
  exact (if N ≤ B then ⊥ else A) ⊔ (if N ≤ A then ⊥ else B)

private theorem pairSupport_contains {D : Type*} [Group D]
    (A B N : Subgroup D) (hd : Disjoint A B) (hN : N ≤ A ⊔ B) :
    N ≤ pairSupport A B N := by
  classical
  unfold pairSupport
  split_ifs with hB hA hA
  · simpa only [sup_bot_eq] using (le_inf hA hB).trans hd.eq_bot.le
  · simpa only [bot_sup_eq] using hB
  · simpa only [sup_bot_eq] using hA
  · exact hN

private theorem normal_of_normal_subgroup_distinguishes {D : Type*} [Group D]
    (A B N : Subgroup D) [N.Normal]
    (hp : ∀ x : D,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A))
    (hNA : N ≤ A) (hNB : ¬ N ≤ B) : A.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro x _
  rcases hp x with hx | hx
  · exact mem_normalizer_iff_map_conj_eq.mpr hx.1
  · exfalso
    apply hNB
    have hn : N.map (MulAut.conj x).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (show x ∈ normalizer (N : Set D) by
        rw [normalizer_eq_top]; trivial)
    exact hn.symm.le.trans ((map_mono hNA).trans hx.1.le)

private theorem pairSupport_normal {D : Type*} [Group D]
    (A B J N : Subgroup D) [J.Normal] [N.Normal] (hs : A ⊔ B = J)
    (hp : ∀ x : D,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A)) :
    (pairSupport A B N).Normal := by
  classical
  unfold pairSupport
  split_ifs with hB hA hA
  · simpa only [sup_bot_eq] using (inferInstance : (⊥ : Subgroup D).Normal)
  · simpa only [bot_sup_eq] using
      normal_of_normal_subgroup_distinguishes B A N (fun x => (hp x).imp And.symm And.symm) hB hA
  · simpa only [sup_bot_eq] using normal_of_normal_subgroup_distinguishes A B N hp hA hB
  · rw [hs]
    infer_instance

/-- The selected product is normal and contains the original subgroup and
 all its ambient conjugates. Its definition retains precisely nonzero projections. -/
theorem selected_pair {D : Type*} [Group D]
    (A B J K : Subgroup D) [J.Normal] (hs : A ⊔ B = J) (hd : Disjoint A B)
    (hK : K ≤ J)
    (hp : ∀ x : D,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A)) :
    let N := normalClosure (K : Set D)
    (pairSupport A B N).Normal ∧ K ≤ pairSupport A B N ∧ pairSupport A B N ≤ J := by
  let N := normalClosure (K : Set D)
  have hNJ : N ≤ J := normalClosure_le_normal hK
  have hcontain : N ≤ pairSupport A B N := pairSupport_contains A B N hd (hNJ.trans hs.symm.le)
  refine ⟨pairSupport_normal A B J N hs hp, le_normalClosure.trans hcontain, ?_⟩
  classical
  unfold pairSupport
  apply sup_le
  · split_ifs
    · exact bot_le
    · exact le_sup_left.trans hs.le
  · split_ifs
    · exact bot_le
    · exact le_sup_right.trans hs.le

end CFSG.Quasithin.Chapter6.Source.ThompsonImage

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- Noncentrality of `H` on the original omega-center survives on its
 two-residual image in the enlarged centralizer quotient. -/
theorem hstar_residual_image_ne_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    (pResidual 2 H).map (q.comp (inclusion hHX)) ≠ ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := (conjugateSpanBy Z X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let f := inclusion hHX
  let S := T.subtype hH.1.1.2
  change (pResidual 2 H).map (q.comp f) ≠ ⊥
  intro hb
  have hker := (map_eq_bot_iff (pResidual 2 H)).mp hb
  have hcent : (⊤ : Subgroup H) ≤ centralizer (Z.subgroupOf H : Set H) := by
    rw [← pResidual_sup_sylow_eq_top S]
    apply sup_le
    · intro k hk z hz
      have hc : f k ∈ C := (QuotientGroup.eq_one_iff _).mp (hker hk)
      have hzU : f z ∈ U := le_conjugateSpanBy _ _ hz
      apply inclusion_injective hHX
      simpa only [map_mul] using hc (f z) hzU
    · intro t ht z hz
      exact Subtype.ext (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  apply hZH
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz k hk
  have hzH : z ∈ H := hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact (congrArg H.subtype (hcent (mem_top (⟨k,hk⟩ : H)) ⟨z,hzH⟩ hz)).symm

/-- The selected source product is exactly one factor or the whole pair,
 is normal in `X*`, and contains the original residual image. -/
theorem hstar_overgroup_selected_factor_product
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    let K := (pResidual 2 H).map (q.comp (inclusion hHX))
    ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype),
      let A := d.first.map J.subtype
      let B := d.second.map J.subtype
      let L₀ := ThompsonImage.pairSupport A B (normalClosure (K : Set (X ⧸ C)))
      L₀.Normal ∧ K ≤ L₀ ∧ L₀ ≤ J ∧ (L₀ = A ∨ L₀ = B ∨ L₀ = J) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  let K := (pResidual 2 H).map (q.comp (inclusion hHX))
  let : J.Normal := ThompsonImage.normal U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hKJ : K ≤ J := h.hstar_residual_image_le_overgroup_thompson hout hH hZH hHX hX
  have hKne : K ≠ ⊥ := h.hstar_residual_image_ne_bot hH hZH hHX hX
  change ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype), _
  intro d
  let A := d.first.map J.subtype
  let B := d.second.map J.subtype
  let N := normalClosure (K : Set (X ⧸ C))
  have hs : A ⊔ B = J := by
    rw [← Subgroup.map_sup, d.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  have hd : Disjoint A B := disjoint_map J.subtype_injective d.product.disjoint
  have hmap (F : Subgroup J) (x : X ⧸ C) :
      (F.map (MulAut.conjNormal x).toMonoidHom).map J.subtype =
        (F.map J.subtype).map (MulAut.conj x).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
  have hp (x : X ⧸ C) :
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A) := by
    rcases h.hstar_overgroup_factor_permutation hX d x with hx | hx
    · exact Or.inl ⟨(hmap d.first x).symm.trans
        (congrArg (fun F : Subgroup J => F.map J.subtype) hx.1),
        (hmap d.second x).symm.trans
        (congrArg (fun F : Subgroup J => F.map J.subtype) hx.2)⟩
    · exact Or.inr ⟨(hmap d.first x).symm.trans
        (congrArg (fun F : Subgroup J => F.map J.subtype) hx.1),
        (hmap d.second x).symm.trans
        (congrArg (fun F : Subgroup J => F.map J.subtype) hx.2)⟩
  obtain ⟨hn, hKL, hLJ⟩ := ThompsonImage.selected_pair A B J K hs hd hKJ hp
  refine ⟨hn, hKL, hLJ, ?_⟩
  change ThompsonImage.pairSupport A B N = A ∨
    ThompsonImage.pairSupport A B N = B ∨ ThompsonImage.pairSupport A B N = J
  classical
  unfold ThompsonImage.pairSupport
  split_ifs with hNB hNA hNA
  · exfalso
    apply hKne
    apply bot_unique
    exact (le_normalClosure.trans (le_inf hNA hNB)).trans hd.eq_bot.le
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr hs)

/-- The source generation `X = ⟨D_L,H⟩` gives `X* = L₀* D_L* T*`
 after selecting the factors met by the residual. -/
theorem hstar_overgroup_selected_product_generates
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G))
    (A : Subgroup X) (hgen : A ⊔ H.subgroupOf X = ⊤) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    let K := (pResidual 2 H).map (q.comp (inclusion hHX))
    ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype),
      let L₀ := ThompsonImage.pairSupport (d.first.map J.subtype) (d.second.map J.subtype)
        (normalClosure (K : Set (X ⧸ C)))
      L₀ ⊔ (A ⊔ (T.subtype (hH.1.1.2.trans hHX) : Subgroup X)).map q = ⊤ := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  let f := inclusion hHX
  let K := (pResidual 2 H).map (q.comp f)
  let S := T.subtype (hH.1.1.2.trans hHX)
  have hHgen : (pResidual 2 H).map f ⊔ (S : Subgroup X) = H.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_map, map_subgroupOf_eq_of_le hHX]
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf X).map X.subtype = H
    rw [map_subgroupOf_eq_of_le (hH.1.1.2.trans hHX)]
    have hs := congrArg (fun B : Subgroup H => B.map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    have hTmap : (T.subtype hH.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hH.1.1.2
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hTmap] using hs
  have hKgen : K ⊔ (S : Subgroup X).map q = (H.subgroupOf X).map q := by
    simpa only [Subgroup.map_sup, map_map] using congrArg (fun B : Subgroup X => B.map q) hHgen
  have htop : A.map q ⊔ (H.subgroupOf X).map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  change ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype), _
  intro d
  have hKL := (h.hstar_overgroup_selected_factor_product hout hH hZH hHX hX d).2.1
  apply top_unique
  rw [← htop, ← hKgen, Subgroup.map_sup]
  exact sup_le (le_sup_of_le_right le_sup_left)
    (sup_le (le_sup_of_le_left hKL) (le_sup_of_le_right le_sup_right))

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
