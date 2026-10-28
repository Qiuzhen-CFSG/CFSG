module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CanonicalSeed

/-!
# The original cubic factor and its orbit in the binary branch

An S-invariant normal cubic factor of K can be prescribed as the first
factor of the conjugate pair. Enlarge it by O₂(K), use T-irreducibility
to obtain generation, then take O² again. This applies to the literal
O²(K ∩ X) supplied by the original binary parabolic geometry.

That factor is normal in MI. Since reducibility puts Kc in MI, both it
and its T-conjugate are normal in Kc. Their span K is solvable and normal
in Kc. The alternative in which Kc is a perfect component orbit is
impossible: its solvable radical is Mc-invariant and contains K, hence
contains the whole Mc-orbit span Kc. Thus K = Kc is proved.

The binary consumer combines this equality with CanonicalSeed and the
existing quotient/action results. After the pair construction, the local
premise still to prove is [X,K₂] ≤ O₂(X). This does not identify the earlier
H₁,H₂ or prove the L₄(2) exclusion and arbitrary-seed version of 15.2.22.
The earlier component-orbit alternative remains supplied by
qt-e-152-plane-geometry. The outside-component and faithful-action inputs
retain their component-model producers; final discharge remains with
qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.21--23, printed pp.1114--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_sup_two (Y Q : Subgroup G) (hp : IsPPerfect 2 Y)
    (hq : IsPGroup 2 Q) (hn : Q ≤ normalizer (Y : Set G)) :
    (pResidual 2 (Y ⊔ Q : Subgroup G)).map (Y ⊔ Q).subtype = Y := by
  let D := Y ⊔ Q
  let : (Y.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer hn)
  have hp' : IsPPerfect 2 (Y.subgroupOf D) :=
    hp.of_surjective (subgroupOfEquivOfLe (show Y ≤ D from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y ≤ D from le_sup_left)).symm.surjective
  have hs : Y.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ D from le_sup_left) (show Q ≤ D from le_sup_right)]
    exact subgroupOf_self D
  rw [pResidual_eq_of_isPPerfect_sup (Y.subgroupOf D) (Q.subgroupOf D)
    hp' hq.comap_subtype hs, map_subgroupOf_eq_of_le (show Y ≤ D from le_sup_left)]

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Start the constructed residual pair with a specified normal cubic factor.
The second factor is its literal t-conjugate, and irreducibility of T supplies
both generation and its distinctness from the first. -/
theorem residualPair_with_first (hI : PlaneEscapes Mc ZS I)
    {Y : Subgroup G} (hY : Y ∈ normalCubicResiduals (smallActionK H))
    (hSY : smallActionS T ZS ≤ normalizer (Y : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      p.K₁ = Y := by
  let K := smallActionK H
  let S := smallActionS T ZS
  let Q := K.pCoreIn 2
  let L := Y ⊔ Q
  let f := (MulAut.conj t).toMonoidHom
  let L₂ := L.map f
  have hirr := sylow_irreducible d
  have hKY : K ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hY.1).mp hY.2.1
  have hKQ : K ≤ normalizer (Q : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hKL : K ≤ normalizer (L : Set G) :=
    (le_inf hKY hKQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hLK : L ≤ K := sup_le hY.1 (pCoreIn_le 2 K)
  have hL₂K : L₂ ≤ K := (map_mono hLK).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hirr.1 ht))
  have hSL : S ≤ normalizer (L : Set G) :=
    (le_inf hSY ((inf_le_left.trans hirr.1).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTL : (T : Subgroup G) ≤ normalizer ((L ⊔ L₂ : Subgroup G) : Set G) := by
    simpa only [inv_inv] using index_two_normalizes_pair S (T : Subgroup G) L
      inf_le_left (d.escape_index hI).2 t⁻¹ ((T : Subgroup G).inv_mem ht)
      (by simpa only [inv_mem_iff] using htS) hSL
  have hspan : L ⊔ L₂ = K := by
    rcases hirr.2 (L ⊔ L₂) (le_sup_right.trans le_sup_left)
      (sup_le hLK hL₂K) hTL with he | he
    · have hp : IsPGroup 2 Y := (isPGroup_pCoreIn 2 K).to_le
        ((le_sup_left.trans le_sup_left).trans he.le)
      obtain ⟨n,hn⟩ := (hp.to_quotient (pCore 2 Y)).exists_card_eq
      rw [hY.2.2.2] at hn
      have hd : 3 ∣ 2 ^ n := by rw [← hn]
      exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
    · exact he
  have hKL₂ : K ≤ normalizer (L₂ : Set G) :=
    normalizes_conjugate_of_normalizes (hirr.1 ht) hKL
  let : (L.subgroupOf (L ⊔ L₂)).Normal :=
    normal_subgroupOf_of_le_normalizer (hspan ▸ hKL)
  let : (L₂.subgroupOf (L ⊔ L₂)).Normal :=
    normal_subgroupOf_of_le_normalizer (hspan ▸ hKL₂)
  have hres : (pResidual 2 L).map L.subtype = Y :=
    residual_sup_two Y Q hY.2.2.1 (isPGroup_pCoreIn 2 K) ((pCoreIn_le 2 K).trans hKY)
  have hres₂ : (pResidual 2 L₂).map L₂.subtype = Y.map f := by
    rw [← map_embedded_pResidual 2 L f, hres]
  have hYY : Y ⊔ Y.map f = K := by
    rw [← hres₂, ← hres, embedded_pResidual_sup_of_relative_normal, hspan,
      (pResidual_eq_top_iff 2 K).mpr (isPPerfect_embedded_pResidual 2 H),
      ← MonoidHom.range_eq_map, range_subtype]
  exact ⟨⟨Y,Y.map f,ht,htS,hY,
    normalCubicResiduals_conjugate K Y t (hirr.1 ht) hY,hYY,rfl,hSY⟩,rfl⟩


/-- If the first constructed factor is normal in MI, so is its conjugate
relative to Kc. Their span makes K normal in Kc. A perfect component-orbit
alternative would then be generated by normal solvable subgroups, impossible.
Thus the original orbit span collapses to K. -/
theorem orbit_eq_of_pair_factor_normalized
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t)
    (hn : Mc ⊓ I ≤ normalizer (p.K₁ : Set G)) :
    smallActionK H = smallActionKc H Mc := by
  rcases horbit with he | ⟨L,hL,he⟩
  · exact he.symm
  let K := smallActionK H
  let Kc := smallActionKc H Mc
  have hKKc : K ≤ Kc := le_conjugateSpanBy _ _
  have hMcKc : Mc ≤ normalizer (Kc : Set G) := le_normalizer_conjugateSpanBy _ _
  have hTMc : (T : Subgroup G) ≤ Mc := d.geometry.outside.1.1.2.trans d.geometry.in_partner
  have htKc : t ∈ normalizer (Kc : Set G) := hMcKc (hTMc p.t_mem)
  have hKcMI : Kc ≤ Mc ⊓ I :=
    (orbit_centralizes_of_reducible d (Or.inr ⟨L,hL,he⟩) hI hnot).trans
      (d.centralizer_le_intersection hI)
  have hn₁ : Kc ≤ normalizer (p.K₁ : Set G) := hKcMI.trans hn
  have hn₂ : Kc ≤ normalizer (p.K₂ : Set G) := by
    rw [← p.conjugate]
    exact normalizes_conjugate_of_normalizes htKc hn₁
  have hKcK : Kc ≤ normalizer (K : Set G) := by
    rw [show K = smallActionK H from rfl, ← p.span]
    exact (le_inf hn₁ hn₂).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let e := ChosenGeometry.residualQuotientEquiv H d.geometry.quotient.some
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  let : Group.IsNilpotent (pCore 2 K) := (pCore_isPGroup (p := 2) (G := K)).isNilpotent
  let : Group.IsSolvable K := (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr
    ⟨inferInstance,inferInstance⟩
  let A := K.subgroupOf Kc
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hKKc).mpr hKcK
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hKKc).toMonoidHom) (subgroupOfEquivOfLe hKKc).injective
  let R := (solvableRadical Kc).map Kc.subtype
  have hKR : K ≤ R := by
    have hh := map_mono (f := Kc.subtype) (le_solvableRadical A inferInstance inferInstance)
    rwa [map_subgroupOf_eq_of_le hKKc] at hh
  have hMcR : Mc ≤ normalizer (R : Set G) := hMcKc.trans
    (normalizer_le_normalizer_characteristic_image Kc (solvableRadical Kc))
  have hKcR : Kc ≤ R := conjugateSpanBy_le hKR hMcR
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (Kc.subtype.subgroupMap_surjective (solvableRadical Kc))
  let : Group.IsSolvable Kc := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hKcR)
  let := Chapter1.mem_L_isPerfect hL
  let : Group.IsPerfect (componentOrbit L (T : Subgroup G)) := isPerfect_iSup_conjugates L T
  let : Group.IsPerfect Kc := by
    change Group.IsPerfect (smallActionKc H Mc)
    rw [he]
    infer_instance
  have hne : Kc ≠ ⊥ := by
    intro hz
    exact d.residual_not_le ((hKKc.trans hz.le).trans bot_le)
  let : Nontrivial Kc := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact (Group.IsPerfect.not_isSolvable Kc inferInstance).elim

/-- The first factor is the actual O²(K ∩ X), and its normality in MI
comes from the original opposite parabolic. -/
theorem binary_pair_with_original_factor
    (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      p.K₁ = (pResidual 2 (smallActionK H ⊓ X : Subgroup G)).map
        (smallActionK H ⊓ X).subtype ∧
      Mc ⊓ I ≤ normalizer (p.K₁ : Set G) := by
  obtain ⟨hLK,hperfect,hcard,hSL,hMI,_⟩ := b.binary_factor_data_of_action d hI hout f hker
  have hKL := (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans hMI
  have hn := (normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
  obtain ⟨p,he⟩ := residualPair_with_first d hI ⟨hLK,hn,hperfect,hcard⟩ hSL t ht htS
  exact ⟨p,he,by rwa [he]⟩


/-- In the binary branch, construct the pair starting with O²(K ∩ X)
and discharge K = Kc from the preceding component-orbit alternative. -/
theorem binary_pair_and_orbit_eq
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      p.K₁ = (pResidual 2 (smallActionK H ⊓ X : Subgroup G)).map
        (smallActionK H ⊓ X).subtype ∧ smallActionK H = smallActionKc H Mc := by
  obtain ⟨p,he,hn⟩ := binary_pair_with_original_factor d hI b hout f hker t ht htS
  have hnot := b.binary_reducible_of_normalized d hI (b.binary_sylow_normalizes d hI hout f hker)
  exact ⟨p,he,orbit_eq_of_pair_factor_normalized d horbit hI hnot p hn⟩

open ChapterD.UniqueFactor in
/-- After the preceding pair construction, the remaining local input is
core-centralization by the complementary cubic factor. The seed quotient, residual comparison,
conjugate-seed relation, K = Kc, and the normalizer contradiction are all
proved on the original subgroups. -/
theorem binary_component_false_of_original_factor
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t)
    (hfirst : p.K₁ = (pResidual 2 (smallActionK H ⊓ X : Subgroup G)).map
      (smallActionK H ⊓ X).subtype)
    (hc : ⁅X,p.K₂⁆ ≤ X.pCoreIn 2) : False := by
  have hnot := b.binary_reducible_of_normalized d hI (b.binary_sylow_normalizes d hI hout f hker)
  have hn : Mc ⊓ I ≤ normalizer (p.K₁ : Set G) := by
    rw [hfirst]
    exact b.binary_factor_normalized d hI hout (b.binary_normal_of_action d hI hout f hker)
  exact binary_component_false_of_omega_action d hI hfit e b hout f hker p hc
    (orbit_eq_of_pair_factor_normalized d horbit hI hnot p hn)

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
