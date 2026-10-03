module

public import ABG.ChapterII.Section2.SemidihedralCentralizerSylow
public import ABG.ChapterII.Section2.SimpleQD
public import ABG.ChapterII.Section1.FourInvolutionRepresentatives
public import Theory.GroupTheory.NormalizerActionSurjective
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.ElementaryAbelian.Basic

/-!
# Fusion in overgroups of a semidihedral involution centralizer

In a finite simple group with semidihedral Sylow two-subgroups, let `T` be
a four-group containing an involution `x`. Every subgroup containing both
`C_G(x)` and `N_G(T)` fuses all its involutions to `x`.

Choose a Sylow subgroup of `C_G(x)` containing `T`. The QD fusion theorem
shows that the centralizer contains an ambient Sylow, so equality of Sylow
orders promotes the chosen subgroup to an ambient semidihedral Sylow. Both
of its involution classes meet `T`, and simplicity gives the full automorphism
group on `T`. All the conjugations therefore take place in the overgroup.

Source: Alperin--Brauer--Gorenstein, III.7 Proposition 8, alternative
strong-embedding proof, article p.110,
`refs/original/n-group-global/semidihedral-source/abg-iii7-8.pdf`.
-/

namespace Stellmacher.Recognition

private theorem sylow_between_four_and_centralizer
    {G : Type*} [Group G] [Finite G]
    (hQD : ABG.IsQDGroup G) (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) (hT : Nat.card T = 4)
    (hTC : T ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ P : Sylow 2 G, IsSemidihedralGroup P ∧ T ≤ P ∧
      (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
  let C := Subgroup.centralizer ({x} : Set G)
  obtain ⟨R₀, _, ⟨e₀⟩⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  have hU : Nat.card (T.subgroupOf C) = 2 ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv).trans hT
  obtain ⟨R, hTR⟩ := (IsPGroup.of_card hU).exists_le_sylow
  have hRcard : Nat.card ((R : Subgroup C).map C.subtype) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    calc
      Nat.card R = Nat.card R₀ := Nat.card_congr (R.equiv R₀).toEquiv
      _ = Nat.card S := Nat.card_congr e₀.symm.toEquiv
      _ = _ := S.card_eq_multiplicity
  let P : Sylow 2 G := Sylow.ofCard ((R : Subgroup C).map C.subtype) hRcard
  refine ⟨P, ABG.semidihedral_equiv (S.equiv P) hS, ?_,
    Subgroup.map_subtype_le (R : Subgroup C)⟩
  intro t ht
  exact ⟨⟨t, hTC ht⟩, hTR ht, rfl⟩

private theorem four_normalizer_conjugates
    {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) [IsKleinFour T] (hindex : ABG.automizerIndex T = 6)
    (x y : T) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (T : Set G), g * (x : G) * g⁻¹ = y := by
  classical
  let f : MulAut T := IsKleinFour.mulEquiv (Equiv.swap x y)
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hx) (Ne.symm hy))
  have hs : Function.Surjective T.normalizerMonoidHom :=
    T.normalizerMonoidHom_surjective_of_index_eq_card (by
      rw [IsKleinFour.card_mulAut T]
      exact hindex)
  obtain ⟨g, hg⟩ := hs f
  have hh := congrArg (fun f : MulAut T => (f x : G)) hg
  change (g : G) * (x : G) * (g : G)⁻¹ = (Equiv.swap x y x : G) at hh
  exact ⟨g, g.property, by simpa only [Equiv.swap_apply_left] using hh⟩

/-- Every overgroup of the involution centralizer and the chosen four-group
normalizer has a single involution class, represented by the chosen involution. -/
public theorem involution_fusion_of_semidihedral_centralizer_and_four_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) [IsElementaryAbelian 2 T]
    (hT : Nat.card T = 4) (hxT : x ∈ T)
    (M : Subgroup G) (hCM : Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNM : Subgroup.normalizer (T : Set G) ≤ M) :
    ∀ y ∈ M, orderOf y = 2 → ∃ m ∈ M, m * x * m⁻¹ = y := by
  classical
  let : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour T := ⟨hT, IsElementaryAbelian.exponent_eq_prime⟩
  have hTC : T ≤ Subgroup.centralizer ({x} : Set G) :=
    T.le_centralizer.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxT))
  obtain ⟨P, hP, hTP, hPC⟩ := sylow_between_four_and_centralizer
    (ABG.isQDGroup_of_simple ⟨S, hS⟩) S hS x hx T hT hTC
  obtain ⟨_, Q, hframe⟩ := ABG.exists_quasiDihedralFusionFrame P hP
  have hindex : ABG.automizerIndex T = 6 :=
    (ABG.quasiDihedral_qdPattern_of_simple P T Q
      ⟨hP, hTP, hframe.2.2.1, inferInstance, hframe.2.2.2.2⟩).2.2.2.1
  have hPM : (P : Subgroup G) ≤ M := hPC.trans hCM
  have hTM : T ≤ M := hTP.trans hPM
  let xM : M := ⟨x, hTM hxT⟩
  let i : P →* M := Subgroup.inclusion hPM
  have hfour (t : P) (htT : (t : G) ∈ T) (ht : orderOf t = 2) :
      IsConj xM (i t) := by
    obtain ⟨g, hgN, hg⟩ := four_normalizer_conjugates T hindex
      ⟨x, hxT⟩ ⟨t, htT⟩ (by
        intro he
        have hx1 : x = 1 := congrArg Subtype.val he
        simp [hx1] at hx) (by
        intro he
        have htG1 : (t : G) = 1 := congrArg (fun u : T => (u : G)) he
        have ht1 : t = 1 := Subtype.ext htG1
        simp [ht1] at ht)
    exact isConj_iff.mpr ⟨⟨g, hNM hgN⟩, Subtype.ext hg⟩
  obtain ⟨z, t, hzT, htT, hz, ht, _, hcov⟩ :=
    ABG.QuasiDihedral.four_involution_representatives
      (P : Subgroup G) hP T hTP inferInstance
  have hlocal (a : P) (ha : orderOf a = 2) : IsConj (i a) xM := by
    rcases hcov a ha with haz | hat
    · exact (i.map_isConj haz).trans (hfour z hzT hz).symm
    · exact (i.map_isConj hat).trans (hfour t htT ht).symm
  intro y hyM hy
  let yM : M := ⟨y, hyM⟩
  have hyMorder : orderOf yM = 2 := (Subgroup.orderOf_coe yM).symm.trans hy
  obtain ⟨a, hya⟩ := (P.subtype hPM).exists_isConj_of_orderOf_eq_prime_pow
    (x := yM) (n := 1) (by simpa using hyMorder)
  have ha : orderOf a = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hya
    have he := (MulAut.conj g).orderOf_eq yM
    change orderOf (g * yM * g⁻¹) = orderOf yM at he
    rw [hg] at he
    exact (Subgroup.orderOf_coe a).symm.trans (he.trans hyMorder)
  let e : P.subtype hPM ≃* P := Subgroup.subgroupOfEquivOfLe hPM
  have hax : IsConj (a : M) xM := hlocal (e a) ((e.orderOf_eq a).trans ha)
  obtain ⟨m, hm⟩ := isConj_iff.mp (hya.trans hax).symm
  exact ⟨m, m.property, congrArg Subtype.val hm⟩

end Stellmacher.Recognition
