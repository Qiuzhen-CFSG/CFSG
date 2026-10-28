module

public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Stellmacher.SectionFiveToSeven.Defs
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# The quotient normalizer transfer in Stellmacher (5.2)

Let `S` be a Sylow two-subgroup, `B=B(S)`, and suppose `[K,B]=K`.  For a
normal quotient kernel `C`, the two-core of `G/C` normalizes the image of
`K`.  This is the sentence “as above in the proof of (1)” in the source.

The key point is that every two-subgroup `D` of the quotient containing the
image of `B` normalizes that image.  Pull `D` back to `G`, choose a Sylow
two-subgroup of the pullback containing `B`, and map it onto `D`.  The
ambient Baumann weak-closure theorem makes this Sylow lift normalize `B`, so
its quotient image normalizes the image of `B`.  Applying this to the join
of the quotient two-core and the Baumann image supplies the missing
normalizer premise.  Normality of the two-core and the mapped commutator
identity then give the result by the generic full-commutator normalizer
transfer.

No identification of the quotient Baumann image with a Baumann subgroup of
a quotient Sylow subgroup is used.  Source: B. Stellmacher, Journal of
Algebra 190 (1997), proof of Lemma (5.2), p. 29.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem quotient_twoOvergroup_le_normalizer_baumann_image
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (C : Subgroup G) [C.Normal]
    (D : Subgroup (G ⧸ C)) (hDtwo : IsPGroup 2 D)
    (hBD : (baumannIn (S : Subgroup G)).map (QuotientGroup.mk' C) ≤ D) :
    D ≤ Subgroup.normalizer
      ((baumannIn (S : Subgroup G)).map (QuotientGroup.mk' C) : Set (G ⧸ C)) := by
  classical
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let B : Subgroup G := baumannIn (S : Subgroup G)
  let E : Subgroup G := D.comap q
  have hBE : B ≤ E := by
    intro b hb
    exact hBD (Subgroup.mem_map_of_mem q hb)
  let BE : Subgroup E := B.subgroupOf E
  have hBtwo : IsPGroup 2 B :=
    S.isPGroup'.to_le (show B ≤ (S : Subgroup G) from inf_le_left)
  have hBEtwo : IsPGroup 2 BE :=
    hBtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hBE).symm
  obtain ⟨U, hBEU⟩ := hBEtwo.exists_le_sylow
  let f₀ : E →* G ⧸ C := q.comp E.subtype
  let f : E →* D := f₀.codRestrict D (fun x ↦ x.property)
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective C d
    let gE : E := ⟨g, by
      change q g ∈ D
      exact (show q g = (d : G ⧸ C) by simpa [q] using hg) ▸ d.property⟩
    refine ⟨gE, ?_⟩
    apply Subtype.ext
    change q g = (d : G ⧸ C)
    simpa [q] using hg
  let Ubar : Sylow 2 D := U.mapSurjective hf
  have hUbarTop : (Ubar : Subgroup D) = ⊤ :=
    (Ubar.is_maximal' (hDtwo.to_subgroup ⊤) le_top).symm
  let UG : Subgroup G := (U : Subgroup E).map E.subtype
  have hBUG : B ≤ UG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBE]
    exact Subgroup.map_mono hBEU
  have hUGtwo : IsPGroup 2 UG := U.isPGroup'.map E.subtype
  have hUGnormB : UG ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B, baumannIn, omegaOneCenter,
      Stellmacher.omegaOneCenterAmbient] using
      (Stellmacher.twoSubgroup_le_normalizer_baumann S UG hUGtwo (by
        simpa [B, baumannIn, omegaOneCenter,
          Stellmacher.omegaOneCenterAmbient] using hBUG))
  have hUGmap : UG.map q = D := by
    apply le_antisymm
    · rintro y ⟨g, hg, rfl⟩
      rcases hg with ⟨e, heU, rfl⟩
      exact e.property
    · intro d hd
      let dD : D := ⟨d, hd⟩
      have hdUbar : dD ∈ (Ubar : Subgroup D) := by
        rw [hUbarTop]
        trivial
      rcases hdUbar with ⟨e, heU, he⟩
      refine ⟨(e : G), ⟨e, heU, rfl⟩, ?_⟩
      exact congrArg Subtype.val he
  rw [← hUGmap]
  exact (Subgroup.map_mono hUGnormB).trans
    (Subgroup.le_normalizer_map q)

/-- The two-core of the source quotient normalizes the image of `K` when
`K` is its full commutator with the ambient Baumann subgroup. -/
public theorem five_two_quotient_twoCore_le_normalizer
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (C K : Subgroup G) [C.Normal]
    (hcomm : K = ⁅K, baumannIn (S : Subgroup G)⁆) :
    let q : G →* G ⧸ C := QuotientGroup.mk' C
    pCore 2 (G ⧸ C) ≤
      Subgroup.normalizer (K.map q : Set (G ⧸ C)) := by
  classical
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let B : Subgroup G := baumannIn (S : Subgroup G)
  let Kbar : Subgroup (G ⧸ C) := K.map q
  let Bbar : Subgroup (G ⧸ C) := B.map q
  let Wbar : Subgroup (G ⧸ C) := pCore 2 (G ⧸ C)
  have hBtwo : IsPGroup 2 B :=
    S.isPGroup'.to_le (show B ≤ (S : Subgroup G) from inf_le_left)
  have hBbarTwo : IsPGroup 2 Bbar := hBtwo.map q
  have hWbarTwo : IsPGroup 2 Wbar := pCore_isPGroup
  have hQtwo : IsPGroup 2 ↑(Wbar ⊔ Bbar) :=
    hWbarTwo.to_sup_of_normal_left hBbarTwo
  have hQnormB : Wbar ⊔ Bbar ≤ Subgroup.normalizer (Bbar : Set (G ⧸ C)) := by
    simpa [B, Bbar, q] using
      quotient_twoOvergroup_le_normalizer_baumann_image
        S C (Wbar ⊔ Bbar) hQtwo le_sup_right
  have hWnormB : Wbar ≤ Subgroup.normalizer (Bbar : Set (G ⧸ C)) :=
    le_sup_left.trans hQnormB
  have hKBnormW : Kbar ⊔ Bbar ≤
      Subgroup.normalizer (Wbar : Set (G ⧸ C)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcommbar : ⁅Kbar, Bbar⁆ = Kbar := by
    have hm := congrArg (Subgroup.map q) hcomm.symm
    simpa [Kbar, Bbar, B, Subgroup.map_commutator] using hm
  exact Subgroup.twoSubgroup_le_normalizer_of_full_commutator
    Kbar Bbar Wbar hBbarTwo hWbarTwo hKBnormW hWnormB hcommbar

end Stellmacher.SectionsFiveToSeven
