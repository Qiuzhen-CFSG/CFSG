module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage
public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer
public import Stellmacher.BaumannNormalizer

/-!
# Thompson and Baumann normalizers in the three-pair branch

For a full three-pair radical image, the same canonical quotient maps the
actual elementary Thompson subgroup onto either the even plane or the full
three-pair group. Lift the radical-image normalizer through the two-core
kernel. A rotation of the three pairs normalizes the Thompson image; the
sixteen-subgroup lattice of the binary cube leaves just those two possibilities
once the proved order-four lower bound is applied.

The even plane has centralizer exactly the three-pair group. This is checked
on six-letter coordinates and eight words. Its normalizer therefore equals
the normalizer of the full three-pair group. Thompson normalizer lifting then
identifies the actual radical and Thompson normalizers inside the replacement
overgroup. Thompson heredity gives the same normalizer for its Baumann subgroup.
No equality of the radical with either characteristic subgroup is asserted.

Pulling back the image alternatives also identifies the core supplement of
the Thompson subgroup: it is the whole radical or its intersection with the
preimage of A₆. The beyond-four nonsylow consumer supplies the three-pair image
and both normalizer equalities on the literal minimum replacement, without
an image premise from its caller. Both moved-cover orders and all central
attachments are retained. Excluding this branch, the original Sylow branches,
and full-point distance four remains with the large-distance assembly owner.

Source: Aschbacher--Smith B.2.3 and B.3.2--4, printed pp.75,83--85;
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
the local Thompson normalizer analysis of Section 5, printed pp.912--927.
These image and normalizer reductions do not establish (5.11) or (5.12).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeThompson
local notation "S" => Equiv.Perm (Fin 6)
private def rotation : S :=
  Equiv.swap 0 2 * Equiv.swap 2 4 * (Equiv.swap 1 3 * Equiv.swap 3 5)

private theorem rotation_normalizes : rotation ∈ normalizer (D 6 : Set S) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hx
    have cert : ∀ i : Fin 8, ∃ j : Fin 8,
        dWords j = rotation * dWords i * rotation⁻¹ := by decide +kernel
    exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr (cert i)
  · rw [card_map_of_injective (MulAut.conj rotation).injective]

private theorem invariant_cube (A : Subgroup S) (hA : A ≤ D 6)
    (hc : 4 ≤ Nat.card A) (hn : normalizer (D 6 : Set S) ≤ normalizer (A : Set S)) :
    A = evenPart 6 ∨ A = D 6 := by
  obtain ⟨r,rfl⟩ := (subgroup_le_D_iff A).mp hA
  rw [card_dLattice] at hc
  have hrot : ∀ i ∈ dLatticeIndices r, ∃ j ∈ dLatticeIndices r,
      dWords j = rotation * dWords i * rotation⁻¹ := by
    intro i hi
    exact (mem_dLattice_iff _ _).mp
      ((mem_normalizer_iff.mp (hn rotation_normalizes) _).mp
        ((dWords_mem_dLattice _ _).mpr hi))
  have cert : ∀ r : Fin 16, 4 ≤ (dLatticeIndices r).card →
      (∀ i ∈ dLatticeIndices r, ∃ j ∈ dLatticeIndices r,
        dWords j = rotation * dWords i * rotation⁻¹) → r = 14 ∨ r = 15 := by
    decide +kernel
  rcases cert r hc hrot with rfl | rfl
  · exact Or.inl dLattice_fourteen
  · exact Or.inr dLattice_fifteen

private abbrev a : S := pairSwap 6 0 * pairSwap 6 1
private abbrev b : S := pairSwap 6 0 * pairSwap 6 2

private theorem even_centralizer : centralizer (evenPart 6 : Set S) = D 6 := by
  apply le_antisymm
  · intro g hg
    have ha : a ∈ evenPart 6 := (mem_evenPart_iff _).mpr ⟨1,by decide⟩
    have hb : b ∈ evenPart 6 := (mem_evenPart_iff _).mpr ⟨2,by decide⟩
    have hga : g*a=a*g := (mem_centralizer_iff.mp hg a ha).symm
    have hgb : g*b=b*g := (mem_centralizer_iff.mp hg b hb).symm
    have h1a : g 1 = a (g 0) := congrArg (fun q : S => q 0) hga
    have h1b : g 1 = b (g 0) := congrArg (fun q : S => q 0) hgb
    have h3 : g 3 = a (g 2) := congrArg (fun q : S => q 2) hga
    have h2 : g 2 = b (g 2) := congrArg (fun q : S => q 2) hgb
    have h4 : g 4 = a (g 4) := congrArg (fun q : S => q 4) hga
    have h5 : g 5 = b (g 4) := congrArg (fun q : S => q 4) hgb
    have table : ∀ i j k : Fin 6, a i = b i → j = b j → k = a k →
        ∃ n : Fin 8, dWords n 0 = i ∧ dWords n 2 = j ∧ dWords n 4 = k := by
      decide +kernel
    obtain ⟨n,h0,h2,h4⟩ := table (g 0) (g 2) (g 4) (h1a.symm.trans h1b) h2 h4
    have words : ∀ n : Fin 8,
        dWords n 1 = a (dWords n 0) ∧ dWords n 3 = a (dWords n 2) ∧
          dWords n 5 = b (dWords n 4) := by decide +kernel
    apply (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr
    refine ⟨n,?_⟩
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · exact (words n).1.trans ((congrArg a h0).trans h1a.symm)
    · exact h2
    · exact (words n).2.1.trans ((congrArg a h2).trans h3.symm)
    · exact h4
    · exact (words n).2.2.trans ((congrArg b h4).trans h5.symm)
  · let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show evenPart 6 ≤ D 6 from inf_le_left))

private theorem even_normalizer : normalizer (evenPart 6 : Set S) =
    normalizer (D 6 : Set S) := by
  apply le_antisymm
  · rw [←even_centralizer]
    exact normalizer_le_normalizer_centralizer (evenPart 6)
  · intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (D 6 ⊓ alternatingGroup (Fin 6)).map (MulAut.conj g).toMonoidHom = _
    have hD : (D 6).map (MulAut.conj g).toMonoidHom = D 6 :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hA : (alternatingGroup (Fin 6)).map (MulAut.conj g).toMonoidHom =
        alternatingGroup (Fin 6) := mem_normalizer_iff_map_conj_eq.mp
      (show g ∈ normalizer (alternatingGroup (Fin 6) : Set S) by
        rw [normalizer_eq_top]; trivial)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,hD,hA]
    rfl

private theorem thompson_normalizer {H : Type*} [Group H] [Finite H]
    (q : H →* S) (hq : Function.Surjective q) (R : Subgroup H) (hk : q.ker ≤ R) :
    normalizer (R.map q : Set S) ≤
      normalizer ((Stellmacher.elementaryAbelianMaxJ R).map q : Set S) := by
  apply (comap_le_comap_of_surjective hq).mp
  rw [Stellmacher.normalizer_comap_map_maxJ R q hq hk,
    comap_normalizer_eq_of_surjective _ hq,comap_map_eq,sup_eq_left.mpr hk]
  exact Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ R

private theorem conjugate_back (A : Subgroup S) (u : S) :
    (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      MonoidHom.id S := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

end CubeThompson

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

/-- In the full three-pair branch, the elementary Thompson image is exactly
its even plane or the entire three-pair group, with the same conjugator. -/
theorem large_distance_cube_thompson_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    (Stellmacher.elementaryAbelianMaxJ d.radical).map
        (SourceReduction.projection h e hz hn d) =
      (evenPart 6).map (MulAut.conj u).toMonoidHom ∨
    (Stellmacher.elementaryAbelianMaxJ d.radical).map
        (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom := by
  let π := SourceReduction.projection h e hz hn d
  let c := (MulAut.conj u⁻¹).toMonoidHom
  let q := c.comp π
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hπ : Function.Surjective π := by
    have hs := s.surjective
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hs
  have hq : Function.Surjective q := (MulAut.conj u⁻¹).surjective.comp hπ
  have hk : q.ker ≤ d.radical := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj u⁻¹).injective,
      SourceReduction.projection_kernel h e hz hn d]
    exact replacement_core_le_radical h d
  have hR : d.radical.map q = D 6 := by
    rw [←map_map,himage,CubeThompson.conjugate_back]
  let J := (Stellmacher.elementaryAbelianMaxJ d.radical).map q
  have hJR : J ≤ D 6 :=
    (map_mono (sSup_le fun _ hE => hE.1)).trans_eq hR
  have hc : 4 ≤ Nat.card J := by
    change 4 ≤ Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map (c.comp π))
    rw [←map_map,card_map_of_injective (MulAut.conj u⁻¹).injective]
    exact large_distance_thompson_image_four_le_knownSimple hb
  have hnJ : normalizer (D 6 : Set S) ≤ normalizer (J : Set S) := by
    rw [←hR]
    exact CubeThompson.thompson_normalizer q hq d.radical hk
  have pullback (A : Subgroup S) (he : J = A) :
      (Stellmacher.elementaryAbelianMaxJ d.radical).map π =
        A.map (MulAut.conj u).toMonoidHom := by
    apply map_injective (f := c) (MulAut.conj u⁻¹).injective
    rw [CubeThompson.conjugate_back,map_map]
    exact he
  exact (CubeThompson.invariant_cube J hJR hc hnJ).imp (pullback _) (pullback _)
/-- In the three-pair branch, the literal radical and its elementary
Thompson subgroup have the same normalizer inside the replacement overgroup.
The kernel is retained when lifting either image normalizer. -/
theorem large_distance_cube_normalizers_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
      normalizer (d.radical : Set d.overgroup) := by
  let π := SourceReduction.projection h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hπ : Function.Surjective π := by
    have hs := s.surjective
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hs
  have hk : π.ker ≤ d.radical := by
    rw [SourceReduction.projection_kernel]
    exact replacement_core_le_radical h d
  have he : normalizer ((Stellmacher.elementaryAbelianMaxJ d.radical).map π : Set S) =
      normalizer (d.radical.map π : Set S) := by
    rcases large_distance_cube_thompson_knownSimple hb u himage with hJ | hJ
    · rw [hJ,himage,←map_normalizer_eq_of_bijective (evenPart 6) (MulAut.conj u).bijective,
        ←map_normalizer_eq_of_bijective (D 6) (MulAut.conj u).bijective,
        CubeThompson.even_normalizer]
    · rw [hJ,himage]
  rw [←Stellmacher.normalizer_comap_map_maxJ d.radical π hπ hk,he,
    comap_normalizer_eq_of_surjective _ hπ,comap_map_eq,sup_eq_left.mpr hk]

/-- The same normalizer also controls the actual Baumann subgroup; no
identification of that subgroup with the whole radical is made. -/
theorem large_distance_cube_baumann_normalizer_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    normalizer (CFSG.Quasithin.ChapterB.baumann d.radical : Set d.overgroup) =
      normalizer (d.radical : Set d.overgroup) := by
  have hJ : Stellmacher.elementaryAbelianMaxJ (CFSG.Quasithin.ChapterB.baumann d.radical) =
      Stellmacher.elementaryAbelianMaxJ d.radical :=
    Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate d.radical _
      (CFSG.Quasithin.ChapterB.elementaryAbelianMaxJ_le_baumann d.radical) inf_le_left
  have hnorm := Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ
    (CFSG.Quasithin.ChapterB.baumann d.radical)
  rw [hJ,large_distance_cube_normalizers_knownSimple hb u himage] at hnorm
  exact le_antisymm hnorm (Stellmacher.normalizer_le_normalizer_baumann d.radical)

/-- The actual core supplement of the Thompson subgroup is either the whole
replacement radical or exactly its even part under the canonical projection. -/
theorem large_distance_cube_thompson_supplement_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    pCore 2 d.overgroup ⊔ Stellmacher.elementaryAbelianMaxJ d.radical =
      d.radical ⊓ (alternatingGroup (Fin 6)).comap
        (SourceReduction.projection h e hz hn d) ∨
    pCore 2 d.overgroup ⊔ Stellmacher.elementaryAbelianMaxJ d.radical = d.radical := by
  let π := SourceReduction.projection h e hz hn d
  have hk : π.ker ≤ d.radical := by
    rw [SourceReduction.projection_kernel]
    exact replacement_core_le_radical h d
  have heven : (evenPart 6).map (MulAut.conj u).toMonoidHom =
      d.radical.map π ⊓ alternatingGroup (Fin 6) := by
    change (D 6 ⊓ alternatingGroup (Fin 6)).map (MulAut.conj u).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective,←himage]
    have hA : (alternatingGroup (Fin 6)).map (MulAut.conj u).toMonoidHom =
        alternatingGroup (Fin 6) := mem_normalizer_iff_map_conj_eq.mp
      (show u ∈ normalizer (alternatingGroup (Fin 6) : Set S) by
        rw [normalizer_eq_top]; trivial)
    rw [hA]
  rcases large_distance_cube_thompson_knownSimple hb u himage with hJ | hJ
  · left
    have hh := congrArg (Subgroup.comap π) (hJ.trans heven)
    rw [comap_inf,comap_map_eq,comap_map_eq,sup_eq_left.mpr hk,
      SourceReduction.projection_kernel] at hh
    exact (sup_comm _ _).trans hh
  · right
    have hh := congrArg (Subgroup.comap π) (hJ.trans himage.symm)
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hk,
      SourceReduction.projection_kernel] at hh
    exact (sup_comm _ _).trans hh

/-- The beyond-four nonsylow consumer supplies the three-pair branch and
both actual normalizer equalities without an image premise from its caller. -/
theorem nonsylow_four_lt_thompson_configuration_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    ∃ u : S,
      d.radical.map (SourceReduction.projection h e hz hn d) =
        (D 6).map (MulAut.conj u).toMonoidHom ∧
      ((Stellmacher.elementaryAbelianMaxJ d.radical).map
          (SourceReduction.projection h e hz hn d) =
        (evenPart 6).map (MulAut.conj u).toMonoidHom ∨
       (Stellmacher.elementaryAbelianMaxJ d.radical).map
          (SourceReduction.projection h e hz hn d) =
        (D 6).map (MulAut.conj u).toMonoidHom) ∧
      normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
        normalizer (d.radical : Set d.overgroup) ∧
      normalizer (CFSG.Quasithin.ChapterB.baumann d.radical : Set d.overgroup) =
        normalizer (d.radical : Set d.overgroup) := by
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hb2 : 2 < replacementDistance h d := by omega
  exact ⟨u,hu,large_distance_cube_thompson_knownSimple hb2 u hu,
    large_distance_cube_normalizers_knownSimple hb2 u hu,
    large_distance_cube_baumann_normalizer_knownSimple hb2 u hu⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
