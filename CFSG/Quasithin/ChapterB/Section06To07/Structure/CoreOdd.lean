module

public import CFSG.Quasithin.ChapterB.Section06To07.Residual
public import Theory.GroupTheory.MinimalParabolicResidual
public import Theory.GroupTheory.MinimalSylowSupplementKernel
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Quotient

import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The odd core and solvable residual of a minimal parabolic

For the unique maximal overgroup `M` of a Sylow two-subgroup `T`, put
`J = M.normalCore` and `Q = O₂(H)`. The intersection `T ∩ J` is `Q`, so
`Q` is a Sylow two-subgroup of `J`. Consequently the literal image of `J`
in `H/Q` has odd order. The unique-maximal property places this image in
the Frattini subgroup, proving its nilpotence.

When `H` is solvable, the existing solvable primitive-group construction
identifies the residual of `H/J` as an elementary abelian odd-prime group,
with its actual irreducible conjugation action by the image of `T`.
The map `H/Q → H/J` then gives the odd residual of `H/Q`: its restricted
kernel is contained in the odd image of `J`, and its image is contained
in the odd residual of `H/J`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.6.8,
printed pp.113–115, especially (2), (5), and the opening normalizer argument.
The odd nilpotent assertion concerns `J/Q`, not `J` in the original group.
This leaf imports `Structure` and must be assembled above that module.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterB
open Subgroup
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem uniqueMaximal (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    Order.HasUniqueMaximalOver (T : Subgroup H) ⊤ := hP.1

/-- The intersection of the fixed Sylow subgroup with `J` is exactly `O₂(H)`. -/
theorem minimalParabolic_sylow_inf_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    (T : Subgroup H) ⊓ minimalParabolicCore T hP = pCore 2 H := by
  apply le_antisymm
  · exact sylow_inf_normal_le_twoCore_of_uniqueMaximal T (uniqueMaximal T hP)
      (minimalParabolicMax T hP) (minimalParabolicCore T hP)
      ⟨(minimalParabolicMax_spec T hP).2, (minimalParabolicMax_spec T hP).1⟩
      (normalCore_le _)
  · exact le_inf (pCore_isPGroup.le_sylow_of_normal T)
      (minimalParabolicTwoCore_le_core T hP)

/-- B.6.8(5), with the Sylow subgroup expressed in the literal carrier `J`. -/
theorem minimalParabolic_twoCore_sylow_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    ∃ S : Sylow 2 (minimalParabolicCore T hP),
      (S : Subgroup (minimalParabolicCore T hP)) =
        (pCore 2 H).subgroupOf (minimalParabolicCore T hP) := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal (minimalParabolicCore T hP)
  refine ⟨S, ?_⟩
  rw [hS, ← minimalParabolic_sylow_inf_core T hP]
  ext x
  exact (and_iff_left x.property).symm

/-- The source subgroup `J̄`, embedded in the literal quotient `H/O₂(H)`. -/
abbrev minimalParabolicCoreImage (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    Subgroup (H ⧸ pCore 2 H) :=
  (minimalParabolicCore T hP).map (QuotientGroup.mk' (pCore 2 H))

/-- The image of `J` after factoring out the two-core has odd order. -/
theorem minimalParabolic_coreImage_odd (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : Odd (Nat.card (minimalParabolicCoreImage T hP)) := by
  obtain ⟨S, hS⟩ := minimalParabolic_twoCore_sylow_core T hP
  have hi : Nat.card (minimalParabolicCoreImage T hP) =
      (S : Subgroup (minimalParabolicCore T hP)).index := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    exact congrArg Subgroup.index hS.symm
  rw [hi]
  exact Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index (even_iff_two_dvd.mp he))

private theorem coreImage_le_frattini (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    minimalParabolicCoreImage T hP ≤ frattini (H ⧸ pCore 2 H) := by
  let J := minimalParabolicCore T hP
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq := QuotientGroup.mk'_surjective (pCore 2 H)
  let D := minimalParabolicCoreImage T hP
  let : D.Normal := (inferInstance : J.Normal).map q hq
  apply Sylow.normal_le_frattini_of_minimal_supplement (T.mapSurjective hq) D
    (minimalParabolic_coreImage_odd T hP).not_two_dvd_nat
  intro L hTL hLD
  have hDJ : D.comap q = J := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr
      (minimalParabolicTwoCore_le_core T hP)]
  have hTJ : (T : Subgroup H) ≤ L.comap q := map_le_iff_le_comap.mp hTL
  have hLJ : L.comap q ⊔ J = ⊤ := by
    rw [← hDJ, comap_sup_eq q L D hq, hLD, comap_top]
  have htop : L.comap q = ⊤ := by
    by_contra hne
    have hLM := (uniqueMaximal T hP).le_maximal
      ⟨(minimalParabolicMax_spec T hP).2, (minimalParabolicMax_spec T hP).1.covBy_top⟩
      hTJ (lt_top_iff_ne_top.mpr hne)
    exact (minimalParabolicMax_spec T hP).1.ne_top
      (top_unique (hLJ ▸ sup_le hLM (normalCore_le _)))
  apply Subgroup.comap_injective hq
  simpa using htop

/-- The image of `J` after factoring out the two-core is nilpotent. -/
theorem minimalParabolic_coreImage_nilpotent (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    Group.IsNilpotent (minimalParabolicCoreImage T hP) := by
  have hle := coreImage_le_frattini T hP
  let : Group.IsNilpotent (frattini (H ⧸ pCore 2 H)) := frattini_nilpotent
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hle)

private theorem stellmacher_residual_eq (G : Type*) [Group G] [Finite G] :
    Stellmacher.twoResidualAmbient (⊤ : Subgroup G) = pResidual 2 G := by
  rw [Stellmacher.SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  apply le_antisymm
  · exact BenderSuzuki.External.hktPResidual_le _ inferInstance
      (Subgroup.isPGroup_quotient_pResidual 2)
  · exact sInf_le ⟨BenderSuzuki.External.hktPResidual_normal,
      BenderSuzuki.External.hktPResidual_quotient_isPGroup⟩

set_option backward.isDefEq.respectTransparency false in
/-- The solvable star quotient has an elementary abelian odd residual,
irreducible under the mapped Sylow subgroup and disjoint from the mapped maximal. -/
theorem minimalParabolic_solvable_star_structure (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      IsElementaryAbelian p (pResidual 2 (minimalParabolicStarQuotient T hP)) ∧
      Stellmacher.IsIrreducibleSection (minimalParabolicStarSylow T hP) ⊥
        (pResidual 2 (minimalParabolicStarQuotient T hP)) ∧
      pResidual 2 (minimalParabolicStarQuotient T hP) ⊓
        (minimalParabolicMax T hP).map (QuotientGroup.mk' (minimalParabolicCore T hP)) = ⊥ := by
  obtain ⟨p, E, hp, ho, hn, he, hEM, hET, hir⟩ :=
    Stellmacher.SectionThree.quotientCoreFree_data T (minimalParabolicMax T hP) T rfl
      (minimalParabolicMax_spec T hP).1 (minimalParabolicMax_spec T hP).2
      (fun M hM hTM => minimalParabolicMax_unique T hP hM hTM) hs
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p E := he
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  have hR : pResidual 2 (minimalParabolicStarQuotient T hP) = E := by
    rw [← stellmacher_residual_eq]
    exact Stellmacher.SectionThree.twoResidualAmbient_top_eq_of_normal_complement_sylow_two
      hp hp2 E _ (minimalParabolicStarSylow T hP) (minimalParabolicStarSylow_coe T hP) hn
      (IsElementaryAbelian.isPGroup p E) hET
  refine ⟨p, hp, ho, hR ▸ he, ?_, hR.symm ▸ hEM⟩
  obtain ⟨_, hir⟩ := hir
  dsimp only at hir
  rw [minimalParabolicStarSylow_coe]
  simpa only [stellmacher_residual_eq, minimalParabolicStarQuotient,
    minimalParabolicCore] using hir

/-- The residual of the literal star quotient `H/J` has odd order. -/
theorem minimalParabolic_solvable_star_residual_odd (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H) :
    Odd (Nat.card (pResidual 2 (minimalParabolicStarQuotient T hP))) := by
  obtain ⟨p, hp, ho, he, _⟩ := minimalParabolic_solvable_star_structure T hP hs
  let : Fact p.Prime := ⟨hp⟩
  let := he
  obtain ⟨n, hc⟩ := (IsElementaryAbelian.isPGroup p
    (pResidual 2 (minimalParabolicStarQuotient T hP))).exists_card_eq
  rw [hc]
  exact ho.pow

/-- The solvable consequence needed by the Chapter E and qrc arguments:
`O²(H/O₂(H))` has odd order, under the original minimal-parabolic hypotheses. -/
theorem minimalParabolic_solvable_quotient_residual_odd (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H) :
    Odd (Nat.card (pResidual 2 (H ⧸ pCore 2 H))) := by
  let J := minimalParabolicCore T hP
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let qJ := QuotientGroup.mk' J
  have hQker : Q ≤ qJ.ker := by
    rw [QuotientGroup.ker_mk']
    exact minimalParabolicTwoCore_le_core T hP
  let f : (H ⧸ Q) →* (H ⧸ J) := QuotientGroup.lift Q qJ hQker
  have hk : f.ker = minimalParabolicCoreImage T hP := by
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  let R := pResidual 2 (H ⧸ Q)
  let g : R →* (H ⧸ J) := f.comp R.subtype
  have hko : Odd (Nat.card g.ker) := by
    have hfo : Odd (Nat.card f.ker) := hk.symm ▸ minimalParabolic_coreImage_odd T hP
    apply hfo.of_dvd_nat
    let i : g.ker →* f.ker := (R.subtype.comp g.ker.subtype).codRestrict f.ker
      (fun x => x.property)
    apply card_dvd_of_injective i
    intro a b hab
    have he : ((a : R) : H ⧸ Q) = ((b : R) : H ⧸ Q) :=
      congrArg (fun x : f.ker => (x : H ⧸ Q)) hab
    exact Subtype.ext (Subtype.ext he)
  have hro : Odd (Nat.card g.range) := by
    apply (minimalParabolic_solvable_star_residual_odd T hP hs).of_dvd_nat
    apply card_dvd_of_le
    change (f.comp R.subtype).range ≤ pResidual 2 (H ⧸ J)
    rw [MonoidHom.range_comp, range_subtype]
    exact map_pResidual_le 2 f
  rw [← g.ker.card_mul_index, index_ker]
  exact hko.mul hro

end CFSG.Quasithin.ChapterB
end
end
