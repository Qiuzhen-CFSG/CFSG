module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleCore.FlagBlocks

/-!
# The two-cores and marked SL₃ quotients of the middle flag joins

The large diagonal block is onto SL₃(2). Its kernel is an extension of the
rectangular unipotent radical by the small upper unitriangular SL₂ block,
hence a two-group. The trivial two-core of SL₃ identifies this kernel with
the intrinsic two-core of the join, and gives the marked quotient maps.

Source: Aschbacher–Smith, Lemma 12.5.2(1–2), printed p.817/PDF p.834.
-/

@[expose] public section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.MiddleCore
open SL5TenDimensional
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi

/-- The last three coordinates of the 2+3 parabolic. -/
noncomputable def twoLargeHom : parabolic 2 →* SL(3, ZMod 2) :=
  (MonoidHom.snd SL(2, ZMod 2) SL(3, ZMod 2)).comp (parabolicLeviHom 2 (by decide))

/-- The first three coordinates of the 3+2 parabolic. -/
noncomputable def threeLargeHom : parabolic 3 →* SL(3, ZMod 2) :=
  (MonoidHom.fst SL(3, ZMod 2) SL(2, ZMod 2)).comp (parabolicLeviHom 3 (by decide))

/-- The marked large block on H₂. -/
noncomputable def twoFlagHom : twoFlag →* SL(3, ZMod 2) :=
  twoLargeHom.comp (Subgroup.inclusion twoFlag_le)

/-- The marked large block on H₃. -/
noncomputable def threeFlagHom : threeFlag →* SL(3, ZMod 2) :=
  threeLargeHom.comp (Subgroup.inclusion threeFlag_le)

/-- The same large block restricted to the actual small-block kernel. -/
noncomputable def twoResidualHom : parabolicTwoLargeBlock →* SL(3, ZMod 2) :=
  twoLargeHom.comp (Subgroup.inclusion parabolicTwoLargeBlock_le)

/-- The reversed-block version. -/
noncomputable def threeResidualHom : parabolicThreeLargeBlock →* SL(3, ZMod 2) :=
  threeLargeHom.comp (Subgroup.inclusion parabolicThreeLargeBlock_le)

theorem twoResidualHom_surjective : Function.Surjective twoResidualHom := by
  intro a
  obtain ⟨g, hg⟩ := parabolicLeviHom_surjective 2 (by decide) (1, a)
  have hm : g.val ∈ parabolicTwoLargeBlock :=
    ⟨g, congrArg Prod.fst hg, rfl⟩
  exact ⟨⟨g.val, hm⟩, congrArg Prod.snd hg⟩

theorem threeResidualHom_surjective : Function.Surjective threeResidualHom := by
  intro a
  obtain ⟨g, hg⟩ := parabolicLeviHom_surjective 3 (by decide) (a, 1)
  have hm : g.val ∈ parabolicThreeLargeBlock :=
    ⟨g, congrArg Prod.snd hg, rfl⟩
  exact ⟨⟨g.val, hm⟩, congrArg Prod.fst hg⟩

theorem twoFlagHom_surjective : Function.Surjective twoFlagHom := by
  intro a
  obtain ⟨g, hg⟩ := twoResidualHom_surjective a
  exact ⟨Subgroup.inclusion (show parabolicTwoLargeBlock ≤ twoFlag from le_sup_left) g, hg⟩

theorem threeFlagHom_surjective : Function.Surjective threeFlagHom := by
  intro a
  obtain ⟨g, hg⟩ := threeResidualHom_surjective a
  exact ⟨Subgroup.inclusion (show parabolicThreeLargeBlock ≤ threeFlag from le_sup_left) g, hg⟩

private theorem large_kernel_isPGroup {X Y A B : Type*}
    [Group X] [Group Y] [Group A] [Group B]
    (f : X →* A × B) (hk : IsPGroup 2 f.ker)
    (u : Subgroup A) (hu : IsPGroup 2 u)
    (i : Y →* X) (hi : Function.Injective i)
    (hs : ∀ y, (f (i y)).1 ∈ u) :
    IsPGroup 2 ((MonoidHom.snd A B).comp (f.comp i)).ker := by
  have hup : IsPGroup 2 (u.prod (⊥ : Subgroup B)) := by
    intro x
    obtain ⟨n, hn⟩ := hu ⟨x.val.1, x.property.1⟩
    refine ⟨n, Subtype.ext (Prod.ext (congrArg Subtype.val hn) ?_)⟩
    have hx : x.val.2 = 1 := x.property.2
    change x.val.2 ^ 2 ^ n = 1
    rw [hx, one_pow]
  have hp := (hup.comap_of_ker_isPGroup f hk).comap_of_injective i hi
  apply hp.to_le
  intro y hy
  exact ⟨hs y, hy⟩

private theorem slThree_twoCore : pCore 2 SL(3, ZMod 2) = ⊥ := by
  apply Subgroup.map_injective (f := (slEquivLinear 3).toMonoidHom)
    (slEquivLinear 3).injective
  rw [pCore_map_iso, linearGroup_twoCore_eq_bot, Subgroup.map_bot]

theorem twoFlagHom_ker_isPGroup : IsPGroup 2 twoFlagHom.ker := by
  apply large_kernel_isPGroup (parabolicLeviHom 2 (by decide))
    (by rw [parabolicLeviHom_ker]; exact pCore_isPGroup) smallUnipotent
    (Theory.SpecificGroups.LinearSylowNormalizers.unipotent_isPGroup 2 (ZMod 2) (by decide))
    (Subgroup.inclusion twoFlag_le) (Subgroup.inclusion_injective twoFlag_le)
  intro g
  exact (mem_twoFlag _).mp g.property

theorem threeFlagHom_ker_isPGroup : IsPGroup 2 threeFlagHom.ker := by
  let f := (MulEquiv.prodComm : (SL(3, ZMod 2) × SL(2, ZMod 2)) ≃* _).toMonoidHom.comp
    (parabolicLeviHom 3 (by decide))
  have hk : f.ker = (parabolicLeviHom 3 (by decide)).ker := by
    ext g
    change (parabolicLeviHom 3 (by decide) g).swap = 1 ↔
      parabolicLeviHom 3 (by decide) g = 1
    constructor <;> intro h
    · exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  apply large_kernel_isPGroup f
    (by rw [hk, parabolicLeviHom_ker]; exact pCore_isPGroup) smallUnipotent
    (Theory.SpecificGroups.LinearSylowNormalizers.unipotent_isPGroup 2 (ZMod 2) (by decide))
    (Subgroup.inclusion threeFlag_le) (Subgroup.inclusion_injective threeFlag_le)
  intro g
  exact (mem_threeFlag _).mp g.property

theorem twoFlagHom_ker : twoFlagHom.ker = pCore 2 twoFlag := by
  have h := twoFlagHom.comap_pCore_of_ker_isPGroup
    twoFlagHom_surjective twoFlagHom_ker_isPGroup
  rwa [slThree_twoCore] at h

theorem threeFlagHom_ker : threeFlagHom.ker = pCore 2 threeFlag := by
  have h := threeFlagHom.comap_pCore_of_ker_isPGroup
    threeFlagHom_surjective threeFlagHom_ker_isPGroup
  rwa [slThree_twoCore] at h

/-- The actual H₂/O₂(H₂), with its last-three-coordinate marking. -/
noncomputable def twoFlagQuotientEquiv :
    (twoFlag ⧸ pCore 2 twoFlag) ≃* SL(3, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq twoFlagHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective twoFlagHom twoFlagHom_surjective)

/-- The actual H₃/O₂(H₃), with its first-three-coordinate marking. -/
noncomputable def threeFlagQuotientEquiv :
    (threeFlag ⧸ pCore 2 threeFlag) ≃* SL(3, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq threeFlagHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective threeFlagHom threeFlagHom_surjective)

@[simp] theorem twoFlagQuotientEquiv_mk (g : twoFlag) :
    twoFlagQuotientEquiv (QuotientGroup.mk' _ g) = twoFlagHom g := rfl

@[simp] theorem threeFlagQuotientEquiv_mk (g : threeFlag) :
    threeFlagQuotientEquiv (QuotientGroup.mk' _ g) = threeFlagHom g := rfl

theorem twoFlagHom_entry (g : twoFlag) (i j : Fin 3) :
    (twoFlagHom g).val i j = g.val.val ⟨2+i.val, by omega⟩ ⟨2+j.val, by omega⟩ :=
  parabolicLeviHom_snd_entry 2 (by decide) (Subgroup.inclusion twoFlag_le g) i j

theorem threeFlagHom_entry (g : threeFlag) (i j : Fin 3) :
    (threeFlagHom g).val i j = g.val.val (Fin.castLE (by decide) i)
      (Fin.castLE (by decide) j) :=
  parabolicLeviHom_fst_entry 3 (by decide) (Subgroup.inclusion threeFlag_le g) i j

/-- The embedded radical, including the small unitriangular block. -/
noncomputable def twoRadical : Subgroup Group :=
  (smallUnipotent.prod (⊥ : Subgroup SL(3, ZMod 2))).comap
    (parabolicLeviHom 2 (by decide)) |>.map (parabolic 2).subtype

/-- The embedded radical in the 3+2 orientation. -/
noncomputable def threeRadical : Subgroup Group :=
  ((⊥ : Subgroup SL(3, ZMod 2)).prod smallUnipotent).comap
    (parabolicLeviHom 3 (by decide)) |>.map (parabolic 3).subtype

theorem twoCore_map : (pCore 2 twoFlag).map twoFlag.subtype = twoRadical := by
  rw [← twoFlagHom_ker]
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨Subgroup.inclusion twoFlag_le g, ⟨(mem_twoFlag _).mp g.property, hg⟩, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g.val, (mem_twoFlag g).mpr hg.1⟩, hg.2, rfl⟩

theorem threeCore_map : (pCore 2 threeFlag).map threeFlag.subtype = threeRadical := by
  rw [← threeFlagHom_ker]
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨Subgroup.inclusion threeFlag_le g, ⟨hg, (mem_threeFlag _).mp g.property⟩, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g.val, (mem_threeFlag g).mpr hg.2⟩, hg.1, rfl⟩

end Representation.SL5ExteriorSquare.MiddleCore
