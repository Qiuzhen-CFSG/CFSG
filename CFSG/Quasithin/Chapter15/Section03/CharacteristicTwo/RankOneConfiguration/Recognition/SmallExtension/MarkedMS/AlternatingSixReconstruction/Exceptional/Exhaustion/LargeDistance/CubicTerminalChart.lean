module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEvenComplete
public import Theory.Representation.Quotient

/-!
# Literal terminal actors at arbitrary original vertices

A source chart transports M isomorphically onto the actual stabilizer.
The six-letter projection then has the transported E-kernel, whose index
over the original neighborhood two-core is still three. Its residual
image is A₆. An action on the literal moving central quotient descends
through this projection precisely after the supplied raw E-commutator
centralization makes that kernel act trivially.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalChart
open NaturalStructure.Exclusion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
  {a : Vertex (edge L R)} (c : CubicEven.Chart (L := L) (R := R) a)
local notation "S" => stabilizer T a

/-- A source chart identifies M with the literal vertex stabilizer. -/
@[expose] def equivalence : M ≃* S :=
  (MonoidHom.ofInjective c.injective).trans (MulEquiv.subgroupCongr c.range_eq)

omit [Finite G] in
theorem equivalence_apply (x : M) :
    (equivalence c x : FreeAmalgam T) = c.embedding x := rfl

omit [Finite G] in
private theorem equivalence_map (A : Subgroup M) :
    A.map (equivalence c).toMonoidHom = (A.map c.embedding).subgroupOf S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (equivalence_apply c y).symm⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, Subtype.ext ((equivalence_apply c y).trans hyx)⟩

/-- The actual six-letter projection in the given source chart. -/
@[expose] def projection : S →* Equiv.Perm (Fin 6) :=
  (CubicAction.projection h e hz hk).comp (equivalence c).symm.toMonoidHom

theorem projection_surjective : Function.Surjective (projection h e hz hk c) :=
  (CubicEven.projection_surjective h e hz hk).comp (equivalence c).symm.surjective

theorem projection_kernel :
    (projection h e hz hk c).ker = (c.kernel h).subgroupOf S := by
  rw [projection, ← MonoidHom.comap_ker, CubicAction.projection_kernel,
    comap_equiv_eq_map_symm', MulEquiv.symm_symm, equivalence_map]
  rfl

theorem projection_residual_image :
    (pResidual 2 S).map (projection h e hz hk c) = alternatingGroup (Fin 6) := by
  let : Finite S := Finite.of_equiv M (equivalence c).toEquiv
  rw [projection, ← map_map,
    map_pResidual_of_surjective 2 (equivalence c).symm.toMonoidHom
      (equivalence c).symm.surjective, h.relative_residual,
    CubicAction.component_image]

theorem core_le_projection_kernel (ha : color T a = false) :
    (Q T a).subgroupOf S ≤ (projection h e hz hk c).ker := by
  rw [projection_kernel]
  apply comap_mono
  rw [← c.map_Q h ha]
  exact map_mono le_sup_right

/-- The actual kernel retains its nontrivial cubic quotient above Q. -/
theorem projection_kernel_core_index (ha : color T a = false) :
    ((Q T a).subgroupOf S).relIndex (projection h e hz hk c).ker = 3 := by
  have hES : c.kernel h ≤ S := (map_le_range _ _).trans_eq c.range_eq
  rw [projection_kernel, relIndex_subgroupOf hES, ← c.map_Q h ha,
    CubicEven.Chart.kernel, relIndex_map_map_of_injective _ _ c.injective]
  change ((pCore 2 M).subgroupOf (extensionKernel h)).index = 3
  have he : pCore 2 (extensionKernel h) =
      (pCore 2 M).subgroupOf (extensionKernel h) :=
    pCore_subnormal_eq_comap 2 (inferInstance : (extensionKernel h).Normal).isSubnormal
  rw [← he]
  exact extensionKernel_core_index h hz

theorem projection_kernel_core_odd (ha : color T a = false) :
    Odd (((Q T a).subgroupOf S).relIndex (projection h e hz hk c).ker) := by
  rw [projection_kernel_core_index h e hz hk c ha]
  decide

omit [Finite G] in
private theorem moving_kernel_of_central
    (hc : ⁅Vcirc T a, c.kernel h⁆ ≤ centralizer (Vcirc T a : Set (FreeAmalgam T))) :
    (c.kernel h).subgroupOf S ≤ (movingQuotientAction a).ker := by
  intro g hg
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center (Vcirc T a)) v
  rw [movingQuotientAction_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  change (y : FreeAmalgam T) * ((g : FreeAmalgam T) * (x : FreeAmalgam T) *
    (g : FreeAmalgam T)⁻¹ / (x : FreeAmalgam T)) = _
  rw [commutator_comm] at hc
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.coe_mul,
    Subgroup.coe_inv, movingAction_apply, Subgroup.subtype_apply] using
    hc (commutator_mem_commutator hg x.property) y y.property

/-- Actual E-centralization gives descent on the unchanged moving quotient. -/
theorem exists_moving_descent
    (hc : ⁅Vcirc T a, c.kernel h⁆ ≤ centralizer (Vcirc T a : Set (FreeAmalgam T)))
    (he : IsElementaryAbelian 2 ((Vcirc T a) ⧸ center (Vcirc T a))) :
    letI := he
    ∃ σ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
        (Additive ((Vcirc T a) ⧸ center (Vcirc T a))),
      σ.comp (projection h e hz hk c) = Offenders.linearize (movingQuotientAction a) := by
  let := he
  let ρ := Offenders.linearize (movingQuotientAction a)
  let π := projection h e hz hk c
  have hkerAct : π.ker ≤ (movingQuotientAction a).ker := by
    rw [projection_kernel]
    exact moving_kernel_of_central h c hc
  have hker : π.ker ≤ ρ.ker := by
    intro g hg
    have hg' := MonoidHom.mem_ker.mp (hkerAct hg)
    apply LinearMap.ext
    intro v
    change Additive.ofMul (movingQuotientAction a g v.toMul) = v
    rw [hg']
    rfl
  let f := QuotientGroup.quotientKerEquivOfSurjective π
    (projection_surjective h e hz hk c)
  let σ := (quotientOfLEKer ρ π.ker hker).comp f.symm.toMonoidHom
  refine ⟨σ, MonoidHom.ext (fun g => ?_)⟩
  change quotientOfLEKer ρ π.ker hker
    (f.symm (f (QuotientGroup.mk' π.ker g))) = ρ g
  rw [f.symm_apply_apply]
  rfl

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalChart
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
