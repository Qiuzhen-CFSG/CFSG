module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Spaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Complements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Normalizers

/-!
# A Cartan-compatible opposite point in the original central quotient

Maschke over the specified binary field gives an X-invariant line
complementing the original three-space. An explicit element of the
point radical sends the standard opposite line to this complement
while preserving the entire marked flag. Lifting the resulting
opposition through the original L/O₂(L) map produces y in L.

The same y has the previously proved SL₂ pair image, complementary
quotient spaces, denominator containment, and three L₁ conjugators.
The full source Cartan normalizes its opposite point and its core pair.
Containment X₁≤I and the natural-module calculation on Q/N are
separate obligations retained by the opposite-core assembly.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open LocalGeometry

private theorem radical_preserves_stage {F : Type*} [Field F] [Finite F] [CharP F 2]
    (u v z : F) (i : Fin 3) :
    (Sp4.ModelFlag.stage (F := F) i.succ).map
        (toLinear (pointRadicalElement u v z).val).toLinearMap =
      Sp4.ModelFlag.stage i.succ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro x ⟨w,hw,rfl⟩
    fin_cases i
    · change (pointRadicalElement u v z).val • w ∈ point F
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
      change toLinear _ (a • e 0) ∈ _
      rw [map_smul]
      change a • ((pointRadicalElement u v z).val • e 0) ∈ _
      rw [(mem_pointLocal_iff_fixed _).mp (pointRadicalElement u v z).property]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · change (pointRadicalElement u v z).val • w ∈ plane F
      intro j
      fin_cases j <;>
        simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
          dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,show w (.inr 0) = 0 from hw 0,
          show w (.inr 1) = 0 from hw 1]
    · apply (Sp4.ModelFlag.mem_hyperplane _).mpr
      have hw0 := (Sp4.ModelFlag.mem_hyperplane w).mp hw
      simp [toLinear_apply,pointRadicalElement,pointRadicalMatrix,
        Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,hw0]
  · exact (toLinear _).finrank_map_eq _

private theorem opposition_point {F : Type*} [Field F] [CharP F 2] :
    (TwoConjugate.opposition (F := F)) • e 0 = (Pi.single (.inr 0) 1 : Theory.SpecificGroups.SymplecticFour.Vector F) := by
  rw [TwoConjugate.opposition_apply]
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e]

private theorem radical_opposite {F : Type*} [Field F] [CharP F 2]
    (u v z : F) :
    (pointRadicalElement u v z).val • (Pi.single (.inr 0) 1 : Vector F) =
      Sum.elim ![z,u] ![1,v] := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single]

private theorem moved_opposite_point {F : Type*} [Field F] [CharP F 2]
    (g : Sp F) :
    ((point F).map (toLinear TwoConjugate.opposition).toLinearMap).map
        (toLinear g).toLinearMap = F ∙ (g • ((TwoConjugate.opposition (F := F)) • e 0)) := by
  rw [point,Submodule.map_span,Set.image_singleton,Submodule.map_span,Set.image_singleton]
  rfl

/-- A complement of the marked three-space is reached by a point-radical
change of frame, preserving all three members of the original flag. -/
theorem complement_frame {F : Type*} [Field F] [Finite F] [CharP F 2]
    (g : Sp F) (U : Submodule F (Vector F))
    (hU : IsCompl (Sp4.ModelFlag.movedStage g 3) U) :
    ∃ g' : Sp F,
      (∀ i : Fin 3, Sp4.ModelFlag.movedStage g' i.succ =
        Sp4.ModelFlag.movedStage g i.succ) ∧
      ((point F).map (toLinear TwoConjugate.opposition).toLinearMap).map
        (toLinear g').toLinearMap = U := by
  have hd : Module.finrank F U = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Sp4.ModelFlag.movedStage g 3) U
    rw [hU.sup_eq_top,hU.inf_eq_bot,finrank_bot,finrank_top,
      Sp4.ModelFlag.movedStage_dimension] at h
    have hdim : Module.finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hdim] at h
    omega
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show U ≠ ⊥ from by
    intro he; rw [he,finrank_bot] at hd; omega)
  let a := g⁻¹ • w
  have ha : a (.inr 0) ≠ 0 := by
    intro hz
    have hg : w ∈ Sp4.ModelFlag.movedStage g 3 := by
      rw [Sp4.ModelFlag.mem_movedStage]
      exact (Sp4.ModelFlag.mem_hyperplane _).mpr hz
    exact hw0 (hU.disjoint.le_bot ⟨hg,hw⟩)
  let r := pointRadicalElement ((a (.inr 0))⁻¹ * a (.inl 1))
    ((a (.inr 0))⁻¹ * a (.inr 1)) ((a (.inr 0))⁻¹ * a (.inl 0))
  refine ⟨g * r.val, ?_, ?_⟩
  · intro i
    change (Sp4.ModelFlag.stage i.succ).map (toLinear (g * r.val)).toLinearMap = _
    have he : (toLinear (g * r.val)).toLinearMap =
        (toLinear g).toLinearMap.comp (toLinear r.val).toLinearMap := by
      apply LinearMap.ext
      intro v
      change (g * r.val) • v = g • (r.val • v)
      exact mul_smul g r.val v
    rw [he,Submodule.map_comp,radical_preserves_stage]
    rfl
  · have he : (g * r.val) • ((TwoConjugate.opposition (F := F)) • e 0) =
        (a (.inr 0))⁻¹ • w := by
      rw [opposition_point,mul_smul]
      have hr : r.val • Pi.single (.inr 0) 1 = (a (.inr 0))⁻¹ • a := by
        change (pointRadicalElement _ _ _).val • _ = _
        rw [radical_opposite]
        ext i
        rcases i with i | i <;> fin_cases i <;> simp [ha]
      rw [hr]
      change toLinear g ((a (.inr 0))⁻¹ • a) = _
      rw [map_smul]
      change (a (.inr 0))⁻¹ • (g • (g⁻¹ • w)) = _
      rw [smul_inv_smul]
    rw [moved_opposite_point]
    rw [he,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero ha))]
    exact (eq_span_singleton_of_mem_of_finrank_eq_one hd hw hw0).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The literal source Cartan preserves the supplied marked flag. -/
theorem cartan_normalizes_marked_flag (m : MarkedFlag E)
    (hX : IsCartan T L E.X) (i : Fin 3) : E.X ≤ normalizer (m.flag.Vi i : Set G) := by
  apply m.flag.cartan_normalizes _ hX i
  intro j U hd hn
  exact (Sp4.space_inner_unique m.action j U hd hn).trans (flag_space_alignment E m j).symm

/-- Maschke supplies a Cartan-invariant field line complementary to the
original three-space, with normalization on its literal ambient preimage. -/
theorem exists_cartan_complement (m : MarkedFlag E) (hX : IsCartan T L E.X) :
    ∃ U : Submodule E.input.field.Carrier (Vector E.input.field.Carrier),
      IsCompl (m.flag.space 2) U ∧ E.X ≤ normalizer
        ((Coordinates.sp4 m.action).preimage U : Set G) := by
  let c := Coordinates.sp4 m.action
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  let ρ := c.modelAction.comp (c.quotientMap.comp (inclusion hXL))
  have hU : ∀ x : E.X, ∀ u ∈ m.flag.space 2, ρ x u ∈ m.flag.space 2 := by
    intro x u hu
    exact ((c.mem_normalizer_preimage_iff (m.flag.space 2) (inclusion hXL x)).mp
      (cartan_normalizes_marked_flag E m hX 2 x.property) u).mpr hu
  obtain ⟨U,hc,hU⟩ := ShadowReduction.CompatibleCartan.exists_invariant_field_complement
    hX.odd ρ (m.flag.space 2) hU
  refine ⟨U,hc,?_⟩
  intro x hx
  apply (c.mem_normalizer_preimage_iff U (inclusion hXL ⟨x,hx⟩)).mpr
  intro u
  constructor
  · intro hu
    have hh := hU (⟨x,hx⟩ : E.X)⁻¹ _ hu
    change ρ (⟨x,hx⟩ : E.X)⁻¹ (ρ ⟨x,hx⟩ u) ∈ U at hh
    simpa only [Representation.inv_self_apply] using hh
  · exact hU ⟨x,hx⟩ u

/-- Select an opposite lift while keeping the full original flag and making
its opposite point invariant under the actual Cartan. -/
theorem exists_cartan_opposition_lift (m : MarkedFlag E) (hX : IsCartan T L E.X) :
    ∃ (g : Sp E.input.field.Carrier) (y : L),
      (∀ i : Fin 3, m.flag.space i = Sp4.ModelFlag.movedStage g i.succ) ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      E.X ≤ normalizer (E.V₁.map (MulAut.conj (y : G)).toMonoidHom : Set G) := by
  obtain ⟨U,hU,hn⟩ := exists_cartan_complement E m hX
  let g₀ := Sp4.alignment m.action
  have hf := flag_space_alignment E m
  obtain ⟨g,hg,he⟩ := complement_frame g₀ U (by
    change IsCompl (Sp4.ModelFlag.movedStage (Sp4.alignment m.action) (Fin.succ 2)) U
    rw [← hf 2]
    exact hU)
  have hflag (i : Fin 3) : m.flag.space i = Sp4.ModelFlag.movedStage g i.succ :=
    (hf i).trans (hg i).symm
  have hs : Function.Surjective (PointModel.quotientMap m) :=
    m.action.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  obtain ⟨y,hy⟩ := hs (g * TwoConjugate.opposition * g⁻¹)
  refine ⟨g,y,hflag,hy,?_⟩
  let c := Coordinates.sp4 m.action
  have hpoint : E.V₁.map (MulAut.conj (y : G)).toMonoidHom = c.preimage U := by
    rw [m.point_preimage]
    change (c.preimage (m.flag.space 0)).map _ = _
    rw [← c.preimage_map_action]
    congr 1
    have hmap : ((m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap) =
        ((point E.input.field.Carrier).map (toLinear TwoConjugate.opposition).toLinearMap).map
          (toLinear g).toLinearMap := by
      rw [hflag 0,hy]
      change ((point E.input.field.Carrier).map (toLinear g).toLinearMap).map _ = _
      rw [← Submodule.map_comp,← Submodule.map_comp]
      congr 1
      apply LinearMap.ext
      intro v
      change (g * TwoConjugate.opposition * g⁻¹) • (g • v) =
        g • ((TwoConjugate.opposition (F := E.input.field.Carrier)) • v)
      simp only [mul_smul,inv_smul_smul]
    exact hmap.trans he
  rwa [hpoint]

/-- The opposite action, quotient spaces, and three source conjugators can
all be selected compatibly with the original Cartan. No containment of
X₁ or natural-module statement about Q/N is assumed here. -/
theorem exists_cartan_opposite_pair_geometry (m : MarkedFlag E)
    (hX : IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    ∃ (g : Sp E.input.field.Carrier) (y : L),
      (∀ i : Fin 3, m.flag.space i = Sp4.ModelFlag.movedStage g i.succ) ∧
      PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
          (FullAction.modelHom m) ∧
      E.X ≤ normalizer (E.V₁.map (MulAut.conj (y : G)).toMonoidHom : Set G) ∧
      E.X ≤ normalizer (corePair (auxiliaryW E) (y : G) : Set G) ∧
      IsCompl E.threeSpace (E.point.map (D.chosenCentralAction y)) ∧
      E.V₃ ⊔ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ∧
      E.V₃ ⊓ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ⊓ centralizer (L : Set G) ∧
      (oppositeJoin (auxiliaryW E) (y : G)).pCoreIn 2 ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      pairDenominator E (y : G) ≤ corePair (auxiliaryW E) (y : G) ∧
      ∃ l : Fin 3 → G, (∀ i, l i ∈ E.L₁) ∧
        L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) (y : G)).map
          (MulAut.conj (l i)).toMonoidHom) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨g,y,hflag,hy,hXpoint⟩ := exists_cartan_opposition_lift E m hX
  have hlocal := PointModel.local_identification m g (hflag 0)
  have hr := hroot.trans (FullAction.center_eq_marked_root m g hlocal)
  have hi := pair_image_of_opposition_lift E m hW g hr y hy
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact cartan_normalizes_marked_flag E m hX 0
  have hs := opposite_preimages E m g hflag y hy
  exact ⟨g,y,hflag,hlocal,hy,hi,hXpoint,
    NaturalQuotient.cartan_normalizes_corePair E y hXG hXpoint,
    opposite_quotient_spaces_complementary E m g hflag y hy,hs.1,hs.2,
    marked_pair_core_le_large_core E m hW y.property g hi,
    opposition_denominator_le_corePair E m hW hPhi g hflag y hy,
    three_conjugates_of_marked_pair E m hW y.property g hlocal hi⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
