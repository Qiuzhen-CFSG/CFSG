module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.SourceAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence

/-!
# Generation by the full G₂ plane family

The proved point-residual plane orbit lies in the original third preimage
and its relative residuals generate all of L, including the two-core kernel.
Enlarging to the full L-plane family preserves that generation. Both the
family and its local residuals are transported by the same ambient maps.
Thus every L-conjugate of the supplied third preimage has the required
generation property; no containment in another module is needed for this step.

One-sided inclusion in a conjugate plane family suffices to identify the
components by 11.1.3. It gives L ≤ Lᵍ, and equal orders give equality. The
last theorem applies this to the actual zeroth weak closure. Its reciprocal
full-plane inclusion remains explicit and must still be proved by
qt-d-1222-natural-weak-closure-source, including recovery of the central
term identified by RootPullback. No central kernel is removed, and these
conditional consumers are not unconditional source 11.2.2(5).

Source: Aschbacher--Smith, 11.1.3--4 and 11.2.2(5), printed pp.765,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
variable {G : Type*} [Group G] [Finite G]

private theorem embeddedResidual_map (e : G ≃* G) (H : Subgroup G) :
    ((solvableResidual H).map H.subtype).map e.toMonoidHom =
      (solvableResidual (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype := by
  have he := congrArg (map (H.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq (e.subgroupMap H).toMonoidHom (e.subgroupMap H).surjective)
  rw [map_map] at he ⊢
  exact he

private theorem localResidual_map (e : G ≃* G) (L U : Subgroup G) :
    (localResidual L U).map e.toMonoidHom =
      localResidual (L.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  unfold localResidual
  rw [embeddedResidual_map, map_inf _ _ _ e.injective, map_equiv_normalizer_eq]

omit [Finite G] in
private theorem planeFamily_map_mem (e : G ≃* G) {L P U I : Subgroup G}
    (hI : I ∈ planeFamily L P U) :
    I.map e.toMonoidHom ∈ planeFamily (L.map e.toMonoidHom)
      (P.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  obtain ⟨hIU,l,rfl⟩ := hI
  refine ⟨map_mono hIU,⟨e l,mem_map_of_mem _ l.property⟩,?_⟩
  rw [map_map,map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
    map_mul,map_inv]

/-- Generation transports along the literal ambient automorphism and full preimages. -/
theorem planeFamily_generation_map (e : G ≃* G) {L P U : Subgroup G}
    (hgen : planeResidualSpan L (planeFamily L P U) = L) :
    planeResidualSpan (L.map e.toMonoidHom)
      (planeFamily (L.map e.toMonoidHom) (P.map e.toMonoidHom) (U.map e.toMonoidHom)) =
      L.map e.toMonoidHom := by
  apply le_antisymm
  · exact iSup_le fun I => iSup_le fun _ => (localResidual_le I).trans inf_le_left
  · conv_lhs => rw [←hgen]
    unfold planeResidualSpan
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hI
    rw [localResidual_map]
    exact le_iSup_of_le (I.map e.toMonoidHom)
      (le_iSup_of_le (planeFamily_map_mem e hI) le_rfl)

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- The full original plane family generates L by its actual relative residuals. -/
theorem planeFamily_residuals_generate : planeResidualSpan L (planeFamily L (f.Vi 1) (f.Vi 2)) = L := by
  have hf (i : Fin 3) : f.Vi i = (LocalGeometry.G2.flag S m).Vi i := by
    exact congrArg (Coordinates.g2 m).preimage
      (LocalGeometry.G2.flag_unique S m i (f.space i) (f.dimension i) (f.invariant i))
  rw [hf 1,hf 2]
  apply le_antisymm
  · exact iSup_le fun I => iSup_le fun _ => (localResidual_le I).trans inf_le_left
  · conv_lhs => rw [LocalGeometry.G2.ResidualIncidence.planeOrbit_residuals_generate S m]
    apply iSup_le
    intro I
    have hIF : I.val ∈ planeFamily L ((LocalGeometry.G2.flag S m).Vi 1)
        ((LocalGeometry.G2.flag S m).Vi 2) := by
      obtain ⟨b,hb⟩ := I.property
      exact ⟨(LocalGeometry.G2.ResidualIncidence.planeOrbit_interval S m I.val I.property).2,
        ⟨b.val,(localResidual_le _ b.property).1⟩,hb⟩
    exact le_iSup_of_le I.val (le_iSup_of_le hIF le_rfl)

/-- Every L-conjugate of the full original third preimage has the same generation property. -/
theorem planeFamily_residuals_generate_conjugate (l : L) :
    planeResidualSpan L (planeFamily L (f.Vi 1)
      ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom)) = L := by
  have hgen := planeFamily_residuals_generate D S m f
  let e := MulAut.conj (l : G)
  have hL : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer l.property)
  have hh := planeFamily_generation_map e hgen
  rw [hL] at hh
  apply le_antisymm
  · exact iSup_le fun I => iSup_le fun _ => (localResidual_le I).trans inf_le_left
  · conv_lhs => rw [←hh]
    apply iSup_le
    intro I
    apply iSup_le
    rintro ⟨hIU,b,hb⟩
    have hIF : I ∈ planeFamily L (f.Vi 1) ((f.Vi 2).map e.toMonoidHom) := by
      refine ⟨hIU,b*l,?_⟩
      rw [hb,map_map]
      congr 1
      ext x
      change (b : G) * ((l : G) * x * (l : G)⁻¹) * (b : G)⁻¹ =
        ((b : G)*(l : G)) * x * ((b : G)*(l : G))⁻¹
      group
    exact le_iSup_of_le I (le_iSup_of_le hIF le_rfl)

/-- One-sided inclusion of the full plane family already reconstructs the
component; equal-order ambient conjugates make the reverse inclusion unnecessary. -/
theorem mem_normalizer_of_planeFamily_inclusion (g : G) (l : L)
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hplanes : planeFamily L (f.Vi 1) ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom) ⊆
      planeFamily (L.map (MulAut.conj g).toMonoidHom)
        ((f.Vi 1).map (MulAut.conj g).toMonoidHom)
        ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom)) :
    g ∈ normalizer (L : Set G) := by
  have hc := planeComponents_of_unique hcomponent
  have hle : L ≤ L.map (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [←planeFamily_residuals_generate_conjugate D S m f l]
    apply iSup_le
    intro I
    apply iSup_le
    intro hI
    have hc0 : Source.NoncentralComponent (normalizer (I : Set G)) I (localResidual L I) := by
      have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      have hI' : I ∈ planeFamily (L.map (MulAut.conj (1 : G)).toMonoidHom)
          ((f.Vi 1).map (MulAut.conj (1 : G)).toMonoidHom)
          ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom) := by
        simpa only [hone,map_id] using hI
      simpa only [hone,map_id] using (hc 1 _ I hI').1
    have he := (hc g _ I (hplanes hI)).2 _ hc0
    rw [he]
    exact (localResidual_le I).trans inf_le_left
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])).symm

/-- The actual zeroth weak-closure application. Reciprocal inclusion of the
full plane families is still an explicit obligation of this source owner. -/
theorem zero_centralizes_of_planeFamily_inclusions
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hplanes : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      ∃ l : L, planeFamily L (f.Vi 1) ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom) ⊆
        planeFamily (L.map (MulAut.conj g).toMonoidHom)
          ((f.Vi 1).map (MulAut.conj g).toMonoidHom)
          ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom)) :
    ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  refine le_inf (ChapterE.indexedWeakClosure_le V (T : Subgroup G) 0) ?_
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hg⟩ := (ChapterE.mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra hnon
  obtain ⟨l,hl⟩ := hplanes g hg hnon
  have hgM := mem_normalizer_of_planeFamily_inclusion D S m f g l hcomponent hl
  let W := componentOrbit V (normalizer (L : Set G))
  let : IsElementaryAbelian 2 W := Preliminary.fullModule_elementary D S
  have hVW : V ≤ W := le_componentOrbit V _
  have hAW : V.map (MulAut.conj g).toMonoidHom ≤ W :=
    le_iSup_of_le (⟨g,hgM⟩ : normalizer (L : Set G)) le_rfl
  exact hnon (hAW.trans ((Subgroup.le_centralizer W).trans (Subgroup.centralizer_le hVW)))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
