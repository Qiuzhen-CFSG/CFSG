module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.Tits.RelativeSylowMarking
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.ComponentRank

/-!
# Concrete Ree carriers and generating full parabolics in E.6.8

The LocalBlockInput equivalence retains the actual fixed matrices. Sylow
conjugacy aligns the component intersection with the standard positive subgroup,
and the full parabolics retain their complementary torus. Fixed Bruhat coverage
and the two Weyl lifts prove that these parabolics generate the whole carrier.

The checked Tits subgroup embeds through the binary coefficient field. Its
centerlessness and three-rank two force Q to normalize the Ree component,
using local quasithinness. This does not require simplicity or an order formula
for the Ree group. Automorphism invariance and the intrinsic local core/block
calculations for the full Ree parabolics remain for the final family assembly.

Source: Aschbacher–Smith E.6.8, printed pp.247–248 (PDF pp.258–259);
GLS3 §§2.3 and 2.6 for the full parabolics and subfield construction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
open ReeF4
open LargeLocalSeeds

/-- The two full parabolics generate the actual fixed-point group. -/
theorem ree_full_parabolics_generate (m : ℕ) :
    ConverseParabolics.parabolic m .suzuki ⊔ ConverseParabolics.parabolic m .linear = ⊤ := by
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic,
    MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic]
  apply top_unique
  rw [← SectionGeometry.BNPair.borel_sup_normalizerWords m]
  have hB : Parabolics.borel m ≤ Parabolics.parabolic m .suzuki ⊔
      Parabolics.parabolic m .linear := (Parabolics.borel_le_parabolic m .suzuki).trans le_sup_left
  refine sup_le hB ((SectionGeometry.BNPair.normalizerWords_le_fixedTorus_sup_weylSubgroup m).trans
    (sup_le ?_ ?_))
  · exact (show Parabolics.fixedTorus m ≤ Parabolics.borel m from comap_mono le_sup_right).trans hB
  · exact (Parabolics.Binary.FixedGeometry.weylSubgroup_le_seeds m).trans
      (sup_le_sup (Parabolics.seed_le_parabolic m .suzuki) (Parabolics.seed_le_parabolic m .linear))

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- Convert the exact local-block carrier and align the actual component Sylow. -/
theorem ree_sylow_marking (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) {m : ℕ}
    (hm : Chapter1.Section02.LocalModels.IsReeF4At L m) :
    ∃ e : L ≃* Model m,
      (Q.subgroupOf L).map e.toMonoidHom = ConverseParabolics.unipotent m := by
  obtain ⟨d, ⟨e⟩⟩ := hm
  let f := e.trans d.modelEquiv
  obtain ⟨R, hR⟩ := component_sylow_intersection h hU hL
  rw [← hQ] at hR
  have hR' : (R : Subgroup L) = Q.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hR, subgroupOf_map_subtype, inf_comm]
  obtain ⟨S, hS⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  let R' := R.mapSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) R' S
  refine ⟨f.trans (MulAut.conj g), ?_⟩
  rw [← hR']
  change (R : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp f.toMonoidHom) = _
  rw [← map_map]
  change (R' : Subgroup (Model m)).map (MulAut.conj g).toMonoidHom = _
  rw [← hS, ← hg, Sylow.coe_subgroup_smul, pointwise_smul_def]
  rfl

/-- Full parabolics, including the complementary torus, on the original component. -/
def reeParabolic {m : ℕ} (e : L ≃* Model m) (s : Side) : Subgroup L :=
  (ConverseParabolics.parabolic m s).map e.symm.toMonoidHom

omit [Finite G] in
theorem reeParabolic_generate {m : ℕ} (e : L ≃* Model m) :
    reeParabolic e .suzuki ⊔ reeParabolic e .linear = ⊤ := by
  rw [reeParabolic, reeParabolic, ← Subgroup.map_sup, ree_full_parabolics_generate,
    map_top_of_surjective _ e.symm.surjective]

omit [Finite G] in
/-- The marking preserves the inclusion of the supplied component Sylow in each parabolic. -/
theorem reeParabolic_sylow_le {m : ℕ} (e : L ≃* Model m)
    (he : (Q.subgroupOf L).map e.toMonoidHom = ConverseParabolics.unipotent m)
    (s : Side) : Q.subgroupOf L ≤ reeParabolic e s := by
  intro x hx
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  apply ConverseParabolics.unipotent_le_parabolic
  rw [← he]
  exact mem_map_of_mem _ hx


/-- The embedded binary Tits group forces the Ree component to be normalized
by Q. No simplicity or order assertion about the Ree model is an extra input. -/
theorem ree_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) {m : ℕ}
    (hm : Chapter1.Section02.LocalModels.IsReeF4At L m) : Q ≤ normalizer (L : Set G) := by
  obtain ⟨d, ⟨e⟩⟩ := hm
  let j := e.trans d.modelEquiv
  obtain ⟨f, hf⟩ := Subfield.exists_tits_embedding m
  let fL : Tits.Atlas1600Group →* L := j.symm.toMonoidHom.comp
    (f.comp Tits.parrottFiniteImageEquiv.symm.toMonoidHom)
  have hfL : Function.Injective fL :=
    j.symm.injective.comp (hf.comp Tits.parrottFiniteImageEquiv.symm.injective)
  exact normalizes_of_centerless_embedding h hU hL hQ fL hfL
    Tits.RelativeSylowMarking.atlas_center_eq_bot 3 (by decide) Tits.ThreeRank.rank_two_le

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
