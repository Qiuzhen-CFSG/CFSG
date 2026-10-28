module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Hitting
/-!
# The outside-line pencil in a native sextet

Octads of one sextet have intersection size divisible by four. A small
checked calculation excludes coplanarity away from the shared-octad pencil
for the outside-trio representative. The existing exhaustive trio forest
and the literal sextet conjugator transport the statement to every flag.
This is the pencil assertion in AS91 (3.10), used for the two ovals and the
common-neighbor bound in (7.4). No orbital or contraction premise is added.

Source: Aschbacher–Segev (1991), (3.10), (7.4), pp.596,603–604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Theory.SpecificGroups.SymmetricSix
open scoped Pointwise

theorem tetradUnion_inter (π : Plane) (e : Fin 6 ≃ {A // A ∈ π.parts})
    (s t : Finset (Fin 6)) :
    tetradUnion π e s ∩ tetradUnion π e t = tetradUnion π e (s ∩ t) := by
  ext u
  simp only [tetradUnion, Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i,hi,hui⟩,j,hj,huj⟩
    have hij : i = j := by
      by_contra hn
      exact Finset.disjoint_left.mp (π.disjoint _ (e i).property _ (e j).property
        (fun he => hn (e.injective (Subtype.ext he)))) hui huj
    exact ⟨i,⟨hi,hij.symm ▸ hj⟩,hui⟩
  · rintro ⟨i,⟨hi,hj⟩,hui⟩
    exact ⟨⟨i,hi,hui⟩,i,hj,hui⟩

theorem tetradUnion_card (π : Plane) (e : Fin 6 ≃ {A // A ∈ π.parts})
    (s : Finset (Fin 6)) : (tetradUnion π e s).card = s.card * 4 := by
  rw [tetradUnion, Finset.card_biUnion]
  · simp only [π.tetrad _ (e _).property, Finset.sum_const, smul_eq_mul]
  · intro i hi j hj hij
    exact π.disjoint _ (e i).property _ (e j).property
      (fun he => hij (e.injective (Subtype.ext he)))

theorem planeOctad_inter_four_dvd {π : Plane} {A B : Finset (Fin 24)}
    (hA : PlaneOctad π A) (hB : PlaneOctad π B) : 4 ∣ (A ∩ B).card := by
  classical
  let e : Fin 6 ≃ {A // A ∈ π.parts} :=
    (Fintype.equivFinOfCardEq (by simpa using π.card)).symm
  obtain ⟨a,rfl⟩ := planeOctad_duad π e hA
  obtain ⟨b,rfl⟩ := planeOctad_duad π e hB
  rw [duadOctad,duadOctad,tetradUnion_inter,tetradUnion_card]
  exact dvd_mul_left _ _

theorem not_coplanar_of_inter_two {l m : Line} {A B : Finset (Fin 24)}
    (hA : A ∈ l.parts) (hB : B ∈ m.parts) (hcard : (A ∩ B).card = 2) :
    ¬ Coplanar l m := by
  rintro ⟨π,hl,hm⟩
  have hd := planeOctad_inter_four_dvd (hl A hA) (hm B hB)
  rw [hcard] at hd
  norm_num at hd

/-- An outside trio sees only the three trios containing one specified octad. -/
def OutsidePencil (π : Plane) (b : Line) : Prop :=
  ∃ A ∈ b.parts, PlaneOctad π A ∧
    ∀ l, Incident l π → Coplanar b l → A ∈ l.parts

theorem outsidePencil_transport (g : M24) {π σ : Plane} {b c : Line}
    (hπ : σ.parts = g • π.parts) (hb : c.parts = g • b.parts)
    (hp : OutsidePencil π b) : OutsidePencil σ c := by
  obtain ⟨A,hAb,hA,hit⟩ := hp
  refine ⟨g • A,hb.symm ▸ Finset.smul_mem_smul_finset hAb,
    planeOctad_transport g hπ hA,?_⟩
  intro l hl hbl
  have hi : Incident (g⁻¹ • l) π := incident_transport g⁻¹ rfl
    (by rw [hπ,inv_smul_smul]) hl
  have hc : Coplanar b (g⁻¹ • l) := coplanar_transport g⁻¹
    (by rw [hb,inv_smul_smul]) rfl hbl
  simpa only [smulLine_parts,smul_inv_smul] using
    Finset.smul_mem_smul_finset (a := g) (hit _ hi hc)

namespace PlanePencil
noncomputable def labels : Fin 6 ≃ {A // A ∈ standardSextet.parts} :=
  Equiv.ofBijective (fun i => ⟨standardTetrad i,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨by
      intro i j he
      exact (by decide : Function.Injective standardTetrad) (congrArg Subtype.val he),by
      rintro ⟨A,hA⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
      exact ⟨i,rfl⟩⟩

theorem seed_intersection (s : Syntheme)
    (hn : FarOrbit.support (FarOrbit.seedMasks 1 2) ∉
      (synthemeTrio standardSextet labels s).parts) :
    ∃ A ∈ (FarOrbit.seedLine 1).parts,
      ∃ B ∈ (synthemeTrio standardSextet labels s).parts, (A ∩ B).card = 2 := by
  revert s; decide +kernel

theorem seed_pencil : OutsidePencil standardSextet (FarOrbit.seedLine 1) := by
  refine ⟨FarOrbit.support (FarOrbit.seedMasks 1 2),by decide +kernel,?_,?_⟩
  · exact ⟨standardTetrad 1,by decide +kernel,standardTetrad 5,
      by decide +kernel,by decide +kernel,by decide +kernel⟩
  · intro l hl hc
    let s := residueEquiv standardSextet labels ⟨l,hl⟩
    have he : synthemeTrio standardSextet labels s = l := by
      exact congrArg Subtype.val ((residueEquiv standardSextet labels).injective
        (residueSyntheme_synthemeTrio standardSextet labels s))
    rw [←he] at hc ⊢
    by_contra hn
    obtain ⟨A,hA,B,hB,hcard⟩ := seed_intersection s hn
    exact not_coplanar_of_inter_two hA hB hcard hc

theorem root_no_octad (r : Fin 4) (hr : r ≠ 1) (hr' : r ≠ 3)
    {A : Finset (Fin 24)} (hA : A ∈ (FarOrbit.rootLine r).parts) :
    ¬ PlaneOctad standardSextet A := by
  rintro ⟨B,hB,C,hC,hBC,rfl⟩
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hC
  have hc : ∀ (r : Fin 4) (i j : Fin 6), r ≠ 1 → r ≠ 3 →
      standardTetrad i ∪ standardTetrad j ∉ (FarOrbit.rootLine r).parts := by
    decide +kernel
  exact hc r i j hr hr' hA

theorem standard_outside_pencil (b : Line) (hb : ¬ Incident b standardSextet)
    (hA : ∃ A ∈ b.parts, PlaneOctad standardSextet A) : OutsidePencil standardSextet b := by
  obtain ⟨i,rfl⟩ := FarOrbit.entry_surjective b
  let g := (FarOrbit.exists_transport i).choose
  let r := (FarOrbit.row i).root
  have hr : r = 1 := by
    by_contra hn
    by_cases hr : r = 3
    · apply hb
      have hi : Incident (FarOrbit.rootLine r) standardSextet := by
        rw [hr]
        exact FarOrbit.seed_three_incident_standard
      exact incident_transport (g : M24) rfl g.property.symm hi
    · obtain ⟨A,hAb,hA⟩ := hA
      have hAr : (g : M24)⁻¹ • A ∈ (FarOrbit.rootLine r).parts := by
        simpa only [FarOrbit.entry,g,r,smulLine_parts,inv_smul_smul] using
          Finset.smul_mem_smul_finset (a := (g : M24)⁻¹) hAb
      exact root_no_octad r hn hr hAr
        (planeOctad_transport (g : M24)⁻¹ (g⁻¹).property.symm hA)
  have hp : OutsidePencil standardSextet (FarOrbit.rootLine r) := by
    rw [hr]
    exact seed_pencil
  exact outsidePencil_transport (g : M24) g.property.symm rfl hp
end PlanePencil

/-- The pencil part of (3.10): a nonincident trio sharing an octad with a
sextet is coplanar only with its three incident trios containing that octad. -/
theorem outside_pencil (π : Plane) (b : Line) (hb : ¬ Incident b π)
    (hA : ∃ A ∈ b.parts, PlaneOctad π A) : OutsidePencil π b := by
  obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
  have hi : ¬ Incident (g⁻¹ • b) standardSextet := fun hi => hb
    (incident_transport g (by simp) hg.symm hi)
  have hA' : ∃ A ∈ (g⁻¹ • b).parts, PlaneOctad standardSextet A := by
    obtain ⟨A,hAb,hA⟩ := hA
    exact ⟨g⁻¹ • A,Finset.smul_mem_smul_finset hAb,
      planeOctad_transport g⁻¹ (by rw [←hg,inv_smul_smul]) hA⟩
  exact outsidePencil_transport g hg.symm (by simp)
    (PlanePencil.standard_outside_pencil _ hi hA')
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
