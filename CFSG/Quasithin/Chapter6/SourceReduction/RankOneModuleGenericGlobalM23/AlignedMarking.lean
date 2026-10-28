module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.TripleHeptad
public import Theory.GroupTheory.Recognition.QuasithinM23.AdjacentPairs

/-!
# Aligning the marked exceptional triple

Conjugate the compatible heptad marking by an actual alternating-group
element that fixes the marked pair and sends the original triple to the
triple supporting the native four-set edge. The core and every original local
subgroup remain under this one map.
Source: Aschbacher--Smith 5.2.17--5.2.20, printed pp.655--656.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

theorem Preparation.linear_exceptional_aligned_heptad_marking
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    ∃ ζ : J ≃* heptadStabilizer,
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction := by
  obtain ⟨ζ,s,hs,h5,h6,hcore,hK,hHm,hM⟩ :=
    d.linear_exceptional_pair_triple_heptad_marking h hH hp F hm hF he hJ hKJ
  obtain ⟨a,ha5,ha6,has⟩ := QuasithinM23.seven_pair_triple_alignment s hs h5 h6
  let k := AlternatingSection.s a
  let c := MulAut.conj k
  have hc (x : heptadStabilizer) : heptadAction (c x) =
      a.val * heptadAction x * a.val⁻¹ := by
    change heptadAction (k*x*k⁻¹) = _
    rw [map_mul,map_mul,map_inv,AlternatingSection.heptadAction_s]
  have hap : a.val • ({5,6} : Set (Fin 7)) = {5,6} := by
    simp only [Set.smul_set_insert,Set.smul_set_singleton,Equiv.Perm.smul_def,ha5,ha6]
  have hat : a.val • (s : Set (Fin 7)) = ({4,5,6} : Set (Fin 7)) := by
    have hh := congrArg (fun t : Finset (Fin 7) => (t : Set (Fin 7))) has
    simpa only [Finset.coe_smul_finset,MulAction.subgroup_smul_def,Finset.coe_insert,Finset.coe_singleton] using hh
  have hpair : pairStabilizer.subgroupOf heptadStabilizer =
      (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction := by
    ext g
    change (g : Sporadic.Mathieu.M23) • x.val = x.val ↔ _
    have hx : ({5,6} : Finset (Fin 7)).image label = x.val := by decide +kernel
    have hh := heptadAction_stabilizes_labels g ({5,6} : Finset (Fin 7))
    rw [hx] at hh
    symm
    convert hh using 1
    change heptadAction g • ({5,6} : Set (Fin 7)) = {5,6} ↔ _
    rw [←Finset.coe_inj]
    simp only [Finset.coe_smul_finset,Finset.coe_insert,Finset.coe_singleton]
  have hmap (R : Subgroup J) : R.map (ζ.trans c).toMonoidHom =
      (R.map ζ.toMonoidHom).map c.toMonoidHom := by
    change R.map (c.toMonoidHom.comp ζ.toMonoidHom) = _
    rw [←map_map]
  refine ⟨ζ.trans c,?_,?_,?_,?_⟩
  · rw [hmap,hcore]
    exact QuasithinM23.heptad_marking_map_kernel heptadAction c a.val hc
  · rw [hmap,hK,QuasithinM23.heptad_marking_map_fixingSubgroup heptadAction c a.val hc,hap]
  · rw [hmap,hHm,hpair,QuasithinM23.heptad_marking_map_stabilizer heptadAction c a.val hc,hap]
  · rw [hmap,hM,QuasithinM23.heptad_marking_map_stabilizer heptadAction c a.val hc,hat]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
