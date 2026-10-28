module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Triple

/-!
# One native heptad marking for the original pair and triple

Extend the source triple marking through the actual exceptional-local
isomorphism with the native M₂₃ heptad stabilizer. Align its marked pair
once. The same equivalence preserves the entire two-core, both original
pair subgroups, and the original maximal-local intersection as the
stabilizer of a triple containing that native pair.

Source: Aschbacher–Smith 5.2.11(1),(2) and 5.2.17, printed pp.653–655
(`refs/quasithin.pdf`). This is compatible local marking, not ambient
M₂₃ recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

theorem Preparation.linear_exceptional_pair_triple_heptad_marking
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
    ∃ (ζ : J ≃* heptadStabilizer) (t : Finset (Fin 7)),
      t.card = 3 ∧ (5 : Fin 7) ∈ t ∧ (6 : Fin 7) ∈ t ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) (t : Set (Fin 7))).comap heptadAction := by
  obtain ⟨e,i,j,s,hij,hs,his,hjs,hK,hHmark,hMmark⟩ :=
    d.linear_exceptional_pair_triple_marking h hH hp F hm hF he hJ hKJ
  obtain ⟨ζ,σ,hζ⟩ := d.linear_exceptional_heptad_marking h hH hp F hm hF he hJ hKJ e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  let p := (alternatingGroup (Fin 7)).subtype.comp q
  have hK' : (residual H).subgroupOf J =
      (fixingSubgroup (Equiv.Perm (Fin 7)) ({i,j} : Set (Fin 7))).comap p := hK
  have hH' : H.subgroupOf J =
      (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({i,j} : Set (Fin 7))).comap p := hHmark
  obtain ⟨η,τ,hi,hj,hη⟩ := QuasithinM23.heptad_marking_align_pair p ζ σ hζ i j hij
  have hpair : τ • ({i,j} : Set (Fin 7)) = ({5,6} : Set (Fin 7)) := by
    simp only [Set.smul_set_insert,Set.smul_set_singleton,Equiv.Perm.smul_def,hi,hj]
  have hk : p.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective q (alternatingGroup (Fin 7)).subtype
      Subtype.val_injective]
    exact (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  have hM' : (normalizer (L : Set G)).subgroupOf J =
      (MulAction.stabilizer (Equiv.Perm (Fin 7)) (s : Set (Fin 7))).comap p := hMmark
  have htriple : τ • (s : Set (Fin 7)) = (s.image τ : Set (Fin 7)) := by
    rw [Finset.coe_image]
    rfl
  refine ⟨η,s.image τ,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ τ.injective,hs]
  · rw [←hi]
    exact Finset.mem_image_of_mem τ his
  · rw [←hj]
    exact Finset.mem_image_of_mem τ hjs
  · rw [←hk]
    exact QuasithinM23.heptad_marking_map_kernel p η τ hη
  · rw [hK',←hpair]
    exact QuasithinM23.heptad_marking_map_fixingSubgroup p η τ hη _
  · have hp : (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap
        heptadAction = pairStabilizer.subgroupOf heptadStabilizer := by
      ext g
      change heptadAction g • ({5,6} : Set (Fin 7)) = {5,6} ↔
        (g : Sporadic.Mathieu.M23) • x.val = x.val
      have hx : ({5,6} : Finset (Fin 7)).image label = x.val := by decide +kernel
      have hh := heptadAction_stabilizes_labels g ({5,6} : Finset (Fin 7))
      rw [hx] at hh
      convert hh using 1
      rw [←Finset.coe_inj]
      simp only [Finset.coe_smul_finset,Finset.coe_insert,Finset.coe_singleton]
    rw [←hp,hH',←hpair]
    exact QuasithinM23.heptad_marking_map_stabilizer p η τ hη _

  · rw [hM',←htriple]
    exact QuasithinM23.heptad_marking_map_stabilizer p η τ hη _

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
