module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Pair
public import Theory.GroupTheory.Recognition.QuasithinM23.ExceptionalMarking
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalQuotients

/-!
# Source 5.2.17 and the compatible original pair marking

The original exceptional local has a self-centralizing E₁₆ core and actual
A₇ quotient. Its proved splitting and faithful-action comparison construct
a multiplicative equivalence to the native M₂₃ heptad stabilizer, together
with a permutation equivalence on all seven quotient points.

Apply that equivalence to the original pair marking from 5.2.11(1). One
inner adjustment in the native heptad sends the marked pair to {5,6}.
The same equivalence sends the entire original core to the heptad kernel,
K = O²(H) to the pointwise pair fixer, and H to the named native heptad–pair
intersection. No independent endpoint isomorphisms or splitting inputs are
assumed. The compatible linear-completion marking and ambient recognition
remain separate steps.

Source: Aschbacher–Smith 5.2.11(1), 5.2.17, printed pp.653,655
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Sporadic.Mathieu.M23Geometry
variable {G : Type*} [Group G] [Finite G]

/-- Source 5.2.17: an actual permutation equivalence from the original
exceptional local to the native M₂₃ heptad stabilizer. -/
theorem Preparation.linear_exceptional_heptad_marking
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
    (hKJ : residual H < J)
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7)) :
    ∃ (ζ : J ≃* heptadStabilizer) (σ : Equiv.Perm (Fin 7)),
      ∀ x : J, heptadAction (ζ x) = σ * (e (QuotientGroup.mk x)).val * σ⁻¹ := by
  have hTH := hH.1.1.2
  have hn := (d.block_overcomponent_parameter h hTH hp F hm hF (.inl he) hJ.1 hKJ).1
  obtain ⟨ha,hcard,_⟩ := d.linear_overcomponent_action h hTH hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  let := ha
  have hC : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1) (fun x hx y hy => setLike_mul_comm hy hx)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  exact QuasithinM23.exceptional_heptad_marking (pCore 2 J) hcard q hq hk hC

/-- The same native marking sends the whole original H and K to the setwise
and pointwise stabilizers of the same marked pair, respectively. -/
theorem Preparation.linear_exceptional_pair_heptad_marking
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
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer := by
  obtain ⟨e,i,j,hij,hK,hHmark,_⟩ := d.linear_exceptional_pair_marking h hH hp F hm hF he hJ hKJ
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
  refine ⟨η,?_,?_,?_⟩
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

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
