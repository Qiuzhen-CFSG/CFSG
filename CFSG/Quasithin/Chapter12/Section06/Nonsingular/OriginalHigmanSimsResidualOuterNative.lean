module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageIntersectionsTransitivity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.Alternating.Aut

/-!
# A pure HS sixteen-subgroup acts outer on the point residual quotient

The native map from the involution centralizer to S5 sends a member of the
marked sixteen-subgroup to a transposition. Its cubic residual maps onto A5.
An inner action on the intrinsic two-core quotient of that residual would
give the same conjugation on A5 as an even permutation, contradicting the
faithfulness of S5 conjugation on A5. Conjugation marks the supplied pure
subgroup and its supplied nonidentity point simultaneously.

Source application: the HS inspection in Aschbacher--Smith 12.6.12, printed
pp.825--826. The action is on the literal residual and its entire two-core.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualOuterNative
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.HS
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
open EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
open OriginalHigmanSimsImageIntersectionsNative

private theorem symmetricFive_primeToResidual :
    primeToResidual 3 (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  apply primeToResidual_eq_of_generated (alternatingGroup (Fin 5))
    (by rw [alternatingGroup.index_eq_two]; decide)
    _ Equiv.Perm.closure_three_cycles_eq_alternating
  intro x hx
  refine ⟨1,?_⟩
  simpa only [pow_one,hx.orderOf] using pow_orderOf_eq_one x

private theorem outer_of_odd_image
    {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 A) (w : A) (hw : f w ∉ alternatingGroup (Fin 5)) :
    normalQuotientAction (primeToResidual 3 A) (pCore 2 (primeToResidual 3 A)) w ∉
      MulAut.innerSubgroup ((primeToResidual 3 A) ⧸ pCore 2 (primeToResidual 3 A)) := by
  let R := primeToResidual 3 A
  let N := pCore 2 R
  have hr : R.map f = alternatingGroup (Fin 5) := by
    rw [map_primeToResidual_of_surjective 3 f hf,symmetricFive_primeToResidual]
  have hn : N ≤ (f.comp R.subtype).ker := by
    rw [←MonoidHom.comap_ker,hk,←pCore_eq_comap_of_normal]
  let q : (R ⧸ N) →* Equiv.Perm (Fin 5) := QuotientGroup.lift N (f.comp R.subtype) hn
  intro hi
  obtain ⟨c,hc⟩ := hi
  obtain ⟨r,hrc⟩ := QuotientGroup.mk'_surjective N c
  have he : (MulAut.conjNormal (H := alternatingGroup (Fin 5)) (f (r : A))) =
      MulAut.conjNormal (H := alternatingGroup (Fin 5)) (f w) := by
    apply MulEquiv.ext
    intro x
    have hx : (x : Equiv.Perm (Fin 5)) ∈ R.map f := by
      rw [hr]
      exact x.property
    obtain ⟨s,hs,hsx⟩ := hx
    have hh := congrArg (fun a : MulAut (R ⧸ N) => q (a (QuotientGroup.mk' N ⟨s,hs⟩))) hc
    rw [←hrc,MulAut.conj_apply,normalQuotientAction_apply_mk] at hh
    change f ((r : A) * s * (r : A)⁻¹) = f (w * s * w⁻¹) at hh
    simp only [map_mul,map_inv,hsx] at hh
    exact Subtype.ext hh
  have heq := _root_.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5
    (by decide) he
  exact hw (heq ▸ (hr ▸ mem_map_of_mem f r.property))

private theorem swap_mem_marked : (swapLocal : Carrier) ∈ markedW := by
  refine ⟨1,?_⟩
  have hr : candidateRow 0 1 = 2 := by decide +kernel
  change element (candidateRow 0 1) = s1
  rw [hr]
  apply Subtype.ext
  apply Equiv.ext
  intro p
  have h : ∀ p : Fin 100, (element 2 : Equiv.Perm (Fin 100)) p = s1Map p := by
    apply SylowCatalogueData.allFin
    decide +kernel
  exact h p

private theorem swap_odd : fiveHom swapLocal ∉ alternatingGroup (Fin 5) := by
  rw [swapLocal_image]
  simp

/-- Every pure elementary sixteen-subgroup supplies a genuinely outer
automorphism of the cubic residual quotient at each nonidentity point. -/
theorem pure_sixteen_has_outer_residual_action
    (W : Subgroup Carrier) (hW : IsElementaryAbelian 2 W) (hcard : Nat.card W = 16)
    (hp : ∀ x ∈ W, ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p)
    (j : Carrier) (hj : j ∈ W) (hne : j ≠ 1) :
    let F := centralizer ({j} : Set Carrier)
    let R := primeToResidual 3 F
    ∃ w : F, (w : Carrier) ∈ W ∧
      normalQuotientAction R (pCore 2 R) w ∉ MulAut.innerSubgroup (R ⧸ pCore 2 R) := by
  obtain ⟨g,hg⟩ := pure_sixteen_conjugate W hW hcard hp
  have hjW : (MulAut.conj g) j ∈ markedW := hg ▸ mem_map_of_mem _ hj
  have hjne : (MulAut.conj g) j ≠ 1 := by
    intro he
    exact hne ((MulAut.conj g).injective (he.trans (map_one (MulAut.conj g)).symm))
  obtain ⟨k,hk,hkj⟩ := markedW_point_transitive _ hjW hjne
  let α : MulAut Carrier := MulAut.conj k * MulAut.conj g
  have hmark : W.map α.toMonoidHom = markedW := by
    change W.map ((MulAut.conj k).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = markedW
    rw [←Subgroup.map_map,hg]
    exact mem_normalizer_iff_map_conj_eq.mp hk
  have hpoint : α j = e0 := hkj
  let F := centralizer ({j} : Set Carrier)
  have hcent : F.map α.toMonoidHom = localGroup 0 := by
    rw [map_centralizer_equiv,Set.image_singleton,hpoint,←LocalGeneration.first_eq_centralizer]
  let e : F ≃* localGroup 0 := (α.subgroupMap F).trans (MulEquiv.subgroupCongr hcent)
  let f : F →* Equiv.Perm (Fin 5) := fiveHom.comp e.toMonoidHom
  have hf : Function.Surjective f := fiveHom_surjective.comp e.surjective
  have hfker : f.ker = pCore 2 F := by
    rw [←MonoidHom.comap_ker,fiveHom_kernel,LocalGeneration.first_core_eq,
      ←pCore_map_iso 2 e,comap_map_eq_self_of_injective e.injective]
  let w : F := e.symm swapLocal
  have hew : α (w : Carrier) = (swapLocal : Carrier) :=
    congrArg Subtype.val (e.apply_symm_apply swapLocal)
  have hw : (w : Carrier) ∈ W := by
    have hm : α (w : Carrier) ∈ W.map α.toMonoidHom := by
      rw [hmark,hew]
      exact swap_mem_marked
    obtain ⟨x,hx,hxe⟩ := hm
    exact α.injective hxe ▸ hx
  refine ⟨w,hw,outer_of_odd_image f hf hfker w ?_⟩
  change fiveHom (e (e.symm swapLocal)) ∉ alternatingGroup (Fin 5)
  rw [e.apply_symm_apply]
  exact swap_odd

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualOuterNative
