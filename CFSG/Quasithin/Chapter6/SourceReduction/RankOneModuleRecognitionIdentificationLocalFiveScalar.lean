module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveCubic
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The nonidentity scalar in the final A5 branch of source 6.2.7

The original cubic centralizes the actual A5 component on the marked
field-plane quotient. Restricting to its whole moved space and transporting
through its natural SL2 marking makes this operator a scalar. Its cube is
one. To exclude the identity scalar, take the component preimage under the
original centralizer action. It contains the original offender and commutes
with the cubic modulo the action kernel. The source three-subgroups claim
then gives a nonzero displacement of this same moved space.

The resulting section keeps the original cubic, quotient coordinates,
component Sylow and fixed complement. The Chapter12 companion constructs it
from the original chosen module. The outer two-action contradiction and the
subsequent graph argument remain for LocalAnalysis.
Source: Aschbacher--Smith, 6.2.7, printed p.684, using the noncentrality claim
on p.682 and the natural-component calculation on p.683.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction

private theorem section_component_not_fixed
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {H J U P A : Subgroup G} (hHP : H ≤ P) (hAH : A ≤ H)
    (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D W)
    (c : BinaryConjugationSection H J U (ρ.comp π))
    (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η)
    (hcoords : c'.coordinates = c.coordinates)
    (hr : ∀ a : H, η (inclusion hHP a) = ρ (π a))
    (d : P) (K : Subgroup D) (hAK : (A.subgroupOf H).map π ≤ K)
    (hc : ∀ k : K, Commute (η.asGroupHom d) (ρ.asGroupHom k))
    (hclaim : ∀ Q : Subgroup G, A ≤ Q → Q ≤ H →
      (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ →
      c'.imageSpace ⁅⁅J,Q⁆,zpowers (d : G)⁆ ≠ ⊥) :
    ¬ ∀ w ∈ moved ρ K, η d w = w := by
  intro hf
  let K0 := K.comap π
  let Q := K0.map H.subtype
  have hQH : Q ≤ H := map_subtype_le _
  have hQP : Q ≤ P := hQH.trans hHP
  have hAQ : A ≤ Q := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hAK (mem_map_of_mem π ha),rfl⟩
  have hQsub : Q.subgroupOf H = K0 := by
    change (K0.map H.subtype).comap H.subtype = K0
    rw [comap_map_eq_self_of_injective H.subtype_injective]
  have hKmap : K0.map π = K := by
    exact map_comap_eq_self_of_surjective hπ K
  have hQsubP : Q.subgroupOf P = K0.map (inclusion hHP) := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hQP,map_map]
    rfl
  have hQimage : (Q.subgroupOf P).map η.asGroupHom = K.map ρ.asGroupHom := by
    rw [hQsubP,map_map]
    have he : η.asGroupHom.comp (inclusion hHP) = ρ.asGroupHom.comp π := by
      apply MonoidHom.ext
      intro a
      exact Units.ext (hr a)
    rw [he,←map_map,hKmap]
  have hDsub : (zpowers (d : G)).subgroupOf P = zpowers d := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr d.property),MonoidHom.map_zpowers]
    rfl
  have hcommSub : ⁅Q,zpowers (d : G)⁆.subgroupOf P =
      ⁅Q.subgroupOf P,zpowers d⁆ := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (Subgroup.commutator_le_sup Q _ |>.trans
      (sup_le hQP (zpowers_le.mpr d.property))),map_commutator,
      map_subgroupOf_eq_of_le hQP,MonoidHom.map_zpowers]
    rfl
  have hcomm : (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ := by
    rw [hcommSub,map_commutator,hQimage,MonoidHom.map_zpowers,commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply zpowers_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    exact (hc ⟨k,hk⟩).eq.symm
  have hself : c.imageSpace J = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨j,hj⟩ := c.onto (Multiplicative.ofAdd w)
    exact (c.mem_imageSpace_iff _ _).mpr ⟨j,j.property,congrArg Multiplicative.toAdd hj⟩
  have hm : c'.imageSpace ⁅J,Q⁆ = moved ρ K := by
    have he : c'.imageSpace ⁅J,Q⁆ = c.imageSpace ⁅J,Q⁆ := by
      simp only [BinaryConjugationSection.imageSpace,hcoords]
    rw [he,commutator_comm J Q,c.imageSpace_commutator Q J hQH le_rfl,
      hself,subspaceCommutator_comp_map,hQsub,hKmap]
  apply hclaim Q hAQ hQH hcomm
  rw [commutator_comm ⁅J,Q⁆ _,c'.imageSpace_commutator _ _
    (zpowers_le.mpr d.property)
    (le_normalizer_iff_commutator_le_left.mp (hQP.trans c'.normalized)),hm,hDsub]
  apply (subspaceCommutator_eq_bot_iff η _ _).mpr
  intro w hw
  exact (mem_fixedSpace_zpowers_iff η d w).mpr (hf w hw)

private theorem natural_cubic_scalar
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (K : Subgroup D)
    (F : BinaryField)
    (a : ActionEquiv ((invariantSubspace ρ K (moved ρ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) (linearNatural F 2))
    (f : (Module.End (ZMod 2) W)ˣ) (hf3 : f^3=1)
    (hc : ∀ k : K, Commute f (ρ.asGroupHom k))
    (hne : ¬ ∀ w ∈ moved ρ K, f.val w = w) :
    ∃ z : F.Carrier, z ≠ 0 ∧ z ≠ 1 ∧ z^3=1 ∧
      ∀ w : moved ρ K,
        f.val w = (a.linearEquiv.symm (z • a.linearEquiv w) : W) := by
  let I := moved ρ K
  let σ : Representation (ZMod 2) K I := (invariantSubspace ρ K I (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W f
  have hcomm (k : K) (w : W) : l (ρ k w) = ρ k (l w) :=
    congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val w) (hc k).eq
  have hmaple : I.map l.toLinearMap ≤ I := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,_,rfl⟩
    change l (ρ k w - w) ∈ I
    rw [map_sub,hcomm ⟨k,hk⟩]
    exact Submodule.subset_span ⟨k,hk,l w,Submodule.mem_top,rfl⟩
  have hmap : I.map l.toLinearMap = I := Submodule.eq_of_le_of_finrank_eq hmaple
    (LinearEquiv.finrank_map_eq l I)
  let lI := l.ofSubmodules I I hmap
  let e : I ≃ₗ[ZMod 2] (Fin 2 → F.Carrier) := a.linearEquiv
  let b := (e.symm.trans lI).trans e
  have he (k : K) (w : I) : e (σ k w) = (a.groupEquiv k).val.mulVec (e w) :=
    a.intertwines k w
  have hei (k : K) (v : Fin 2 → F.Carrier) :
      e.symm ((a.groupEquiv k).val.mulVec v) = σ k (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  obtain ⟨z,hz⟩ := SL2NaturalOffenders.centralizer_scalar b.toAddMonoidHom (by
    intro k v
    obtain ⟨k,rfl⟩ := a.groupEquiv.surjective k
    change e (lI (e.symm ((a.groupEquiv k).val.mulVec v))) =
      (a.groupEquiv k).val.mulVec (e (lI (e.symm v)))
    rw [hei,show lI (σ k (e.symm v)) = σ k (lI (e.symm v)) from
      Subtype.ext (hcomm k (e.symm v)),he])
  change ∀ v, b v = z • v at hz
  have hformula (w : I) : f.val w = (e.symm (z • e w) : W) := by
    have hh := hz (e w)
    change e (lI (e.symm (e w))) = z • e w at hh
    rw [e.symm_apply_apply] at hh
    exact congrArg Subtype.val (e.injective (hh.trans (e.apply_symm_apply _).symm))
  have hb3 (v : Fin 2 → F.Carrier) : b (b (b v)) = v := by
    apply e.symm.injective
    apply Subtype.ext
    have hh := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val (e.symm v : W)) hf3
    change l (l (l (e.symm v : W))) = (e.symm v : W) at hh
    simp only [b, LinearEquiv.trans_apply, e.symm_apply_apply]
    exact hh
  have hz3 : z^3=1 := by
    have hh := congrFun (hb3 (fun _ => 1)) 0
    rw [hz,hz,hz] at hh
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one,pow_succ,pow_zero,one_mul,mul_assoc] using hh
  refine ⟨z,?_,?_,hz3,hformula⟩
  · intro heq
    rw [heq,zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  · intro heq
    apply hne
    intro w hw
    simpa only [heq,one_smul,e.symm_apply_apply] using hformula ⟨w,hw⟩

/-- On the same marked quotient as the source noncentrality claim, a cubic
centralizing a natural component containing the offender is a nonidentity
field scalar on that component's whole moved space. -/
theorem section_natural_cubic_scalar
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]
    {H J U P A : Subgroup G} (hHP : H ≤ P) (hAH : A ≤ H)
    (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D W)
    (c : BinaryConjugationSection H J U (ρ.comp π))
    (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η)
    (hcoords : c'.coordinates = c.coordinates)
    (hr : ∀ a : H, η (inclusion hHP a) = ρ (π a))
    (d : P) (hd : d^3=1) (K : Subgroup D) (hAK : (A.subgroupOf H).map π ≤ K)
    (hc : ∀ k : K, Commute (η.asGroupHom d) (ρ.asGroupHom k))
    (hclaim : ∀ Q : Subgroup G, A ≤ Q → Q ≤ H →
      (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ →
      c'.imageSpace ⁅⁅J,Q⁆,zpowers (d : G)⁆ ≠ ⊥)
    (F : BinaryField)
    (a : ActionEquiv ((invariantSubspace ρ K (moved ρ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) (linearNatural F 2)) :
    ∃ z : F.Carrier, z ≠ 0 ∧ z ≠ 1 ∧ z^3=1 ∧
      ∀ w : moved ρ K,
        η d w = (a.linearEquiv.symm (z • a.linearEquiv w) : W) := by
  apply natural_cubic_scalar ρ K F a (η.asGroupHom d)
  · rw [←map_pow,hd,map_one]
  · exact hc
  · exact section_component_not_fixed hHP hAH π hπ ρ c η c' hcoords hr d K hAK hc hclaim

/-- The original field-plane section, including its original cubic and quotient
marking, with a moved A5 component on which the cubic is a nonidentity scalar
over the field of four elements. -/
@[expose] def CubicScalarSection {G : Type*} [Group G] [Finite G]
    (L B A U : Subgroup G) [IsElementaryAbelian 2 (space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let P := H ⊔ fieldLocalResidual L U
    let W := Additive (LocalFieldQuotientAction.space B U)
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range W)
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ Nat.card I = 4 ∧
      ∃ (d : G) (hd : d ∈ fieldLocalResidual L U), orderOf d = 3 ∧ ⁅B,zpowers d⁆ = B ∧
        ∃ (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η),
          c'.coordinates = c.coordinates ∧
          (∀ a : H, η (inclusion le_sup_left a) = ρ (π a)) ∧
          (∃ hd : d ∈ P, orderOf (η.asGroupHom ⟨d,hd⟩) = 3) ∧
          (∀ K : Subgroup G, A ≤ K → K ≤ H →
            (⁅K,zpowers d⁆.subgroupOf P).map η.asGroupHom = ⊥ →
            c'.imageSpace ⁅⁅J,K⁆,zpowers d⁆ ≠ ⊥) ∧
          (∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
            ((c'.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)) ∧
          ∃ K : Subgroup (LocalFieldQuotientAction.action B U).range,
            IsComponent _ K ∧ ⁅K,I⁆ = K ∧ Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
            (∀ k : K, Commute (η.asGroupHom ⟨d,mem_sup_right hd⟩) (ρ.asGroupHom k)) ∧
            (∃ S : Sylow 2 K, I = (S : Subgroup K).map K.subtype) ∧
            IsCompl (moved ρ K) (fixedSpace ρ K) ∧
            ∃ (F : BinaryField), F.degree = 2 ∧
              ∃ (a : ActionEquiv ((invariantSubspace ρ K (moved ρ K)
                (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) (linearNatural F 2)),
                ∃ z : F.Carrier, z ≠ 0 ∧ z ≠ 1 ∧ z^3=1 ∧
                  ∀ w : moved ρ K,
                    η ⟨d,mem_sup_right hd⟩ w =
                      (a.linearEquiv.symm (z • a.linearEquiv w) : W)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
