module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoCartanData
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoCartanPair
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoAssembly
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFSolvable

/-!
# Original tensor Cartan rows with explicit geometric inputs

The original Cartan containment and the common local-component markings are
proved. In the G₂ row, solvability of the original Cartan--Sylow join gives
Sylow normalization after the literal action map. A nonzero fixed natural
vector identifies the old residual as the long local component. The concrete
cubic calculation then centralizes its A₅ section; the Cartan orbit contradicts
the cubic lying inside that section.

The two remaining geometric inputs are the actual normalizer-orbit identities
and the fixed-vector marking. They are kept explicit, so the final theorem
below is a conditional assembly of 9.3.8--9, not a proof of these inputs.
Source: Aschbacher--Smith 9.3.8--9, printed p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterC.MSCentralOrbit
open Chapter4 SourceOldResidualActorPair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)
local notation "F" => ChapterB.QuasisimpleSource.BinaryField.four.Carrier

/-- The two original Cartan factors generate the Cartan under its Sylow normalizer. -/
@[expose] def CartanOrbits : Prop :=
  componentOrbit (c.A ⊓ L) ((T : Subgroup G) ⊓ normalizer (c.A : Set G)) = c.A ∧
  ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (L : Set G) ∧
    componentOrbit (c.A ⊓ L.map (MulAut.conj t).toMonoidHom)
      ((T : Subgroup G) ⊓ normalizer (c.A : Set G)) = c.A

/-- A marking of the actual residual action and its common Sylow, with a
nonzero natural vector fixed by the old residual. No local-component or
section-centralization conclusion is assumed. -/
structure G2FixedVectorMarking (W : Subgroup c.M) [W.Normal] where
  marking : ((pResidual 2 c.M).map (actionMk W)) ≃* Atlas.G2.Model F
  sylow_image :
    ((((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M).subgroupOf
      (pResidual 2 c.M)).map
        (marking.toMonoidHom.comp ((actionMk W).subgroupMap (pResidual 2 c.M))) =
      Atlas.G2.unipotent
  vector : Atlas.G2.Natural.Space F
  nonzero : vector ≠ 0
  sylow_fixed : ∀ u ∈ Atlas.G2.unipotent (K := F),
    Atlas.G2.Natural.action F u vector = vector
  residual_fixed :
    ∀ k ∈ ((((pResidual 2 c.H).map c.H.subtype).subgroupOf c.M).subgroupOf
      (pResidual 2 c.M)).map
        (marking.toMonoidHom.comp ((actionMk W).subgroupMap (pResidual 2 c.M))),
      Atlas.G2.Natural.action F k vector = vector

/-- Both linear action rows are excluded once the original normalizer orbit is supplied. -/
theorem not_linear_of_cartanOrbits (ho : c.CartanOrbits)
    (hr : IsPReduced 2 (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))) :
    letI := hr.normal
    ¬ Nonempty (((pResidual 2 c.M).map (actionMk (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))) ≃* SL(3,F)) := by
  let := hr.normal
  let := c.elementary_cartan
  rintro ⟨a⟩
  obtain ⟨t,ht,htn,htorbit⟩ := ho.2
  exact m.old_residual_linear_image_false
    (by rw [ChapterB.QuasisimpleSource.BinaryField.four.card_eq]; decide)
    c.hstar c.large c.M c.core_ne_bot c.generated c.line_centralized
    _ c.tensorLine_le_omegaOrbit c.A c.B c.cartan_le c.cartan_normalizes
    c.hall_le_cartan c.hall_le_residual c.card_hall ht htn htorbit a

/-- The G₂ fixed-vector marking supplies the original short/long assignment;
the solvable Cartan--Sylow join supplies the remaining Borel condition. -/
theorem false_of_g2FixedVectorMarking
    (W : Subgroup c.M) [W.Normal] (hUW : m.tensorLine.subgroupOf c.M ≤ W)
    (d : c.G2FixedVectorMarking W)
    (horbit : componentOrbit (c.A ⊓ L)
      ((T : Subgroup G) ⊓ normalizer (c.A : Set G)) = c.A) : False := by
  let J := pResidual 2 c.M
  let K := (pResidual 2 c.H).map c.H.subtype
  let C := L.subgroupOf c.M
  let B := K.subgroupOf c.M
  let E := c.A ⊓ L
  let E₁ := E.subgroupOf c.M
  let q := actionMk W
  let := c.elementary_cartan
  have hLM : L ≤ c.M := c.generated ▸ le_sup_of_le_left le_sup_left
  have hKM : K ≤ c.M := c.generated ▸ le_sup_of_le_left le_sup_right
  have hEM : E ≤ c.M := inf_le_right.trans hLM
  obtain ⟨_,hCJ,hBJ,_,hkB,hne,_,_,R,hR,hBlocal,hClocal⟩ :=
    m.old_residual_pair_action_data c.hstar c.large c.M c.core_ne_bot c.generated
      c.line_centralized W hUW
  let aC : C ≃* L := subgroupOfEquivOfLe hLM
  let eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ aC (pCore_map_iso 2 aC)).trans e
  obtain ⟨eK⟩ := m.old_residual_a5 c.hstar c.large
  let aB : B ≃* K := subgroupOfEquivOfLe hKM
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ aB (pCore_map_iso 2 aB)).trans eK
  have hEC : E₁ ≤ C := comap_mono inf_le_right
  have hEJ : E₁ ≤ J := hEC.trans hCJ
  have hEK : E ≤ normalizer (K : Set G) := inf_le_left.trans c.cartan_normalizes
  have hEB : E₁ ≤ normalizer (B : Set c.M) := by
    rw [←subgroupOf_normalizer_eq hKM]
    exact comap_mono hEK
  let j : J →* G := c.M.subtype.comp J.subtype
  have hji : Function.Injective j := c.M.subtype_injective.comp J.subtype_injective
  let U := (c.A ⊔ (T : Subgroup G)).comap j
  let : Group.IsSolvable (c.A ⊔ (T : Subgroup G) : Subgroup G) :=
    m.cartan_sylow_join_isSolvable c.A c.borel
  let : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
    (f := j.subgroupComap (c.A ⊔ (T : Subgroup G)))
    (fun x y h => Subtype.ext (hji
      (congrArg (fun z : (c.A ⊔ (T : Subgroup G) : Subgroup G) => (z : G)) h)))
  have hsol : Group.IsSolvable (E₁.subgroupOf J ⊔ (R : Subgroup J) : Subgroup J) := by
    have hle : E₁.subgroupOf J ⊔ (R : Subgroup J) ≤ U := by
      refine sup_le ?_ ?_
      · intro x hx
        exact (le_sup_left : c.A ≤ c.A ⊔ (T : Subgroup G)) hx.1
      · intro x hx
        rw [hR] at hx
        exact (le_sup_right : (T : Subgroup G) ≤ c.A ⊔ (T : Subgroup G)) hx.1
    exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  have hmarkR : (R : Subgroup J).map (d.marking.toMonoidHom.comp (q.subgroupMap J)) =
      Atlas.G2.unipotent := by
    rw [hR]
    exact d.sylow_image
  have hcentral : E₁ ≤ sectionCentralizer B := g2_factor_centralizes
    (by rw [ChapterB.QuasisimpleSource.BinaryField.four.card_eq]; decide)
    q J C B E₁ hCJ hBJ hEJ d.marking R hClocal hBlocal eC eB hkB hne hEC hEB
    (fun x hx => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 3) (x : G) hx.1))
    hsol hmarkR d.vector d.nonzero d.sylow_fixed d.residual_fixed
  have hcentral' : E ≤ sectionCentralizer K := by
    apply (le_sectionCentralizer_iff E K).mpr
    refine ⟨hEK,?_⟩
    have hm := map_mono (f := c.M.subtype) ((le_sectionCentralizer_iff E₁ B).mp hcentral).2
    rwa [map_commutator,map_subgroupOf_eq_of_le hEM,
      map_pCoreIn_of_injective 2 _ _ c.M.subtype_injective,map_subgroupOf_eq_of_le hKM] at hm
  have hNK : (T : Subgroup G) ⊓ normalizer (c.A : Set G) ≤ normalizer (K : Set G) :=
    inf_le_left.trans (c.hstar.1.1.2.trans (le_normalizer_embedded_pResidual 2 c.H))
  have hBne : c.B ≠ ⊥ := by
    intro he
    have hc := c.card_hall
    rw [he,card_bot] at hc
    omega
  obtain ⟨b,hb⟩ := ne_bot_iff_exists_ne_one.mp hBne
  have hb3 : orderOf b = 3 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (c.card_hall ▸ orderOf_dvd_natCard b)).resolve_left (fun h => hb (orderOf_eq_one_iff.mp h))
  exact source_tensor_torus_cubic_contradiction K c.A E _ eK hNK hcentral' horbit
    b (c.hall_le_cartan b.property) (c.hall_le_residual b.property)
    ((Subgroup.orderOf_coe b).trans hb3)

end GenerationTwoOvergroup

variable (m)
/-- The natural fixed-vector transport still needed on the literal Omega orbit. -/
@[expose] def G2FixedVectorInput : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ hr : IsPReduced 2 W,
      letI := hr.normal
      Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        Atlas.G2.Model ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
      Nonempty (c.G2FixedVectorMarking W)

/-- Both row contradictions, with exactly the two geometric inputs explicit. -/
theorem linearAndG2Exclusion_of_cartan_and_fixedVector
    (horbits : ∀ c : m.GenerationTwoOvergroup, c.CartanOrbits)
    (hfixed : m.G2FixedVectorInput) : m.LinearAndG2Exclusion := by
  intro c W hr
  let := hr.normal
  refine ⟨c.not_linear_of_cartanOrbits (horbits c) hr,?_⟩
  intro hg2
  obtain ⟨d⟩ := hfixed c hr hg2
  exact c.false_of_g2FixedVectorMarking W c.tensorLine_le_omegaOrbit d (horbits c).1

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
