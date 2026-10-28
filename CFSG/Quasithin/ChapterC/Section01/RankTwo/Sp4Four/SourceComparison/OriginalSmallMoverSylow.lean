module
public import Theory.SpecificGroups.SymplecticFour.SmallMoverSylow
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction

/-!
# The unique maximum small mover on an original Sylow edge

The original moved layer with trivial fixed kernel has a faithful natural
marking. Its actual Sylow subgroup maps to a Sylow subgroup of the ambient
action quotient. The field-four calculation identifies a unique maximum
small mover, with relative order64 and moving index16. Transport retains
the entire kernel Q and the original conjugation action.

Source: MS93 (5.0)--(5.4), pp.912--915, specialized to a full Sylow edge.
The original tensor application is GenerationTwoSymplecticSylowMovers.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Full-Sylow specialization of the source maximum family, with literal kernels. -/
theorem original_sylow_small_mover_unique
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {a : Vertex R} (ha : color R a = false)
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥)
    (T : Subgroup (FreeAmalgam R))
    (hTS : T ≤ stabilizer R a) (hQT : Q R a ≤ T)
    (hSylow : ∃ S : Sylow 2 (stabilizer R a), (S : Subgroup _) = T.subgroupOf (stabilizer R a)) :
    ∃ E : Subgroup (FreeAmalgam R),
      Subgroup.SmallMover.Maximal (U R a) (Q R a) T 16 = {E} ∧
      (Q R a).relIndex E = 64 ∧
      (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) = 16 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,hψ,hconj,_hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq ha
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  let p := (MovedSection.coverProjection s e).toLinearMap
  have hpj : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro w hw
    have hwc := (hker w).mp hw
    have hwu : j (Multiplicative.ofAdd w) ∈ U R a := hjr ▸
      (show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩)
    have hz : j (Multiplicative.ofAdd w) = 1 := mem_bot.mp (hfixed ▸ ⟨hwu,hwc⟩)
    exact Multiplicative.ofAdd.injective (hj (hz.trans j.map_one.symm))
  let ep : s.space.toSubmodule ≃ₗ[ZMod 2] Vector F.Carrier :=
    LinearEquiv.ofBijective p ⟨hpj,he.1⟩
  let j' := j.comp ep.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  have hj' : Function.Injective j' := hj.comp (fun v w h =>
    Multiplicative.toAdd.injective (ep.symm.injective (congrArg Multiplicative.toAdd h)))
  have hjr' : j'.range = U R a := by
    rw [MonoidHom.range_comp]
    have hep : Function.Surjective ep.symm.toLinearMap.toAddMonoidHom.toMultiplicative := by
      intro v
      obtain ⟨w,hw⟩ := ep.symm.surjective v.toAdd
      exact ⟨Multiplicative.ofAdd w,congrArg Multiplicative.ofAdd hw⟩
    rw [MonoidHom.range_eq_top_of_surjective _ hep,←MonoidHom.range_eq_map,hjr]
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by omega : 2 < Nat.card F.Carrier))).trans
      Subgroup.topEquiv
  let := finite_stabilizer R a
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  let V₀ := (U R a).subgroupOf S
  let T₀ := T.subgroupOf S
  let jS := j'.codRestrict S (fun v => hUS (hjr' ▸ (show j' v ∈ j'.range from ⟨v,rfl⟩)))
  have hjS : Function.Injective jS := fun v w h => hj' (congrArg Subtype.val h)
  have hjSr : jS.range = V₀ := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      change j' v ∈ U R a
      exact hjr' ▸ (show j' v ∈ j'.range from ⟨v,rfl⟩)
    · intro hx
      obtain ⟨v,hv⟩ := (show x.val ∈ j'.range from hjr'.symm ▸ hx)
      exact ⟨v,Subtype.ext hv⟩
  have hact (x : S) v : jS (Multiplicative.ofAdd (MovedSection.ambientAction s e (κ x) v)) =
      x*jS (Multiplicative.ofAdd v)*x⁻¹ := by
    apply Subtype.ext
    have hh : ep.symm (MovedSection.ambientAction s e (κ x) v) =
        s.space.toRepresentation (κ x) (ep.symm v) := by
      apply ep.injective
      rw [ep.apply_symm_apply]
      change _ = MovedSection.coverProjection s e (s.space.toRepresentation (κ x) (ep.symm v))
      rw [MovedSection.coverProjection_ambient]
      change _ = MovedSection.ambientAction s e (κ x) (ep (ep.symm v))
      rw [ep.apply_symm_apply]
    change j (Multiplicative.ofAdd (ep.symm (MovedSection.ambientAction s e (κ x) v))) = _
    rw [hh]
    exact hconj x (ep.symm v)
  have hindex (E : Subgroup S) : (centralizer (E : Set S)).relIndex V₀ =
      Nat.card (Vector F.Carrier ⧸ Representation.BinaryOffender.fixedSpace
        (MovedSection.ambientAction s e) (E.map κ)) := by
    have hi := Representation.BinaryOffender.embedded_centralizer_index
      (MovedSection.ambientAction s e) V₀ E jS hjS hjSr (κ.comp E.subtype)
      (fun x v => hact x.val v)
    rw [MonoidHom.range_comp,range_subtype] at hi
    rw [hi,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rfl
  have hκker : κ.ker = (Q R a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1)]
  have hk : κ.ker ≤ centralizer (V₀ : Set S) := by
    intro x hx u hu
    apply Subtype.val_injective
    have hxQ : x.val ∈ Q R a := hκQ ▸ mem_map_of_mem S.subtype hx
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))
      ((U_le_Z a) hu) x.val hxQ).symm
  obtain ⟨P,hP⟩ := hSylow
  obtain ⟨E,hE,hiE,hmove⟩ := Representation.sylow_smallMover_unique hFc
    ((pResidual 2 H).map q) (hC ▸ bot_le) (e.groupEquiv.trans d)
    (MovedSection.ambientAction s e) hψ
    (fun b v => MovedSection.ambientAction_component s e b v)
    V₀ P κ _hκ (by rw [hκker,hP]; exact comap_mono hQT) hk hindex
  have hmapT : (P : Subgroup S).map S.subtype = T := by
    rw [hP,map_subgroupOf_eq_of_le hTS]
  have hmapV : V₀.map S.subtype = U R a := map_subgroupOf_eq_of_le hUS
  have hfamily : Subgroup.SmallMover.Maximal (U R a) (Q R a) T 16 = {E.map S.subtype} := by
    ext C
    constructor
    · intro hC
      have hCS : C ≤ S := hC.1.1.trans hTS
      have hCm : (C.subgroupOf S).map S.subtype = C := map_subgroupOf_eq_of_le hCS
      have hc' := (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective
        V₀ κ.ker (P : Subgroup S) (C.subgroupOf S) 16).mp
        (by rwa [hmapV,hκQ,hmapT,hCm])
      rw [hE] at hc'
      have heq := Set.mem_singleton_iff.mp hc'
      exact Set.mem_singleton_iff.mpr (hCm.symm.trans (congrArg (Subgroup.map S.subtype) heq))
    · rintro rfl
      have he' : E ∈ Subgroup.SmallMover.Maximal V₀ κ.ker P 16 := hE ▸ Set.mem_singleton E
      have hh := (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective
        V₀ κ.ker (P : Subgroup S) E 16).mpr he'
      rwa [hmapV,hκQ,hmapT] at hh
  refine ⟨E.map S.subtype,hfamily,?_,?_⟩
  · rw [←hκQ,relIndex_map_map_of_injective _ _ S.subtype_injective]
    exact hiE
  · rw [←hmapV,Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective]
    exact hmove
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
