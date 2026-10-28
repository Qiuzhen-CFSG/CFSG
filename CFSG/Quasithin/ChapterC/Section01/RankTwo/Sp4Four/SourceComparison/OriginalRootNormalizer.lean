module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalCriticalResidual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.TwoNormalizer
public import Theory.Representation.SymplecticNaturalNormalizer.NormalMover
public import Theory.GroupTheory.Commutator.ElementaryQuotientIndexTwoQuadratic
public import Mathlib.GroupTheory.Frattini

/-!
# Normalizers of original critical roots with outer action retained

A two-subgroup in the full residual preimage that normalizes a critical
root of order four centralizes its image. The proof uses the actual
symplectic marking and pulls back through the entire original vertex kernel.
The ambient natural normalizer has component index at most two, so every
local actor's Frattini subgroup belongs to that same preimage. Its remaining
index-two action on the elementary critical image is quadratic.

The original-radius consumer is GenerationTwoSymplecticRadiusKernelAction.
These bounds retain possible outer field involutions: they do not assert
that the full normalizing actor centralizes the root image. That stronger
inference in MS93 (5.2)(ii) uses the full inner local quotient in (5.0).

Source: MS93 (5.0), (5.2)(ii), printed pp.912--915; the ambient extension
uses the natural-normalizer calculation in Aschbacher--Smith H.7,
printed pp.388--389, in the original tensor setting of 9.3.10, p.734.
-/

open scoped IsMulCommutative commutatorElement
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Inner local two-subgroups centralize a small critical image through
the exact original endpoint kernel. -/
theorem original_small_critical_inner_normalizer_commutator
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
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (P : Subgroup (FreeAmalgam R)) (hP : IsPGroup 2 P)
    (hPS : P ≤ stabilizer R z)
    (hinner : P ≤ Ltilde R z ⊔ Q R z)
    (hn : P ≤ normalizer (Z R a : Set (FreeAmalgam R)))
    (hsmall : (Q R z).relIndex (Z R a) < 16) :
    ⁅Z R a,P⁆ ≤ Q R z := by
  obtain ⟨ha4,hz4⟩ := original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb hsmall
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,hκL,_hψ,hconj,_hproj,_hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z R a →* J := κ.comp (inclusion hAS)
  have hδcard : Nat.card δ.range = 4 :=
    (quotient_image_card _ _ _ hAS κ hκQ).trans ha4
  have hCa := C_eq_Q R hp hQR hfaith a path.start_color
  obtain ⟨β,hβcard,hβmark,_hβ,hd,hquad⟩ := critical_inner_root_actor path hb hCa hFc s e he hC
    j hj hjr δ (fun x v => hconj (inclusion hAS x) v) hδcard hz4
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top
        (by omega : 2 < Nat.card F.Carrier))).trans Subgroup.topEquiv
  let B := (pResidual 2 H).map q
  let eB : B ≃* Sp F.Carrier := e.groupEquiv.trans d
  let i : Sp F.Carrier →* J := B.subtype.comp eB.symm.toMonoidHom
  have hi : Function.Injective i := B.subtype_injective.comp eB.symm.injective
  let α : Z R a →* Sp F.Carrier := d.toMonoidHom.comp β
  have hiα (x : Z R a) : i (α x) = δ x := by
    change (e.groupEquiv.symm (d.symm (d (β x))) : J) = δ x
    rw [d.symm_apply_apply]
    exact hβmark x
  have hαrange : α.range = β.range.map (commutator (Sp F.Carrier)).subtype := by
    rw [MonoidHom.range_comp]
    rfl
  have hαcard : Nat.card α.range = Nat.card F.Carrier := by
    rw [hαrange,card_map_of_injective (commutator (Sp F.Carrier)).subtype_injective,hβcard,hFc]
  have hκker : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
    rw [←hκQ,subgroupOf_map_subtype_eq]
  have hPB : ∀ y : P, κ (inclusion hPS y) ∈ B := by
    have hN : (P.subgroupOf (stabilizer R z)).map κ ≤ B := by
      have hh := map_mono (f := κ) (comap_mono (f := (stabilizer R z).subtype) hinner)
      rw [←comap_sup_eq_of_le_range (stabilizer R z).subtype
        (by rw [range_subtype]; exact Ltilde_le_stabilizer z)
        (by rw [range_subtype]; exact fun _ hx => hx.1),Subgroup.map_sup] at hh
      change (P.subgroupOf (stabilizer R z)).map κ ≤
        ((Ltilde R z).subgroupOf (stabilizer R z)).map κ ⊔
          ((Q R z).subgroupOf (stabilizer R z)).map κ at hh
      rw [hκL,←hκker,Subgroup.map_ker_self,sup_bot_eq] at hh
      exact hh
    intro y
    exact hN (mem_map_of_mem κ y.property)
  let ψ : P →* Sp F.Carrier := eB.toMonoidHom.comp
    ((κ.comp (inclusion hPS)).codRestrict B hPB)
  have hiψ (y : P) : i (ψ y) = κ (inclusion hPS y) := by
    change (eB.symm (eB ⟨κ (inclusion hPS y),hPB y⟩) : J) = _
    rw [eB.symm_apply_apply]
  have hn' : ψ.range ≤ normalizer (α.range : Set (Sp F.Carrier)) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨y,rfl⟩ _ ⟨x,rfl⟩
    let w : Z R a := ⟨y.val*x.val*y.val⁻¹,
      (mem_normalizer_iff.mp (hn y.property) x.val).mp x.property⟩
    refine ⟨w,?_⟩
    apply hi
    rw [hiα,map_mul,map_mul,map_inv,hiψ,hiα]
    change κ (inclusion hAS w) =
      κ (inclusion hPS y)*κ (inclusion hAS x)*(κ (inclusion hPS y))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
  have hcent := two_subgroup_normalizing_displacement_line_centralizes α.range ψ.range
    (hP.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective) hn' hαcard
    (hαrange.symm ▸ hd) (hαrange.symm ▸ hquad)
  apply commutator_le.mpr
  intro x hx y hy
  let xx := inclusion hAS ⟨x,hx⟩
  let yy := inclusion hPS ⟨y,hy⟩
  have hcomm := congrArg i (hcent ⟨⟨y,hy⟩,rfl⟩ _ ⟨⟨x,hx⟩,rfl⟩)
  simp only [map_mul,hiα,hiψ] at hcomm
  have hkxy : ⁅xx,yy⁆ ∈ κ.ker := by
    change κ ⁅xx,yy⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  exact hκQ ▸ (mem_map_of_mem (stabilizer R z).subtype hkxy)

/-- Every local subgroup has at most two cosets over the full residual preimage. -/
theorem original_local_outer_index_le_two
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
    {z : Vertex R} (hz : color R z = false)
    (P : Subgroup (FreeAmalgam R)) (hPS : P ≤ stabilizer R z) :
    (Ltilde R z ⊔ Q R z).relIndex P ≤ 2 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,_he,_j,_hj,_hjr,κ,_hκ,hκQ,_hκC,hκL,_hψ,_hconj,_hproj,_hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq hz
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top
        (by omega : 2 < Nat.card F.Carrier))).trans Subgroup.topEquiv
  let B := (pResidual 2 H).map q
  have hi : B.index ≤ 2 := SymplecticNaturalNormalizer.component_index_le_two hFc B
    (hC.le.trans bot_le) (e.groupEquiv.trans d) (MovedSection.ambientAction s e)
    (fun b v => MovedSection.ambientAction_component s e b v)
  have hpre : (B.comap κ).map (stabilizer R z).subtype = Ltilde R z ⊔ Q R z := by
    change (((pResidual 2 H).map q).comap κ).map (stabilizer R z).subtype = _
    rw [←hκL,comap_map_eq,Subgroup.map_sup,
      map_subgroupOf_eq_of_le (Ltilde_le_stabilizer z),hκQ]
  have hi' : (B.comap κ).relIndex (P.subgroupOf (stabilizer R z)) ≤ 2 := by
    rw [relIndex_comap]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      (relIndex_dvd_index_of_normal B _)).trans hi
  have hh := relIndex_map_map_of_injective (B.comap κ)
    (P.subgroupOf (stabilizer R z)) (stabilizer R z).subtype_injective
  rw [hpre,map_subgroupOf_eq_of_le hPS] at hh
  exact hh.symm ▸ hi'

/-- The actual Frattini subgroup of a local actor belongs to the residual
preimage, even when the actor has outer field action. -/
theorem original_local_frattini_le_residual_sup_kernel
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
    {z : Vertex R} (hz : color R z = false)
    (P : Subgroup (FreeAmalgam R)) (hPS : P ≤ stabilizer R z) :
    (frattini P).map P.subtype ≤ Ltilde R z ⊔ Q R z := by
  let := finite_stabilizer R z
  let : Finite P := Finite.of_injective (inclusion hPS) (inclusion_injective hPS)
  let N := (Ltilde R z ⊔ Q R z).subgroupOf P
  have hi : N.index ≤ 2 := original_local_outer_index_le_two R hms hp hne hQR hself
    hfaith q hq hcore hc hC hsq hz P hPS
  have hphi : frattini P ≤ N := by
    by_cases hN : N = ⊤
    · rw [hN]; exact le_top
    apply frattini_le_coatom
    refine ⟨hN,?_⟩
    intro B hB
    have hs := index_strictAnti hB
    have hz := B.index_ne_zero_of_finite
    exact index_eq_one.mp (by omega)
  rintro _ ⟨x,hx,rfl⟩
  exact hphi hx

/-- Small critical roots admit quadratic normalizer action, and their action
kills the full Frattini subgroup. No inner hypothesis on P is required. -/
theorem original_small_critical_normalizer_bounds
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
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (P : Subgroup (FreeAmalgam R)) (hP : IsPGroup 2 P)
    (hPS : P ≤ stabilizer R z)
    (hn : P ≤ normalizer (Z R a : Set (FreeAmalgam R)))
    (hsmall : (Q R z).relIndex (Z R a) < 16) :
    ⁅Z R a,(frattini P).map P.subtype⁆ ≤ Q R z ∧
      ⁅⁅Z R a,P⁆,P⁆ ≤ Q R z := by
  let N := P ⊓ (Ltilde R z ⊔ Q R z)
  have hNP : N ≤ P := inf_le_left
  have hphiP : (frattini P).map P.subtype ≤ P := map_subtype_le _
  have hphi : ⁅Z R a,(frattini P).map P.subtype⁆ ≤ Q R z :=
    original_small_critical_inner_normalizer_commutator R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq path hb _ (hP.to_subgroup _ |>.map P.subtype)
      (hphiP.trans hPS)
      (original_local_frattini_le_residual_sup_kernel R hms hp hne hQR hself hfaith
        q hq hcore hc hC hsq path.end_color P hPS) (hphiP.trans hn) hsmall
  refine ⟨hphi,?_⟩
  have hN : ⁅Z R a,N⁆ ≤ Q R z :=
    original_small_critical_inner_normalizer_commutator R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq path hb N
      (hP.of_injective (inclusion hNP) (inclusion_injective hNP)) (hNP.trans hPS)
      inf_le_right (hNP.trans hn) hsmall
  let := finite_stabilizer R z
  let : Finite P := Finite.of_injective (inclusion hPS) (inclusion_injective hPS)
  have hi : N.relIndex P ≤ 2 := by
    change (P ⊓ (Ltilde R z ⊔ Q R z)).relIndex P ≤ 2
    rw [inf_relIndex_left]
    exact original_local_outer_index_le_two R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq path.end_color P hPS
  have hpos : 0 < N.relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
  by_cases hone : N.relIndex P = 1
  · have hPN : P ≤ N := relIndex_eq_one.mp hone
    have hPQ : ⁅Z R a,P⁆ ≤ Q R z := (commutator_mono le_rfl hPN).trans hN
    exact (commutator_mono hPQ le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hPS.trans (Q_normalized R z)))
  have htwo : N.relIndex P = 2 := by omega
  let W := Z R a ⊓ Q R z
  have hZN : (W.subgroupOf (Z R a)).Normal := by
    have hAS : Z R a ≤ stabilizer R z :=
      Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
    have hh := normal_subgroupOf_of_le_normalizer (hAS.trans (Q_normalized R z))
    simpa only [W,inf_subgroupOf_left] using hh
  have hPW : P ≤ normalizer (W : Set (FreeAmalgam R)) :=
    (le_inf hn (hPS.trans (Q_normalized R z))).trans inf_normalizer_le_normalizer_inf
  let := hZN
  let := geometry.Z_elementary hb a path.start_color
  let : IsElementaryAbelian 2 (Z R a ⧸ W.subgroupOf (Z R a)) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  exact (commutator_commutator_le_of_elementary_quotient_index_two (Z R a) W N P
    inf_le_left hn hPW hZN inferInstance hNP htwo
    (le_inf (le_normalizer_iff_commutator_le_left.mp (hNP.trans hn)) hN)).trans inf_le_right

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
