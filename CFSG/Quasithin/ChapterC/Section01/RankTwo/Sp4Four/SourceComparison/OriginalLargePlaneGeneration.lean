module
public import Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSelectedGeneration

/-!
# Original large-image residual generators

Transport the entire original natural seed through its faithful marking.
The canonical plane mover contains the full action kernel. A contained
critical image of order greater than four contains an invertible plane
shear, so an opposite conjugate of the mover and that image generate Sp₄.
Lift the conjugator inside the original residual and recover containment
upstairs through the full kernel.

This supplies the large-image equal-mover positioning used by the original
tensor distance exclusion, without replacing the original core or action.
Source: MS93 (5.5)--(5.11), pp.915--924; Aschbacher--Smith 9.3.10, p.734.
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

/-- The large contained critical image has one actual residual generating
conjugate of the full original plane mover. -/
theorem original_small_mover_large_subactor_generator
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
    (path : DistanceEight.PathCentrality.CriticalPath R geometry a z)
    (hb : 0 < geometry.b R)
    (hza : 4 < (Q R a).relIndex (Z R z))
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥)
    (E : Subgroup (FreeAmalgam R)) (hES : E ≤ stabilizer R a)
    (hQE : Q R a ≤ E) (hEp : IsPGroup 2 E)
    (hEc : (Q R a).relIndex E = 64)
    (hEm : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16)
    (hAE : Z R z ≤ E) :
    ∃ g ∈ Ltilde R a,
      Ltilde R a ≤ E.map (MulAut.conj g).toMonoidHom ⊔ Z R z := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,hψ,hconj,_hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq path.start_color
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
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1)]
  let B := (pResidual 2 H).map q
  let eB : B ≃* Sp F.Carrier := e.groupEquiv.trans d
  let E₀ := E.subgroupOf S
  let A₀ := (Z R z).subgroupOf S
  have hzS : Z R z ≤ S := path.endpoint_Z_le_start_stabilizer hb
  let E₁ := E₀.map κ
  have hE₁c : Nat.card E₁ = 64 := by
    rw [←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm.trans hEc
  have hE₁m : Nat.card (Vector F.Carrier ⧸ fixedSpace (MovedSection.ambientAction s e) E₁) ≤ 16 := by
    rw [←hindex]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective V₀ E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm.trans_le hEm
  have hE₁B : E₁ ≤ B := small_offender_le_symplectic_component hFc B
    (hC ▸ bot_le) eB (MovedSection.ambientAction s e) hψ
    (fun b v => MovedSection.ambientAction_component s e b v) E₁ hE₁m
    (by rw [hE₁c]; omega)
  let E₂ := (E₁.subgroupOf B).map eB.toMonoidHom
  have hE₂c : Nat.card E₂ = 64 := by
    rw [card_map_of_injective eB.injective,
      ←card_map_of_injective B.subtype_injective,map_subgroupOf_eq_of_le hE₁B,hE₁c]
  have hE₂p : IsPGroup 2 E₂ :=
    ((hEp.comap_subtype.map κ).comap_subtype).map eB.toMonoidHom
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)
  let f := B.subtype.comp eB.symm.toMonoidHom
  have hE₂image : E₂.map f = E₁ := by
    rw [map_map]
    have hf : f.comp eB.toMonoidHom = B.subtype := by ext b; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hE₁B]
  have hE₂m : Nat.card (Vector F.Carrier ⧸ fixedSpace σ E₂) ≤ 16 := by
    have hd := fixedCodim_map_equivariant σ (MovedSection.ambientAction s e)
      f (LinearEquiv.refl _ _) (fun g v => by
        change symplecticNatural 2 g v = MovedSection.ambientAction s e (eB.symm g).val v
        rw [MovedSection.ambientAction_component]
        change symplecticNatural 2 g v =
          binaryNatural (e.groupEquiv (e.groupEquiv.symm (d.symm g))) v
        rw [e.groupEquiv.apply_symm_apply]
        rfl) E₂
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 ^ fixedCodim σ E₂ ≤ 16
    rw [hd,hE₂image]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hE₁m
    exact hE₁m
  have hAB : A₀.map κ ≤ B := (map_mono (comap_mono hAE)).trans hE₁B
  let A₂ := ((A₀.map κ).subgroupOf B).map eB.toMonoidHom
  have hA₂E₂ : A₂ ≤ E₂ := map_mono (comap_mono (map_mono (comap_mono hAE)))
  have hA₂card : Nat.card F.Carrier < Nat.card A₂ := by
    rw [hFc,card_map_of_injective eB.injective,
      ←card_map_of_injective B.subtype_injective,map_subgroupOf_eq_of_le hAB,
      ←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) A₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hzS] at hh
    exact hza.trans_eq hh
  obtain ⟨g₀,hmodel⟩ := LargePlaneGeneration.exists_plane_large_subactor_generator E₂ A₂
    (SelectedGeneration.conjugate_plane_of_small_order hFc E₂ hE₂p hE₂c hE₂m)
    hA₂E₂ hA₂card
  obtain ⟨g,hg,hgq⟩ := (show (eB.symm g₀).val ∈ ((Ltilde R a).subgroupOf S).map κ from
    _hκL.symm ▸ (eB.symm g₀).property)
  have hArmap : A₂.map f = A₀.map κ := by
    rw [map_map]
    have hf : f.comp eB.toMonoidHom = B.subtype := by ext b; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hAB]
  have hfr : f.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr eB.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hgen := congrArg (Subgroup.map f) hmodel
  rw [Subgroup.map_sup,image_conjugate,hE₂image,hArmap,←MonoidHom.range_eq_map,hfr] at hgen
  have hmap : ((Ltilde R a).subgroupOf S).map κ ≤
      (E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀).map κ := by
    rw [Subgroup.map_sup,image_conjugate,hgq,_hκL]
    exact hgen.ge
  have hkE : κ.ker ≤ E₀.map (MulAut.conj g).toMonoidHom := by
    intro y hy
    refine ⟨g⁻¹*y*g,?_,?_⟩
    · apply (show κ.ker ≤ E₀ from hκker ▸ comap_mono hQE)
      change κ (g⁻¹*y*g)=1
      simp [show κ y=1 from hy]
    · change g*(g⁻¹*y*g)*g⁻¹=y
      group
  have hcover := map_le_map_iff.mp hmap
  rw [sup_eq_left.mpr (hkE.trans le_sup_left)] at hcover
  have hm := map_mono (f := S.subtype) hcover
  rw [Subgroup.map_sup,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le (Ltilde_le_stabilizer a),
    map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS] at hm
  exact ⟨g.val,hg,hm⟩

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
