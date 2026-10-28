module
public import Theory.SpecificGroups.SymplecticFour.SmallMoverKernel
public import Theory.SpecificGroups.SymplecticFour.PointMoverGeneration
public import Theory.GroupTheory.MarkedConjugateGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction

/-!
# Lift the point-mover selection through the original kernel

Use the bijective natural marking of the entire original seed. An abelian
inner actor with cross index at least sixty-four and moving index above
sixteen is the point radical. Its exact order and the full original actor
order force containment of the entire neighborhood kernel. The prescribed
critical endpoint is a full long root in the same marking. One model
conjugator therefore lifts to an actual residual conjugator and generation
by that neighboring mover and the endpoint seed.

The hypotheses of abelian cross image and placement in the residual times
the kernel remain explicit. They are not consequences asserted here for
arbitrary original movers. The actual overlapping-path application is
GenerationTwoSymplecticAbelianSelection. Source: MS93 (5.5)(c), pp.915--917,
and (5.7), p.919, in the field-four setting of Aschbacher--Smith 9.3.10.
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

/-- An abelian inner cross image with large movement gives the actual
one-root residual generator, and forces containment of the entire kernel. -/
theorem original_large_abelian_mover_root_generator
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
    (hza : (Q R a).relIndex (Z R z) = 4)
    (haz : (Q R z).relIndex (Z R a) = 4)
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥)
    (E : Subgroup (FreeAmalgam R)) (hES : E ≤ stabilizer R a)
    (hEp : IsPGroup 2 E)
    (hEc : 64 ≤ (Q R a).relIndex E)
    (hfull : Nat.card E = Nat.card (Q R a) * 64)
    (hEin : E ≤ Ltilde R a ⊔ Q R a)
    (hcomm : ⁅E,E⁆ ≤ Q R a)
    (hEm : 16 < (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a)) :
    Q R a ≤ E ∧ ∃ g ∈ Ltilde R a,
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
  have hE₁index : Nat.card E₁ = (Q R a).relIndex E := by
    rw [←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm
  have hE₁m : 16 < Nat.card (Vector F.Carrier ⧸ fixedSpace (MovedSection.ambientAction s e) E₁) := by
    rw [←hindex]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective V₀ E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
    exact hEm.trans_eq hh
  have hE₁B : E₁ ≤ B := by
    have hE₀ : E₀ ≤ (Ltilde R a).subgroupOf S ⊔ κ.ker := by
      rw [hκker,←subgroupOf_sup (Ltilde_le_stabilizer a)
        (show Q R a ≤ S from fun _ hx => hx.1)]
      exact comap_mono hEin
    have hm := map_mono (f := κ) hE₀
    have hmapL : ((Ltilde R a).subgroupOf S).map κ = B := _hκL
    simpa only [Subgroup.map_sup,hmapL,Subgroup.map_ker_self,sup_bot_eq] using hm
  let : IsMulCommutative E₁ := by
    apply commutator_self_eq_bot_iff.mp
    apply le_bot_iff.mp
    rw [←map_commutator]
    apply (map_le_iff_le_comap).mpr
    change ⁅E₀,E₀⁆ ≤ κ.ker
    rw [hκker]
    apply (map_le_iff_le_comap).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hES]
    exact hcomm
  let E₂ := (E₁.subgroupOf B).map eB.toMonoidHom
  have hE₂index : Nat.card E₂ = (Q R a).relIndex E := by
    rw [card_map_of_injective eB.injective,
      ←card_map_of_injective B.subtype_injective,map_subgroupOf_eq_of_le hE₁B,hE₁index]
  have hE₂p : IsPGroup 2 E₂ :=
    ((hEp.comap_subtype.map κ).comap_subtype).map eB.toMonoidHom
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)
  let f := B.subtype.comp eB.symm.toMonoidHom
  have hE₂image : E₂.map f = E₁ := by
    rw [map_map]
    have hf : f.comp eB.toMonoidHom = B.subtype := by ext b; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hE₁B]
  have hE₂m : 16 < Nat.card (Vector F.Carrier ⧸ fixedSpace σ E₂) := by
    have hd := fixedCodim_map_equivariant σ (MovedSection.ambientAction s e)
      f (LinearEquiv.refl _ _) (fun g v => by
        change symplecticNatural 2 g v = MovedSection.ambientAction s e (eB.symm g).val v
        rw [MovedSection.ambientAction_component]
        change symplecticNatural 2 g v =
          binaryNatural (e.groupEquiv (e.groupEquiv.symm (d.symm g))) v
        rw [e.groupEquiv.apply_symm_apply]
        rfl) E₂
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 16 < 2 ^ fixedCodim σ E₂
    rw [hd,hE₂image]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hE₁m
    exact hE₁m
  obtain ⟨hE₂c,hpoint⟩ := SelectedGeneration.conjugate_point_of_large_abelian hFc E₂ hE₂p
    (hE₂index.symm ▸ hEc) hE₂m
  have hindex64 : (Q R a).relIndex E = 64 := hE₂index.symm.trans hE₂c
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ S from fun _ hx => hx.1)) (inclusion_injective _)
  have hQE : Q R a ≤ E := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
      (E ⊓ Q R a) E bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hindex64,hfull] at hm
    have heq : E ⊓ Q R a = Q R a := eq_of_le_of_card_ge inf_le_right (by omega)
    exact heq ▸ inf_le_left
  let rev : DistanceEight.PathCentrality.CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry (MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith)
        a path.start_color (by rwa [geometry.distance_constant a path.start_color])
        z path.end_color path.critical }
  let δ := κ.comp (inclusion hzS)
  have hδcard : Nat.card δ.range = 4 :=
    (quotient_image_card _ _ _ hzS κ hκQ).trans hza
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor rev hb
    (C_eq_Q R hp hQR hfaith z path.end_color) hFc s e he hC j hj hjr δ
    (fun x v => hconj (inclusion hzS x) v) hδcard haz
  have hδrange : δ.range = A₀.map κ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact x.property
    · intro hy
      exact ⟨⟨y.val,hy⟩,rfl⟩
  have hAB : A₀.map κ ≤ B := by
    rw [←hδrange]
    rintro _ ⟨u,rfl⟩
    exact hβmark u ▸ (e.groupEquiv.symm (β u)).property
  have hAr : ((A₀.map κ).subgroupOf B).map eB.toMonoidHom =
      β.range.map (commutator (Sp F.Carrier)).subtype := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨w,hw⟩ := (show u.val ∈ δ.range from hδrange.symm ▸ hu)
      have hu' : u = e.groupEquiv.symm (β w) := Subtype.ext (hw.symm.trans (hβmark w).symm)
      refine ⟨β w,⟨w,rfl⟩,?_⟩
      rw [hu']
      change (β w).val = d (e.groupEquiv (e.groupEquiv.symm (β w)))
      rw [e.groupEquiv.apply_symm_apply]
      rfl
    · rintro ⟨u,⟨w,rfl⟩,rfl⟩
      refine ⟨e.groupEquiv.symm (β w),?_,?_⟩
      · change (e.groupEquiv.symm (β w)).val ∈ A₀.map κ
        rw [hβmark,←hδrange]
        exact ⟨w,rfl⟩
      · change d (e.groupEquiv (e.groupEquiv.symm (β w))) = (β w).val
        rw [e.groupEquiv.apply_symm_apply]
        rfl
  have hArcard : Nat.card (β.range.map (commutator (Sp F.Carrier)).subtype) = 4 := by
    rw [card_map_of_injective (commutator (Sp F.Carrier)).subtype_injective,hβcard]
  obtain ⟨g₀,hmodel⟩ := SelectedGeneration.exists_point_root_generator E₂
    (((A₀.map κ).subgroupOf B).map eB.toMonoidHom) hpoint
    (FourLongRoots.exists_conjugate_root_of_displacement_one _
      (by rw [hAr]; exact hArcard.trans hFc.symm)
      (by rw [hAr]; exact hd) (by rw [hAr]; exact hquad))
  have hmodel' : (E₂.map (MulAut.conj g₀).toMonoidHom ⊔
      ((A₀.map κ).subgroupOf B).map eB.toMonoidHom) ⊔
      (((A₀.map κ).subgroupOf B).map eB.toMonoidHom).map
        (MulAut.conj (1 : Sp F.Carrier)).toMonoidHom = ⊤ := by
    rw [hmodel,top_sup_eq]
  obtain ⟨g,hg,x,hx,hgq,hxq,hgen⟩ := Subgroup.lift_two_conjugate_generators_with_marking κ B eB
    ((Ltilde R a).subgroupOf S) E₀ A₀ _hκL hE₁B hAB
    (by rw [hκker]; exact comap_mono hQE) g₀ 1 hmodel'
  have hxker : x ∈ κ.ker := by simpa using hxq
  have hxE : x ∈ E₀.map (MulAut.conj g).toMonoidHom := by
    refine ⟨g⁻¹*x*g,?_,?_⟩
    · apply (show κ.ker ≤ E₀ from by rw [hκker]; exact comap_mono hQE)
      change κ (g⁻¹*x*g)=1
      simp [show κ x=1 from hxker]
    · change g*(g⁻¹*x*g)*g⁻¹=x
      group
  have hAx : A₀.map (MulAut.conj x).toMonoidHom ≤
      E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀ := by
    rintro y ⟨z,hz,rfl⟩
    exact mul_mem (mul_mem (mem_sup_left hxE) (mem_sup_right hz))
      (inv_mem (mem_sup_left hxE))
  have hgen' := hgen.trans (sup_le le_rfl hAx)
  have hm := map_mono (f := S.subtype) hgen'
  rw [Subgroup.map_sup,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le (show Ltilde R a ≤ S from Ltilde_le_stabilizer a),
    map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS] at hm
  exact ⟨hQE,g.val,hg,hm⟩
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
