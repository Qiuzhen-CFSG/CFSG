module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSelectedGeneration
public import Theory.SpecificGroups.SymplecticFour.GeneratedRootMovement

/-!
# Root movement under the original three residual generators

The original natural cover, with its residual fixed kernel trivial, gives
an injective marking of the whole moved layer. The canonical small mover
and reciprocal critical root lie in its actual symplectic component. If
the mover centralized the critical commutator, its quadratic fixed plane
would also be fixed by the root. The remaining conjugate root leaves a
nonzero fixed vector in that plane, contradicting residual generation.

All conjugation maps and the full neighborhood kernel are retained. This
is the original-action application of GeneratedRootMovement; the tensor
consumer is GenerationTwoSymplecticPairedImageExclusion. Source: MS93
(3.3), (5.6)--(5.11), pp.867,917--924, in the field-four specialization of
Aschbacher--Smith 9.3.10, p.734.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_generated_root_not_centralized
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
    (_hQE : Q R a ≤ E) (hEp : IsPGroup 2 E)
    (hEc : (Q R a).relIndex E = 64)
    (hEm : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16)
    (hEquad : ⁅E,U R a⁆ ≤ centralizer (E : Set (FreeAmalgam R)))
    (x : FreeAmalgam R) (hx : x ∈ Ltilde R a)
    (hgen : Ltilde R a ≤ (E ⊔ Z R z) ⊔ (Z R z).map (MulAut.conj x).toMonoidHom) :
    ¬ ⁅Z R z,U R a⁆ ≤ centralizer (E : Set (FreeAmalgam R)) := by
  intro hbad

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
    rw [Subgroup.map_map]
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
  let A₂ := ((A₀.map κ).subgroupOf B).map eB.toMonoidHom
  have hA₂image : A₂.map f = A₀.map κ := by
    rw [Subgroup.map_map]
    have hf : f.comp eB.toMonoidHom = B.subtype := by ext b; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hAB]
  let xs : S := ⟨x,Ltilde_le_stabilizer a hx⟩
  have hxB : κ xs ∈ B := by
    change κ xs ∈ (pResidual 2 H).map q
    rw [←_hκL]
    exact mem_map_of_mem κ (show xs ∈ (Ltilde R a).subgroupOf S from hx)
  let x₀ := eB ⟨κ xs,hxB⟩
  have hx₀ : f x₀ = κ xs := by
    change (eB.symm (eB ⟨κ xs,hxB⟩)).val = κ xs
    rw [eB.symm_apply_apply]
  have hgenS : (Ltilde R a).subgroupOf S ≤
      (E₀ ⊔ A₀) ⊔ A₀.map (MulAut.conj xs).toMonoidHom := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le (show Ltilde R a ≤ S from Ltilde_le_stabilizer a),
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS]
    exact hgen
  have hgenκ := map_mono (f := κ) hgenS
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,_hκL] at hgenκ
  have hmodel : (E₂ ⊔ A₂) ⊔ A₂.map (MulAut.conj x₀).toMonoidHom = ⊤ := by
    have him : ((E₂ ⊔ A₂) ⊔ A₂.map (MulAut.conj x₀).toMonoidHom).map f =
        (E₁ ⊔ A₀.map κ) ⊔ (A₀.map κ).map (MulAut.conj (κ xs)).toMonoidHom := by
      rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,hE₂image,hA₂image,hx₀]
    apply eq_top_iff.mpr
    intro y _
    have hfy : f y ∈ B := (eB.symm y).property
    obtain ⟨u,hu,he⟩ := (show f y ∈ ((E₂ ⊔ A₂) ⊔ A₂.map (MulAut.conj x₀).toMonoidHom).map f
      from him.symm ▸ hgenκ hfy)
    have hfi : Function.Injective f := B.subtype_injective.comp eB.symm.injective
    exact hfi he ▸ hu
  have hfAct (y : Sp F.Carrier) (v : Vector F.Carrier) :
      MovedSection.ambientAction s e (f y) v = y • v := by
    change MovedSection.ambientAction s e (eB.symm y).val v = y • v
    rw [MovedSection.ambientAction_component]
    change binaryNatural (e.groupEquiv (e.groupEquiv.symm (d.symm y))) v = y • v
    rw [e.groupEquiv.apply_symm_apply]
    rfl
  have lift {Y : Subgroup S} {Y₂ : Subgroup (Sp F.Carrier)}
      (him : Y₂.map f = Y.map κ) {y : Sp F.Carrier} (hy : y ∈ Y₂) :
      ∃ u : S, u ∈ Y ∧ κ u = f y := by
    exact (show f y ∈ Y.map κ from him ▸ mem_map_of_mem f hy)
  have displacement (y : Sp F.Carrier) (u : S) (hu : κ u = f y) (v : Vector F.Carrier) :
      jS (Multiplicative.ofAdd (y • v-v)) = ⁅u,jS (Multiplicative.ofAdd v)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,←hfAct,←hu,hact]
    rfl
  have fixed (v : Vector F.Carrier) (hv : jS (Multiplicative.ofAdd v) ∈ centralizer (E₀ : Set S)) :
      v ∈ Theory.SpecificGroups.SymplecticFour.TwoLocalCover.fixedSpace E₂ := by
    intro y hy
    obtain ⟨u,hu,he⟩ := lift hE₂image hy
    apply Multiplicative.ofAdd.injective
    apply hjS
    rw [←hfAct,←he,hact]
    exact (mul_inv_eq_iff_eq_mul).mpr (hv u hu)
  have central_lift (Y : Subgroup S)
      (hh : ⁅Y.map S.subtype,U R a⁆ ≤ centralizer (E : Set (FreeAmalgam R))) :
      ⁅Y,V₀⁆ ≤ centralizer (E₀ : Set S) := by
    intro y hy u hu
    apply Subtype.val_injective
    apply hh ?_ u.val hu
    have hy' := mem_map_of_mem S.subtype hy
    rw [map_commutator,map_subgroupOf_eq_of_le hUS] at hy'
    exact hy'
  have hEq : ⁅E₀,V₀⁆ ≤ centralizer (E₀ : Set S) := central_lift E₀
    (by rwa [map_subgroupOf_eq_of_le hES])
  have hAq : ⁅A₀,V₀⁆ ≤ centralizer (E₀ : Set S) := central_lift A₀
    (by rwa [map_subgroupOf_eq_of_le hzS])
  have hquad : ∀ y ∈ E₂, ∀ z ∈ E₂, ∀ v : Vector F.Carrier,
      y • (z • v-v) = z • v-v := by
    intro y hy z hz v
    obtain ⟨u,hu,he⟩ := lift hE₂image hz
    apply fixed _ ?_ y hy
    rw [displacement z u he]
    apply hEq
    apply commutator_mem_commutator hu
    rw [←hjSr]
    exact ⟨_,rfl⟩
  have hrootFixed : displacementSpace A₂ ≤ Theory.SpecificGroups.SymplecticFour.TwoLocalCover.fixedSpace E₂ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y,v⟩,rfl⟩
    obtain ⟨u,hu,he⟩ := lift hA₂image y.property
    apply fixed (y.val • v-v)
    rw [displacement y.val u he]
    apply hAq
    apply commutator_mem_commutator hu
    rw [←hjSr]
    exact ⟨_,rfl⟩
  apply generated_root_displacement_not_fixed E₂ A₂
    (A₂.map (MulAut.conj x₀).toMonoidHom) hquad (by rw [hE₂c,hFc]; decide) ?_ hmodel hrootFixed
  rw [displacementSpace_conjugate,(toLinear x₀).finrank_map_eq]
  change Module.finrank F.Carrier (displacementSpace (((A₀.map κ).subgroupOf B).map eB.toMonoidHom)) ≤ 1
  rw [hAr,hd]

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
