module
public import Theory.SpecificGroups.SymplecticFour.SmallMoverKernel
public import Theory.SpecificGroups.SymplecticFour.SelectedPositioning
public import Theory.GroupTheory.MarkedConjugateGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction

/-!
# Lift the selected root generators to the original residual

A trivial fixed kernel identifies the whole original moved layer with its
natural symplectic module. The small mover and reciprocal critical root
then lie in the same marked component. Their model generators lift inside
the literal residual, with the entire centralizer kernel retained.

The same original conjugators also have zero common centralizer in the
whole natural layer. When the endpoint seed lies in the original mover,
the selected conjugator normalizes that whole mover: the exact marked
image lifts through the full kernel already contained in the mover. This
proves the simultaneous generation, separation and parabolic positioning
clauses of MS93 (5.6)(b--d), printed p.917, in the reciprocal-index-four
branch. The actual tensor consumers are GenerationTwoSymplecticSelectedGeneration
and GenerationTwoSymplecticPositionedSelection.
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

/-- The original small mover gives simultaneous generation, fixed-plane
separation and full-mover normalization when it contains the endpoint seed. -/
theorem original_small_mover_root_positioned_generators
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
    (hQE : Q R a ≤ E) (hEp : IsPGroup 2 E)
    (hEc : (Q R a).relIndex E = 64)
    (hEm : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16) :
    ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
      Ltilde R a ≤ (E.map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
        (Z R z).map (MulAut.conj x).toMonoidHom ∧
      (U R a ⊓ centralizer (E.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam R))) ⊓
        centralizer ((E.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam R)) = ⊥ ∧
      (Z R z ≤ E → x ∈ normalizer (E : Set (FreeAmalgam R))) := by
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
  obtain ⟨g₀,x₀,hmodel,hseparate,hposition⟩ := SelectedPositioning.exists_small_mover_positioned_generators hFc E₂
    (((A₀.map κ).subgroupOf B).map eB.toMonoidHom) hE₂p hE₂c hE₂m
    (by rw [hAr]; exact hArcard) (by rw [hAr]; exact hd) (by rw [hAr]; exact hquad)
  obtain ⟨g,hg,x,hx,hgq,hxq,hgen⟩ := Subgroup.lift_two_conjugate_generators_with_marking κ B eB
    ((Ltilde R a).subgroupOf S) E₀ A₀ _hκL hE₁B hAB
    (by rw [hκker]; exact comap_mono hQE) g₀ x₀ hmodel
  refine ⟨g.val,hg,x.val,hx,?_,?_,?_⟩
  · have hm := map_mono (f := S.subtype) hgen
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le (show Ltilde R a ≤ S from Ltilde_le_stabilizer a),
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS] at hm
    exact hm
  · let E₃ := E₀.map (MulAut.conj g).toMonoidHom
    let E₄ := E₃.map (MulAut.conj x⁻¹).toMonoidHom
    have hE₃ : E₃.map S.subtype = E.map (MulAut.conj g.val).toMonoidHom := by
      rw [Subgroup.image_conjugate,map_subgroupOf_eq_of_le hES]
      rfl
    have hE₄ : E₄.map S.subtype = (E.map (MulAut.conj g.val).toMonoidHom).map
        (MulAut.conj x.val⁻¹).toMonoidHom := by
      rw [Subgroup.image_conjugate,hE₃]
      rfl
    have hi₃ : (E₂.map (MulAut.conj g₀).toMonoidHom).map f = E₃.map κ := by
      rw [Subgroup.image_conjugate,Subgroup.image_conjugate,hE₂image,hgq]
      rfl
    have hi₄ : ((E₂.map (MulAut.conj g₀).toMonoidHom).map
        (MulAut.conj x₀⁻¹).toMonoidHom).map f = E₄.map κ := by
      calc
        _ = (E₃.map κ).map (MulAut.conj (f x₀⁻¹)).toMonoidHom := by
          rw [Subgroup.image_conjugate,hi₃]
        _ = (E₃.map κ).map (MulAut.conj (κ x⁻¹)).toMonoidHom := by
          rw [map_inv f x₀,map_inv κ x,hxq]
          rfl
        _ = _ := (Subgroup.image_conjugate κ E₃ x⁻¹).symm
    have hfAct (y : Sp F.Carrier) (v : Vector F.Carrier) :
        MovedSection.ambientAction s e (f y) v = y • v := by
      change MovedSection.ambientAction s e (eB.symm y).val v = y • v
      rw [MovedSection.ambientAction_component]
      change binaryNatural (e.groupEquiv (e.groupEquiv.symm (d.symm y))) v = y • v
      rw [e.groupEquiv.apply_symm_apply]
      rfl
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨v,hv⟩ := (show w ∈ j'.range from hjr'.symm ▸ hw.1.1)
    have fix (K : Subgroup S) (A : Subgroup (Sp F.Carrier))
        (hi : A.map f = K.map κ)
        (hc : w ∈ centralizer (K.map S.subtype : Set (FreeAmalgam R))) :
        ∀ y ∈ A, y • v.toAdd = v.toAdd := by
      intro y hy
      obtain ⟨u,hu,he⟩ := (show f y ∈ K.map κ from hi ▸ mem_map_of_mem f hy)
      apply Multiplicative.ofAdd.injective
      apply hjS
      change jS (Multiplicative.ofAdd (y • v.toAdd)) = jS v
      rw [←hfAct,←he,hact]
      apply Subtype.ext
      change u.val*j' v*u.val⁻¹ = j' v
      rw [hv]
      have hcomm := hc u.val (mem_map_of_mem S.subtype hu)
      exact (mul_inv_eq_iff_eq_mul).mpr hcomm
    have hz := hseparate v.toAdd (fix E₃ _ hi₃ (hE₃.symm ▸ hw.1.2))
      (fix E₄ _ hi₄ (hE₄.symm ▸ hw.2))
    have hvone : v = 1 := Multiplicative.toAdd.injective hz
    rw [←hv,hvone,map_one]
    exact one_mem _

  · intro hzE
    have hAE : ((A₀.map κ).subgroupOf B).map eB.toMonoidHom ≤ E₂ :=
      map_mono (comap_mono (map_mono (comap_mono hzE)))
    have hxN : κ x ∈ normalizer (E₀.map κ : Set J) := by
      rw [hxq]
      change f x₀ ∈ normalizer (E₁ : Set J)
      rw [←hE₂image]
      exact E₂.le_normalizer_map f (mem_map_of_mem f (hposition hAE))
    have hkerE : κ.ker ≤ E₀ := by rw [hκker]; exact comap_mono hQE
    have hxE : x ∈ normalizer (E₀ : Set S) := by
      have hn := (E₀.map κ).le_normalizer_comap κ hxN
      rwa [comap_map_eq_self hkerE] at hn
    have hn := E₀.le_normalizer_map S.subtype (mem_map_of_mem S.subtype hxE)
    rwa [map_subgroupOf_eq_of_le hES] at hn

/-- The previous generation and separation interface is retained. -/
theorem original_small_mover_root_separated_generators
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
    (hQE : Q R a ≤ E) (hEp : IsPGroup 2 E)
    (hEc : (Q R a).relIndex E = 64)
    (hEm : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16) :
    ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
      Ltilde R a ≤ (E.map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
        (Z R z).map (MulAut.conj x).toMonoidHom ∧
      (U R a ⊓ centralizer (E.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam R))) ⊓
        centralizer ((E.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam R)) = ⊥ := by
  obtain ⟨g,hg,x,hx,hgen,hsep,_⟩ := original_small_mover_root_positioned_generators
    R hms hp hne hQR hself hfaith q hq hcore hc hC hsq path hb hza haz hfixed
    E hES hQE hEp hEc hEm
  exact ⟨g,hg,x,hx,hgen,hsep⟩

/-- The original small mover and two endpoint conjugates generate the residual,
with the full quotient kernel retained. -/
theorem original_small_mover_root_generators
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
    (hQE : Q R a ≤ E) (hEp : IsPGroup 2 E)
    (hEc : (Q R a).relIndex E = 64)
    (hEm : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16) :
    ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
      Ltilde R a ≤ (E.map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
        (Z R z).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨g,hg,x,hx,hgen,_⟩ := original_small_mover_root_separated_generators
    R hms hp hne hQR hself hfaith q hq hcore hc hC hsq path hb hza haz hfixed
    E hES hQE hEp hEc hEm
  exact ⟨g,hg,x,hx,hgen⟩
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)
omit [Finite M] in
/-- The source small-mover join follows the literal inverse-conjugation action. -/
theorem smallMoverJoin_act (g : FreeAmalgam R) (a t : Vertex R) :
    LocalPackage.J R (act R g a) (act R g t) =
      (LocalPackage.J R a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  change Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
    (Q R (act R g t)) 16 = _
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
