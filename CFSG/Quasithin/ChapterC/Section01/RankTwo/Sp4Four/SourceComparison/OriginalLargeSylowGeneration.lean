module
public import Theory.SpecificGroups.SymplecticFour.LargeSylowGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSelectedGeneration

/-!
# Large critical generators using the full original edge Sylow

Quadraticity of the critical endpoint gives its inner natural image.
A conjugate of the prescribed Sylow generates Sp₄ with that image. Lift
its conjugator inside the original residual, retaining the whole kernel
contained in the edge Sylow. This supplies actual full-residual generation
without a comparison between the two canonical movers.

Source: MS93 (3.3), (5.5)--(5.11), pp.867,915--924; Aschbacher--Smith
9.3.10, printed pp.734--735. The consumer is GenerationTwoSymplecticDistanceBound.
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

/-- The full prescribed edge Sylow supplies a residual generator for every large critical image. -/
theorem original_large_critical_sylow_generator
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
    (E : Subgroup (FreeAmalgam R)) (hES : E ≤ stabilizer R a)
    (hQE : Q R a ≤ E)
    (hSylow : ∃ P : Sylow 2 (stabilizer R a),
      (P : Subgroup _) = E.subgroupOf (stabilizer R a)) :
    ∃ g ∈ Ltilde R a,
      Ltilde R a ≤ E.map (MulAut.conj g).toMonoidHom ⊔ Z R z := by

  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,hψ,hconj,_hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq path.start_color
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top
        (by omega : 2 < Nat.card F.Carrier))).trans Subgroup.topEquiv
  let := finite_stabilizer R a
  let S := stabilizer R a
  have hκker : κ.ker = (Q R a).subgroupOf S := by
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1)]
  let B := (pResidual 2 H).map q
  let eB : B ≃* Sp F.Carrier := e.groupEquiv.trans d
  let E₀ := E.subgroupOf S
  let A₀ := (Z R z).subgroupOf S
  let E₁ := E₀.map κ
  have hzS : Z R z ≤ S := path.endpoint_Z_le_start_stabilizer hb
  let δ := κ.comp (inclusion hzS)
  have hδrange : δ.range = A₀.map κ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact x.property
    · intro hy
      exact ⟨⟨y.val,hy⟩,rfl⟩
  have hAc : 4 < Nat.card (A₀.map κ) := by
    rw [←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) A₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hzS] at hh
    exact hza.trans_eq hh
  let rev : DistanceEight.PathCentrality.CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry (MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith)
        a path.start_color (by rwa [geometry.distance_constant a path.start_color])
        z path.end_color path.critical }
  have hqA : IsQuadratic (MovedSection.ambientAction s e) (A₀.map κ) := by
    rw [←hδrange]
    exact critical_ambient_quadratic rev hb s e he j hj hjr δ
      (fun x v => hconj (inclusion hzS x) v)
  have hBact (b : B) (v : Vector F.Carrier) :
      MovedSection.ambientAction s e b.val v = symplecticNatural 2 (eB b) v := by
    rw [MovedSection.ambientAction_component]
    rfl
  have hAB : A₀.map κ ≤ B :=
    SymplecticNaturalNormalizer.le_component_of_quadratic_two_lt_card hFc B
      (hC ▸ bot_le) eB (MovedSection.ambientAction s e) hψ hBact
      (A₀.map κ) hqA (by omega)
  let A₂ := ((A₀.map κ).subgroupOf B).map eB.toMonoidHom
  have hA₂q : ∀ x ∈ A₂, ∀ y ∈ A₂, ∀ v : Vector F.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    have h := hqA x.val hx y.val hy v
    simpa only [hBact,Representation.symplecticNatural_apply,smul_eq_mulVec,
      MulEquiv.coe_toMonoidHom] using h
  have hA₂c : Nat.card F.Carrier < Nat.card A₂ := by
    rw [hFc,card_map_of_injective eB.injective,
      ←card_map_of_injective B.subtype_injective,map_subgroupOf_eq_of_le hAB]
    exact hAc
  obtain ⟨P,hP⟩ := hSylow
  let P₁ := P.mapSurjective (f := κ) _hκ
  obtain ⟨P₂,hP₂⟩ := P₁.exists_subgroupOf_eq_of_normal B
  let P₃ := P₂.mapSurjective (f := eB.toMonoidHom) eB.surjective
  obtain ⟨g₀,hmodel⟩ := LargePlaneGeneration.exists_sylow_large_quadratic_generator
    hFc P₃ A₂ hA₂q hA₂c
  obtain ⟨g,hg,hgq⟩ := (show (eB.symm g₀).val ∈ ((Ltilde R a).subgroupOf S).map κ from
    _hκL.symm ▸ (eB.symm g₀).property)
  let f := B.subtype.comp eB.symm.toMonoidHom
  have hf : f.comp eB.toMonoidHom = B.subtype := by ext b; simp [f]
  have hP₃image : (P₃ : Subgroup (Sp F.Carrier)).map f = E₁ ⊓ B := by
    change ((P₂ : Subgroup B).map eB.toMonoidHom).map f = _
    rw [map_map,hf,hP₂,subgroupOf_map_subtype]
    change ((P : Subgroup S).map κ) ⊓ B = _
    rw [hP]
  have hArmap : A₂.map f = A₀.map κ := by
    rw [map_map,hf,map_subgroupOf_eq_of_le hAB]
  have hfr : f.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr eB.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hgen := congrArg (Subgroup.map f) hmodel
  rw [Subgroup.map_sup,image_conjugate,hP₃image,hArmap,
    ←MonoidHom.range_eq_map,hfr] at hgen
  have hmap : ((Ltilde R a).subgroupOf S).map κ ≤
      (E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀).map κ := by
    rw [Subgroup.map_sup,image_conjugate,hgq,_hκL]
    exact hgen.ge.trans (sup_le_sup_right (map_mono inf_le_left) _)
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
