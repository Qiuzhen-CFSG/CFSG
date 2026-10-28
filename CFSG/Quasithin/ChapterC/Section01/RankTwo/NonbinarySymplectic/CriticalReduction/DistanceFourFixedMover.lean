module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusChief
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualMovers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.QuadraticIndex
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement

/-!
# The actual fixed-radius branch forces equal small movers

At the midpoint a of a large backward critical path u to e, the full
commutator [Z_u,Z_e] lies in X_a. Radius fixedness also puts it in D_a,
so Q_a and L_a together make the whole vertex stabilizer fix it. In
particular the literal edge kernel between a and e fixes this commutator.

Use the original natural cover at e. The large critical actor has a
self-orthogonal displacement plane. Every vector in that plane lifts to
the actual commutator, so the edge kernel fixes the plane pointwise and
acts quadratically on the natural quotient. Quadratic lifting retains the
full covering kernel. Its exact original U-index is therefore at most q².
Unequal individual mover indices force equality across this same edge;
actual edge conjugacy transfers the own-mover bound to a.

No orbit of the backward endpoint, naturality of the full span quotient,
or identification of its recognized marking with the original U is used.
Source: MS93 (5.12)(2), printed p.926, the unequal/point branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem full_displacement_fixer_quadratic
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (U A T : Subgroup G) (j : Multiplicative W →* G)
    (hj : Function.Injective j) (hjr : j.range=U)
    (α : A →* L (K := E)) (β : T →* L (K := E))
    (hA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (α a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hT : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (β t) w))=
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (hlarge : Nat.card E < Nat.card ((commutator (Sp E)).subtype.comp α).range)
    (hquad : let A₀ := ((commutator (Sp E)).subtype.comp α).range
      ∀ x ∈ A₀, ∀ y ∈ A₀, ∀ v : Vector E, x • (y • v-v)=y • v-v)
    (hfix : ⁅A,U⁆ ≤ centralizer (T : Set G)) : ⁅⁅U,T⁆,T⁆=⊥ := by
  let A₀ := ((commutator (Sp E)).subtype.comp α).range
  let D := displacementSpace A₀
  have hself : (form E).orthogonal D=D :=
    large_quadratic_displacement_self_orthogonal A₀ hquad hlarge
  have hfixed (t : T) (v : Vector E) (hv : v ∈ D) : binaryNatural (β t) v=v := by
    obtain ⟨w,hw,hwm⟩ := natural_displacement_lifts U A j hjr α σ hA p hp.1 v hv
    have hwfix : σ (β t) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hT,hfix hwm t.val t.property,mul_inv_cancel_right]
    have hh := congrArg p hwfix
    rw [p.isIntertwining,hw] at hh
    exact hh
  apply embedded_quadratic_of_natural_quadratic U T j hjr β σ hT p hp
  intro t s v
  apply hfixed
  exact displacement_mem_of_self_orthogonal D hself (β s).val
    (fun v hv => hfixed s v hv) v

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem critical_full_displacement_fixer_quadratic
    {geometry : Geometry d.radical} {u e : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F < (Q d.radical e).relIndex (Z d.radical u))
    (T : Subgroup (FreeAmalgam d.radical)) (hTS : T ≤ stabilizer d.radical e)
    (hfix : ⁅Z d.radical u,Z d.radical e⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical))) :
    ⁅⁅U d.radical e,T⁆,T⁆=⊥ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,η,hη,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d back.end_color
  have hCtop : C=⊤ := by
    have hp : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hp,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := η.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s η
  let p := MovedSection.coverProjection s η
  have hAS : Z d.radical u ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le u (geometry.exists_critical u back.start_color) back.critical.1.le
  let α := γ.comp (inclusion hAS)
  let β := γ.comp (inclusion hTS)
  have hact (x : stabilizer d.radical e) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (γ x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (η.groupEquiv.symm (η.groupEquiv (κC x))) w))=_
    rw [η.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγker : γ.ker=(Q d.radical e).subgroupOf (stabilizer d.radical e) := by
    ext x
    change η.groupEquiv (κC x)=1 ↔ x.val ∈ Q d.radical e
    rw [η.groupEquiv.map_eq_one_iff]
    rw [show κC x=1 ↔ κ x=1 from Subtype.ext_iff]
    constructor
    · intro hx
      exact hκQ ▸ mem_map_of_mem (stabilizer d.radical e).subtype hx
    · intro hx
      obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
      exact (show y=x from Subtype.ext hyx) ▸ hy
  have hαker : α.ker=(Q d.radical e).subgroupOf (Z d.radical u) := by
    ext x
    change inclusion hAS x ∈ γ.ker ↔ x.val ∈ Q d.radical e
    rw [hγker]
    rfl
  have hc : Nat.card ((commutator (Sp E.Carrier)).subtype.comp α).range =
      (Q d.radical e).relIndex (Z d.radical u) := by
    rw [MonoidHom.range_comp,card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective,
      ←index_ker,hαker]
    rfl
  have hq := critical_embedded_natural_actor_quadratic back (by omega) σ p hη j hj hjr α
    (fun x w => hact (inclusion hAS x) w)
  apply full_displacement_fixer_quadratic σ p hη (U d.radical e) (Z d.radical u) T
    j hj hjr α β (fun x w => hact (inclusion hAS x) w)
    (fun x w => hact (inclusion hTS x) w)
  · rw [hc,E.card_eq,hE,←h.field_card]
    exact hlarge
  · dsimp only
    rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v
    exact hq (α x) ⟨x,rfl⟩ (α y) ⟨y,rfl⟩ v
  · exact (commutator_mono le_rfl (U_le_Z e)).trans hfix

/-- A fixed radius and an actual large compatible backward critical image
force equality of the original and midpoint movers at the literal forward
edge, together with the small bound on the original whole U-layer. -/
theorem Input.replacement_distance_four_fixed_movers
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let e := path.walk.getVert 2
    let t := path.walk.getVert 1
    let Jₐ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let Jₑ := Subgroup.SmallMover.join (U d.radical e) (Q d.radical e)
      (Q d.radical t) (Nat.card F^2)
    Jₐ=Jₑ ∧ (centralizer (Jₐ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2 := by
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  let T := Q d.radical t
  let Jₐ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) T (Nat.card F^2)
  let Jₑ := Subgroup.SmallMover.join (U d.radical e) (Q d.radical e) T (Nat.card F^2)
  let D := ⁅Z d.radical u,Z d.radical e⁆
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have hbl := back.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have het : Adjacent d.radical e t := adjacent_symm _
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hTa : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hTe : T ≤ stabilizer d.radical e := fun _ hx => hx.2 e (adjacent_symm _ het)
  have hua : (cosetGraph d.radical).dist u a=2 := by
    rw [←hmid]
    exact back.dist_start (by omega)
  have hea : (cosetGraph d.radical).dist e a=2 := by
    rw [SimpleGraph.dist_comm]
    exact path.dist_start (by omega)
  have huV : Z d.radical u ≤ V d.radical a :=
    le_iSup_of_le u (le_iSup_of_le hua.le le_rfl)
  have heV : Z d.radical e ≤ V d.radical a :=
    le_iSup_of_le e (le_iSup_of_le hea.le le_rfl)
  have hDV : D ≤ ⁅V d.radical a,V d.radical a⁆ := commutator_mono huV heV
  have hDX : D ≤ X d.radical a := hDV.trans
    (h.replacement_radius_commutator_bounds d geometry hb4 path.start_color u e).1
  have hDD : D ≤ fixedCore d.radical a := hDV.trans
    ((commutator_mono le_rfl (geometry.V_le_Q (by omega) a path.start_color)).trans hfixed)
  have hDLa : Ltilde d.radical a ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hDD.trans inf_le_right)
  have hDQa : Q d.radical a ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    (Q_le_centralizer_X d.radical a).trans (centralizer_le hDX)
  have hlocal : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ :=
      CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
        (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb4,←MonoidHom.range_eq_map,hir]
  have hfix : D ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    exact hTa.trans (hlocal ▸ sup_le hDLa hDQa)
  have hquad := critical_full_displacement_fixer_quadratic h d back hb4 hlarge T hTe hfix
  have hiT := h.replacement_quadratic_moving_index_le_square d geometry hb4 he T hTe hquad
  let := finite_Z d.radical e
  let : Finite (U d.radical e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  have hiJ : (centralizer (Jₐ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical e) ≤ Nat.card F^2 :=
    (relIndex_le_of_le_left (centralizer_le (Subgroup.SmallMover.join_le _ _ _ _))
      index_ne_zero_of_finite).trans hiT
  have hequal : Jₐ=Jₑ := by
    by_contra hne
    exact (h.replacement_unequal_individual_indices d geometry hb4 he het hat hne).2.not_ge hiJ
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm _ het) (adjacent_symm _ hat)
  have hTg : T.map (MulAut.conj g⁻¹).toMonoidHom=T := by
    change (Q d.radical t).map (MulAut.conj g⁻¹).toMonoidHom=Q d.radical t
    rw [←Q_act,hg]
  have hiTa : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2 := by
    have hh := Subgroup.SmallMover.centralizer_index_map (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective (U d.radical e) T
    rw [hTg,←U_act,hga] at hh
    exact hh.trans_le hiT
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  exact ⟨hequal,(relIndex_le_of_le_left
    (centralizer_le (Subgroup.SmallMover.join_le _ _ _ _)) index_ne_zero_of_finite).trans hiTa⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
