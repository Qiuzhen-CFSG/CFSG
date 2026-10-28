module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.EdgeGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Model.Construction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# The finite core of the terminal binary pairing

This file supplies the finite source data for the canonical dual seed used
at the terminal edge.  The construction keeps the quotient denominator
intrinsic: irreducibility and [Vcirc_a,Q_a] = U_a identify the centralizer
of Q_a inside Vcirc_a with U_a. Graph-twisting the supplied dual coordinates
then gives its natural quotient. The literal fixed preimage is also U_a,
and the opposite-parabolic closure is transported to the natural two-space
using a nonzero lift of the canonical binary line. The order-four bound is
retained from the geometric edge seed.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), pp.847--848,
and its terminal application in (4.3.2), pp.885--886.
-/

@[expose] public section
set_option linter.style.haveILetI false

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Matrix commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
open RankOnePairing
open Incidence
open Incidence.DualGeometry
open FirstPairing.Orientation.QuotientApplication.NaturalGeneration

universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}

private noncomputable def restricted_natural
    {e : Extension (M := M)} {J : Subgroup M}
    (n : NaturalFactor e.projection ⊤ J ⊥) :
    NaturalFactor e.projection (component e.projection e.flag) J ⊥ := by
  refine {
    marking := n.marking
    coordinates := n.coordinates
    surjective := n.surjective
    kernel := n.kernel
    normalized := ?_
    action := ?_ }
  · intro l hl
    exact n.normalized (mem_top l)
  · intro l hl x y hy
    exact n.action l (by trivial) x y hy

private noncomputable def restricted_dual
    {e : Extension (M := M)} {J Z : Subgroup M} [Z.Normal]
    {z : NaturalFactor e.projection ⊤ Z ⊥}
    (n : DualFactor e.projection ⊤ J Z Z z) :
    DualFactor e.projection (component e.projection e.flag) J Z Z
      (restricted_natural (e := e) z) := by
  refine {
    coordinates := n.coordinates
    surjective := n.surjective
    kernel := n.kernel
    normalized := ?_
    action := ?_ }
  · intro l hl
    exact n.normalized (mem_top l)
  · intro l hl x y hy
    exact n.action l (by trivial) x y hy

private theorem component_image (e : Extension (M := M)) :
    (component e.projection e.flag).map e.projection = ⊤ :=
  RankOnePairing.component_map _ e.base.surjective _

private def singer : SL := ⟨!![0,0,1;1,0,1;0,1,0], by decide⟩

private theorem dual_vector_transitive (v w : Fin 3 → ZMod 2)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL, g.val.mulVec v = w := by
  have ht : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
      ∃ k : Fin 7, (singer ^ k.val).val.mulVec v = w := by decide
  obtain ⟨k, hk⟩ := ht v w hv hw
  exact ⟨singer ^ k.val, hk⟩

private theorem space_irreducible :
    ∀ D : Subgroup (Multiplicative (Fin 3 → ZMod 2)),
      (∀ g : SL, D.map (Incidence.FixedGeometry.ValueConstruction.vectorAction g).toMonoidHom = D) →
      D = ⊥ ∨ D = ⊤ := by
  intro D hD
  by_cases hbot : D = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm le_top
  obtain ⟨u, hu, hu1⟩ := D.bot_or_exists_ne_one.resolve_left hbot
  intro v hv
  by_cases hv1 : v = 1
  · simp [hv1]
  obtain ⟨g, hg⟩ := dual_vector_transitive u.toAdd v.toAdd
    (by intro h; apply hu1; exact Multiplicative.toAdd.injective (by simpa using h))
    (by intro h; apply hv1; exact Multiplicative.toAdd.injective (by simpa using h))
  have hu' : u ∈ D := hu
  have hmem : Incidence.FixedGeometry.ValueConstruction.vectorAction g u ∈ D := by
    rw [← hD g]
    exact mem_map_of_mem _ hu'
  have hev : Incidence.FixedGeometry.ValueConstruction.vectorAction g u = v := by
    apply Multiplicative.toAdd.injective
    change g.val.mulVec u.toAdd = v.toAdd
    exact hg
  exact hev ▸ hmem

private theorem full_fixed_zero (v : Multiplicative (Fin 3 → ZMod 2))
    (h : ∀ g : SL, g.val.mulVec v.toAdd = v.toAdd) : v = 1 := by
  have hf : ∀ v : Fin 3 → ZMod 2, singer.val.mulVec v = v → v = 0 := by decide
  exact Multiplicative.toAdd.injective (hf v.toAdd (h singer))

private theorem h_eq_u_subgroup
    (_source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R)
    (facts : PairingControl.ContraryLocalFacts geometry)
    (a : Vertex R) (ha : color R a = false) :
    ⁅(Vcirc R a).subgroupOf (stabilizer R a), (Q R a).subgroupOf (stabilizer R a)⁆ =
      (U R a).subgroupOf (stabilizer R a) := by
  let S := stabilizer R a
  have hVS : V R a ≤ S :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hLS : Ltilde R a ≤ S := Ltilde_le_stabilizer a
  have hVcS : Vcirc R a ≤ S := by
    rw [Vcirc]
    apply commutator_le.mpr
    intro v hv l hl
    simpa only [commutatorElement_def, mul_assoc] using S.mul_mem
      (S.mul_mem (hVS hv) (hLS hl)) (S.mul_mem (S.inv_mem (hVS hv)) (S.inv_mem (hLS hl)))
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  have hUS : U R a ≤ S := by
    rw [U]
    apply commutator_le.mpr
    intro z hz l hl
    simpa only [commutatorElement_def, mul_assoc] using S.mul_mem
      (S.mul_mem (show z ∈ S from (Z_le_stabilizer R a) hz) (hLS hl))
      (S.mul_mem (S.inv_mem (show z ∈ S from (Z_le_stabilizer R a) hz)) (S.inv_mem (hLS hl)))
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  rw [map_commutator,
    map_subgroupOf_eq_of_le hVcS,
    map_subgroupOf_eq_of_le hQS,
    map_subgroupOf_eq_of_le hUS]
  simpa [H] using facts.H_eq_U a ha

namespace EdgeSeedAt

local instance vertex_finite (a : Vertex R) : Finite (stabilizer R a) :=
  finite_stabilizer R a

variable {source : LocalSource L R} {geometry : Geometry R}
  {a t : Vertex R} {ha : color R a = false}

/-- A nonzero fixed line generates the entire irreducible dual quotient;
its full inverse image already contains the coordinate kernel. -/
private theorem seed_generates
    (edge : EdgeSeedAt source a t ha)
    (hU : (U R a).subgroupOf (stabilizer R a) ≤
      (Vcirc R a).subgroupOf (stabilizer R a)) :
    generated (canonicalSeed edge.extension edge.opposite.dual edge.side) =
      (Vcirc R a).subgroupOf (stabilizer R a) := by
  let S := stabilizer R a
  let e := edge.extension
  let J := (Vcirc R a).subgroupOf S
  let Z := (U R a).subgroupOf S
  let X := canonicalSeed e edge.opposite.dual edge.side
  have hZX : Z ≤ X := le_canonicalSeed e edge.opposite.dual edge.side hU
  have hfixed := EdgeGeometry.model_fixed_eq_bot source a ha edge.opposite
    edge.flag edge.weakBN edge.side edge.fixed_bot
  have hJN : J.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  apply le_antisymm
  · exact RankOnePairing.generated_le X J
      (canonicalSeed_le e edge.opposite.dual edge.side)
  intro y hy
  let yy : J := ⟨y, hy⟩
  let q := edge.opposite.dual.coordinates
  by_cases hy0 : q yy = 1
  · have hk : yy ∈ q.ker := hy0
    have hzJ : yy ∈ Z.subgroupOf J := by
      change yy ∈ ((U R a).subgroupOf S).subgroupOf J
      rw [← edge.opposite.dual.kernel]
      exact hk
    exact le_normalClosure (hZX hzJ)
  · let seed := Incidence.DualGeometry.seedLine
      edge.opposite.naturalU.marking e.flag edge.side
    have hseed_ne : seed ≠ ⊥ := by
      have hm := Incidence.DualGeometry.matrixGeometry_of_no_fixed
        edge.opposite.naturalU.marking e.flag edge.side hfixed
      intro hs
      have hc : Nat.card seed = 2 := by simpa [seed] using hm.seed_card
      rw [hs, card_bot] at hc
      omega
    obtain ⟨s, hs, hs1⟩ := seed.bot_or_exists_ne_one.resolve_left hseed_ne
    obtain ⟨x, hx⟩ := edge.opposite.dual.surjective s
    have hxs : q x ∈ seed := by rw [hx]; exact hs
    have hxX : (x : S) ∈ X := ⟨x, hxs, rfl⟩
    obtain ⟨g, hg⟩ := dual_vector_transitive s.toAdd (q yy).toAdd
      (by intro h; apply hs1; exact Multiplicative.toAdd.injective h) hy0
    let p : SL := edge.opposite.naturalU.marking.symm
      (BinaryLinearThree.AutomorphismAction.graph.symm g)
    have hp : p ∈ (component e.projection e.flag).map e.projection := by
      rw [component_image e]
      trivial
    obtain ⟨l, hl, he⟩ := hp
    let y' : J := ⟨(l : S) * (x : S) * (l : S)⁻¹,
      (mem_normalizer_iff.mp (edge.opposite.dual.normalized (mem_top l)) x).mp x.property⟩
    have hact := edge.opposite.dual.action l (mem_top l) x y' (by rfl)
    have hmatrix :
        ((edge.opposite.naturalU.marking (edge.opposite.projection l))⁻¹.val).transpose = g.val := by
      have he' : edge.opposite.projection l = p := by
        simpa [e, EdgeSeedAt.extension] using he
      rw [he']
      change ((edge.opposite.naturalU.marking p)⁻¹.val).transpose = g.val
      rw [show edge.opposite.naturalU.marking p =
        BinaryLinearThree.AutomorphismAction.graph.symm g by
          simp [p]]
      change ((BinaryLinearThree.AutomorphismAction.graph.symm g).val.adjugate).transpose = g.val
      have hg' := BinaryLinearThree.AutomorphismAction.graph_apply
        (BinaryLinearThree.AutomorphismAction.graph.symm g)
      have hga := BinaryLinearThree.AutomorphismAction.graph.apply_symm_apply g
      have hh := hg'.symm.trans hga
      have hh' := congrArg Subtype.val hh
      change ((BinaryLinearThree.AutomorphismAction.graph.symm g)⁻¹.val).transpose = g.val at hh'
      rw [Matrix.SpecialLinearGroup.coe_inv] at hh'
      exact hh'
    have hq' : q y' = q yy := by
      apply Multiplicative.toAdd.injective
      calc
        Multiplicative.toAdd (q y') =
            ((edge.opposite.naturalU.marking (edge.opposite.projection l))⁻¹.val).transpose.mulVec
              (Multiplicative.toAdd (q x)) := hact
        _ = g.val.mulVec (Multiplicative.toAdd (q x)) := by rw [hmatrix]
        _ = g.val.mulVec s.toAdd := by rw [hx]
        _ = Multiplicative.toAdd (q yy) := hg
    have hk : y' * yy⁻¹ ∈ q.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, hq', map_inv, mul_inv_cancel]
    have hzJ : y' * yy⁻¹ ∈ Z.subgroupOf J := by
      change y' * yy⁻¹ ∈ ((U R a).subgroupOf S).subgroupOf J
      rw [← edge.opposite.dual.kernel]
      exact hk
    have hy' : (y' : S) ∈ generated X := by
      have hlN : l ∈ normalizer (generated X : Set S) := by
        rw [normalizer_eq_top]
        exact mem_top l
      exact (mem_normalizer_iff.mp hlN (x : S)).mp (le_normalClosure hxX)
    have hzgen : ((y' : S) * (yy : S)⁻¹) ∈ generated X :=
      le_normalClosure (hZX hzJ)
    exact by
      have hm := (generated X).mul_mem ((generated X).inv_mem hzgen) hy'
      simpa [y', mul_assoc] using hm

/-- The centralizer has invariant image in the dual quotient. A full image
would force the nontrivial commutator U_a to vanish. -/
private theorem intrinsic_centralizer
    (edge : EdgeSeedAt source a t ha)
    (hU : (U R a).subgroupOf (stabilizer R a) ≤
      (Vcirc R a).subgroupOf (stabilizer R a))
    (hcomm : ⁅(Vcirc R a).subgroupOf (stabilizer R a),
      (Q R a).subgroupOf (stabilizer R a)⁆ = (U R a).subgroupOf (stabilizer R a))
    (hZne : (U R a).subgroupOf (stabilizer R a) ≠ ⊥)
    (hZcentral : (U R a).subgroupOf (stabilizer R a) ≤
      centralizer ((Q R a).subgroupOf (stabilizer R a) : Set (stabilizer R a))) :
    (Vcirc R a).subgroupOf (stabilizer R a) ⊓
      centralizer ((Q R a).subgroupOf (stabilizer R a) : Set (stabilizer R a)) =
      (U R a).subgroupOf (stabilizer R a) := by
  let S := stabilizer R a
  let e := edge.extension
  let J := (Vcirc R a).subgroupOf S
  let Z := (U R a).subgroupOf S
  let W := (Q R a).subgroupOf S
  letI : J.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  letI : W.Normal := normal_subgroupOf_of_le_normalizer (Q_normalized R a)
  have hCnorm : component e.projection e.flag ≤
      normalizer ((J ⊓ centralizer (W : Set S) : Subgroup S) : Set S) := by
    exact (le_inf le_normalizer_of_normal
      (normalizes_centralizer _ W le_normalizer_of_normal)).trans
      inf_normalizer_le_normalizer_inf
  change J ⊓ centralizer (W : Set S) = Z
  apply le_antisymm
  · intro c hc
    let cc : J := ⟨c, hc.1⟩
    let hdual : DualFactor e.projection ⊤ J Z Z edge.opposite.naturalU := by
      simpa [e, EdgeSeedAt.extension, vertexExtension_projection] using edge.opposite.dual
    let nd := restricted_dual (e := e) hdual
    let ng := nd.graphNatural
    let D : Subgroup (Multiplicative (Fin 3 → ZMod 2)) :=
      (J ⊓ centralizer (W : Set S)).subgroupOf J |>.map edge.opposite.dual.coordinates
    have hDinv : ∀ g : SL,
      D.map (Incidence.FixedGeometry.ValueConstruction.vectorAction g).toMonoidHom = D := by
      intro g
      let p := ng.marking.symm g
      have hi : p ∈ (component e.projection e.flag).map e.projection := by
        rw [component_image e]
        trivial
      obtain ⟨l, hl, he⟩ := hi
      have hle : D.map (Incidence.FixedGeometry.ValueConstruction.vectorAction g).toMonoidHom ≤ D := by
        rintro v ⟨u, hu, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hu
        let y : J := ⟨(l : S) * (x : S) * (l : S)⁻¹,
          (mem_normalizer_iff.mp (edge.opposite.dual.normalized (mem_top l)) x).mp x.property⟩
        have hyC : (y : S) ∈ J ⊓ centralizer (W : Set S) :=
          (mem_normalizer_iff.mp (hCnorm hl)) (x : S) |>.mp hx
        have hact' : edge.opposite.dual.coordinates y =
            Incidence.FixedGeometry.ValueConstruction.vectorAction g
              (edge.opposite.dual.coordinates x) := by
          apply Multiplicative.toAdd.injective
          change _ = g.val.mulVec _
          have hg : ng.marking (e.projection l) = g := by
            rw [he]
            exact ng.marking.apply_symm_apply g
          have hact := ng.action l hl x y (by rfl)
          change Multiplicative.toAdd (edge.opposite.dual.coordinates y) =
            (ng.marking (e.projection l)).val.mulVec
              (Multiplicative.toAdd (edge.opposite.dual.coordinates x)) at hact
          rw [hg] at hact
          exact hact
        have hyC' : y ∈ (J ⊓ centralizer (W : Set S)).subgroupOf J :=
          ⟨y.property, hyC.2⟩
        refine ⟨y, hyC', ?_⟩
        change edge.opposite.dual.coordinates y =
          (Incidence.FixedGeometry.ValueConstruction.vectorAction g)
            (edge.opposite.dual.coordinates x)
        simpa [Incidence.FixedGeometry.ValueConstruction.vectorAction] using hact'
      exact Subgroup.eq_of_le_of_card_ge hle
        (by
          have hcard : Nat.card
              (D.map (Incidence.FixedGeometry.ValueConstruction.vectorAction g).toMonoidHom) =
              Nat.card D :=
            Subgroup.card_map_of_injective
              (Incidence.FixedGeometry.ValueConstruction.vectorAction g).injective
          exact hcard.symm.le)
    rcases space_irreducible D hDinv with hDbot | hDtop
    · have hccC : cc ∈ (J ⊓ centralizer (W : Set S)).subgroupOf J := by
        exact ⟨hc.1, hc.2⟩
      have hcoord : edge.opposite.dual.coordinates cc ∈ D :=
        mem_map_of_mem _ hccC
      rw [hDbot] at hcoord
      have hqker : cc ∈ edge.opposite.dual.coordinates.ker :=
        MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hcoord)
      rw [edge.opposite.dual.kernel] at hqker
      change (cc : S) ∈ Z at hqker
      exact hqker
    · have hJcentral : J ≤ centralizer (W : Set S) := by
        intro x hx
        let xx : J := ⟨x, hx⟩
        have hqx : edge.opposite.dual.coordinates xx ∈ D := by
          rw [hDtop]
          trivial
        obtain ⟨c, hc, heq⟩ := hqx
        have hk : c * xx⁻¹ ∈ edge.opposite.dual.coordinates.ker := by
          apply MonoidHom.mem_ker.mpr
          rw [map_mul, heq, map_inv, mul_inv_cancel]
        have hk' : c * xx⁻¹ ∈ Z.subgroupOf J := by
          rw [← edge.opposite.dual.kernel]
          exact hk
        have hkZ : ((c * xx⁻¹ : J) : S) ∈ Z := by
          exact hk'
        have hz' : ((c * xx⁻¹ : J) : S) ∈ J ⊓ centralizer (W : Set S) := by
          exact ⟨hU hkZ, hZcentral hkZ⟩
        have hc' : (c : S) ∈ J ⊓ centralizer (W : Set S) := by
          exact Subgroup.mem_subgroupOf.mp hc
        have hx' := (J ⊓ centralizer (W : Set S)).mul_mem
          ((J ⊓ centralizer (W : Set S)).inv_mem hz') hc'
        have hxC : (xx : S) ∈ J ⊓ centralizer (W : Set S) := by
          simpa [mul_assoc] using hx'
        exact hxC.2
      have hbot : ⁅J, W⁆ = (⊥ : Subgroup S) :=
        commutator_eq_bot_iff_le_centralizer.mpr hJcentral
      have hzbot : Z = (⊥ : Subgroup S) := hcomm.symm.trans hbot
      exact (hZne hzbot).elim
  · simpa [Z] using (le_inf hU hZcentral)

private theorem rank_one_of_seed_data {A : Type*} [Group A]
    {π : A →* SL} {flag : SL} {i : Bool} {H N Z : Subgroup A} {x : A}
    (d : NaturalSeedData π flag i H N Z x) :
    Nonempty (RankOneFactor (localResidual (parabolic π flag (!i)))
      (localGenerated (parabolic π flag (!i)) d.seed) N) := by
  obtain ⟨c⟩ := planeCoordinates_nonempty d.natural.marking flag i
    d.vector d.nonzero d.fixed
  exact d.rankOneFactor_nonempty c

/-- Identify the full line preimage with the seed of the checked natural-plane
transport, retaining the untilded residual as its actor. -/
private theorem rank_one_factor {A : Type*} [Group A] [Finite A]
    (e : Extension (M := A)) {J Z : Subgroup A}
    {z : NaturalFactor e.projection ⊤ Z ⊥}
    (o : DualFactor e.projection ⊤ J Z Z z) (i : Bool)
    (hU : Z ≤ J) (hJ : J ≤ extensionCore e.projection)
    (hseed_normal : localParabolic e i ≤ normalizer (canonicalSeed e o i : Set A))
    (hfixed : Incidence.FixedGeometry.ValueConstruction.fixedSpace
      (Incidence.FixedGeometry.ValueConstruction.markedParabolic z.marking e.flag i) = ⊥)
    (hpar : ∀ j, localParabolic e j = parabolic e.projection e.flag j) :
    Nonempty (RankOneFactor (localResidual (localParabolic e (!i)))
      (localGenerated (localParabolic e (!i)) (canonicalSeed e o i)) Z) := by
  let X := canonicalSeed e o i
  let ng : NaturalFactor e.projection ⊤ J Z := o.graphNatural
  have hZX : Z ≤ X := le_canonicalSeed e o i hU
  let line := Incidence.DualGeometry.seedLine z.marking e.flag i
  have hcard : Nat.card line = 2 :=
    (matrixGeometry_of_no_fixed z.marking e.flag i hfixed).seed_card
  have hne : line ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    omega
  obtain ⟨v, hv, hvne⟩ := line.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨x, hx⟩ := ng.surjective v
  have hxline : ng.coordinates x ∈ line := hx ▸ hv
  have hxne : ng.coordinates x ≠ 1 := hx ▸ hvne
  have hJker : J ≤ e.projection.ker := hJ.trans (extensionCore_le_kernel _)
  have hxfix : ∀ g ∈ modelParabolic e.flag i,
      (ng.marking g).val.mulVec (ng.coordinates x).toAdd = (ng.coordinates x).toAdd := by
    intro g hg
    have hm : ng.marking g ∈
        Incidence.FixedGeometry.ValueConstruction.markedParabolic ng.marking e.flag i :=
      mem_map_of_mem ng.marking.toMonoidHom hg
    have hf : Incidence.FixedGeometry.ValueConstruction.vectorAction (ng.marking g)
        (ng.coordinates x) = ng.coordinates x := hxline (ng.marking g) hm
    exact congrArg Multiplicative.toAdd hf
  have d : NaturalSeedData e.projection e.flag i J Z Z (x : A) := {
    natural := ng
    projection_surjective := e.base.surjective
    residual_image := by
      intro i
      rw [← hpar i]
      exact localResidual_map e i
    fixed_le_group := hU
    z_le_fixed := le_rfl
    z_le_kernel := hU.trans hJker
    element_mem := x.property
    element_kernel := hJker x.property
    nonzero := hxne
    fixed := hxfix }
  have hXeq : X = Z ⊔ zpowers (x : A) :=
    EdgeGeometry.canonicalSeed_eq_of_lift e o i hU hcard x hxline hxne
  have hdseed : d.seed = X := by
    apply le_antisymm
    · apply sup_le hZX
      apply Incidence.localGenerated_le_of_normalizes
      · rw [← hpar]
        exact hseed_normal
      · rw [hXeq]
        exact le_sup_right
    · rw [hXeq]
      apply sup_le le_sup_left
      exact le_trans (le_localGenerated _ _ (by
        intro y hy
        change e.projection y ∈ modelParabolic e.flag i
        have hyker := (zpowers_le.mpr (hJker x.property)) hy
        rw [MonoidHom.mem_ker.mp hyker]
        exact one_mem _)) le_sup_right
  have hn := rank_one_of_seed_data d
  simpa only [hdseed, hpar] using hn

/-- The canonical terminal seed satisfies the complete source interface. -/
theorem pairing_of_local_facts
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R)
    (facts : PairingControl.ContraryLocalFacts geometry)
    (edge : EdgeSeedAt source a t ha) : Nonempty edge.Pairing := by
  let S := stabilizer R a
  let _ := finite_stabilizer R a
  let e := edge.extension
  let J := (Vcirc R a).subgroupOf S
  let Z := (U R a).subgroupOf S
  let W := (Q R a).subgroupOf S
  haveI : W.Normal := normal_subgroupOf_of_le_normalizer (Q_normalized R a)
  let X := canonicalSeed e edge.opposite.dual edge.side
  let nz : NaturalFactor e.projection (component e.projection e.flag) Z ⊥ :=
    restricted_natural edge.opposite.naturalU
  have hU : (U R a).subgroupOf S ≤ J := by
    intro x hx
    exact commutator_mono
      (show CFSG.Quasithin.ChapterC.BinaryMS.MS93.Z R a ≤ V R a by
        simpa [V] using Z_le_VBall R a 2) le_rfl hx
  have hcore : extensionCore e.projection = W := by
    simpa [W, e, EdgeSeedAt.extension] using
      (vertexExtension_core source a ha edge.opposite edge.flag edge.weakBN)
  have hJ : J ≤ extensionCore e.projection := by
    rw [hcore]
    intro x hx
    exact geometry.V_le_Q hb a ha
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences.Vcirc_le_V a hx)
  have hZX : Z ≤ X := by
    exact le_canonicalSeed e edge.opposite.dual edge.side hU
  have hcomm : ⁅J, W⁆ = Z := by
    simpa [J, W, Z, e, EdgeSeedAt.extension, vertexExtension_projection] using
      h_eq_u_subgroup source geometry hb facts a ha
  have hcomm_le : ⁅X, W⁆ ≤ Z := by
    exact (commutator_mono (canonicalSeed_le e edge.opposite.dual edge.side) le_rfl).trans
      hcomm.le
  have hZne : Z ≠ ⊥ := by
    intro hz
    let v : Multiplicative (Fin 3 → ZMod 2) :=
      Multiplicative.ofAdd ![1, 0, 0]
    have hv : v ≠ 1 := by decide
    obtain ⟨u, hu⟩ := edge.opposite.naturalU.surjective v
    have hu1 : (u : S) = 1 := by
      have hu' : (u : S) ∈ Z := u.property
      rw [hz] at hu'
      exact Subgroup.mem_bot.mp hu'
    have huZ : u = (1 : Z) := Subtype.ext hu1
    apply hv
    calc
      v = edge.opposite.naturalU.coordinates u := hu.symm
      _ = edge.opposite.naturalU.coordinates (1 : Z) := by rw [huZ]
      _ = 1 := edge.opposite.naturalU.coordinates.map_one
  have hfixed := EdgeGeometry.model_fixed_eq_bot source a ha edge.opposite
    edge.flag edge.weakBN edge.side edge.fixed_bot
  have hgen : generated X = J := seed_generates edge hU
  have hcomm_ne : Nat.card (⁅X, W⁆ : Subgroup S) ≠ 1 := by
    intro hc
    have hbot : ⁅X, W⁆ = ⊥ := eq_bot_of_card_eq _ hc
    have hgenbot : ⁅generated X, W⁆ ≤ (⊥ : Subgroup S) :=
      RankOnePairing.generated_commutator_le X W ⊥ hbot.le
    apply hZne
    rw [← hcomm, ← hgen]
    exact le_antisymm hgenbot bot_le
  have hcomm_ext : ⁅X, extensionCore e.projection⁆ ≤ Z := by
    rw [hcore]
    exact hcomm_le
  have hcomm_ne_ext : Nat.card (⁅X, extensionCore e.projection⁆ : Subgroup S) ≠ 1 := by
    intro hc
    apply hcomm_ne
    simpa [hcore] using hc
  have hseed_normal :
      localParabolic e edge.side ≤ normalizer (X : Set S) := by
    apply le_normalizer_iff.mpr
    intro l hl y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxX : (x : S) ∈ X := ⟨x, hx, rfl⟩
    let y' : J := ⟨(l : S) * (x : S) * (l : S)⁻¹,
      (mem_normalizer_iff.mp (edge.opposite.dual.normalized (mem_top l)) x).mp x.property⟩
    have hp : (e.projection l : SL) ∈ modelParabolic e.flag edge.side := by
      exact hl.1
    have hactor :
        (Incidence.DualGeometry.dualMark edge.opposite.naturalU.marking
          (e.projection l)) ∈
          CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.markedParabolic
            (Incidence.DualGeometry.dualMark edge.opposite.naturalU.marking)
            e.flag edge.side :=
      ⟨e.projection l, hp, rfl⟩
    have hfixed := hx
    change edge.opposite.dual.coordinates x ∈
      Incidence.DualGeometry.seedLine edge.opposite.naturalU.marking
        e.flag edge.side at hfixed
    have hfix := hfixed _ hactor
    have hact := edge.opposite.dual.action l (mem_top l) x y' (by rfl)
    have hcoord : edge.opposite.dual.coordinates y' =
        edge.opposite.dual.coordinates x := by
      apply Multiplicative.toAdd.injective
      simpa only [Incidence.DualGeometry.dualMark,
        BinaryLinearThree.AutomorphismAction.graph_apply] using
        hact.trans (congrArg Multiplicative.toAdd hfix)
    have hk : y' * x⁻¹ ∈ edge.opposite.dual.coordinates.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, hcoord, map_inv, mul_inv_cancel]
    have hzJ : y' * x⁻¹ ∈ Z.subgroupOf J := by
      rw [← edge.opposite.dual.kernel]
      exact hk
    change ((y' * x⁻¹ : J) : S) ∈ Z at hzJ
    exact by simpa [y', mul_assoc] using X.mul_mem (hZX hzJ) hxX
  have hZcentral : Z ≤ centralizer (W : Set S) := by
    intro z hz
    apply mem_centralizer_iff.mpr
    intro w hw
    apply Subtype.ext
    change (z : FreeAmalgam R) ∈ U R a at hz
    have hzZ : (z : FreeAmalgam R) ∈ CFSG.Quasithin.ChapterC.BinaryMS.MS93.Z R a :=
      U_le_Z a hz
    have hzC := (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a ha)) hzZ
    change (w : FreeAmalgam R) ∈ Q R a at hw
    exact hzC (w : FreeAmalgam R) hw
  letI : J.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized a)
  have hcentral : J ⊓ centralizer (W : Set S) = Z :=
    intrinsic_centralizer edge hU hcomm hZne hZcentral
  let ng : NaturalFactor e.projection ⊤ J Z := edge.opposite.dual.graphNatural
  have hpar : ∀ i, localParabolic e i = parabolic e.projection e.flag i := by
    intro i
    exact vertexExtension_parabolic source a ha edge.opposite edge.flag edge.weakBN i
  have hC : fixedPreimage (component e.projection e.flag) X Z = Z := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hygen, hyfix⟩ := (mem_fixedPreimage _ _ _ y).mp hy
      have hyJ : y ∈ J := hgen ▸ hygen
      let yy : J := ⟨y, hyJ⟩
      have hzero : ng.coordinates yy = 1 := by
        apply full_fixed_zero
        intro g
        obtain ⟨l, hl, he⟩ := (show ng.marking.symm g ∈
            (component e.projection e.flag).map e.projection from
          (component_image e).symm ▸ mem_top _)
        let y' : J := ⟨l * y * l⁻¹,
          (mem_normalizer_iff.mp (ng.normalized (mem_top l)) y).mp hyJ⟩
        have hk : y' * yy⁻¹ ∈ ng.coordinates.ker := by
          rw [ng.kernel]
          exact hyfix l hl
        have heq : ng.coordinates y' = ng.coordinates yy := by
          have hh := MonoidHom.mem_ker.mp hk
          rw [map_mul, map_inv, mul_inv_eq_one] at hh
          exact hh
        have hact := ng.action l (mem_top l) yy y' rfl
        rw [he, ng.marking.apply_symm_apply, heq] at hact
        exact hact.symm
      have hk : yy ∈ Z.subgroupOf J := ng.kernel ▸ MonoidHom.mem_ker.mpr hzero
      exact hk
    · exact le_fixedPreimage _ _ _ hZX
  have hseedcomm : ⁅X, localParabolic e edge.side⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    obtain ⟨xx, hxx, rfl⟩ := hx
    let yy : J := ⟨l * (xx : S) * l⁻¹,
      (mem_normalizer_iff.mp (ng.normalized (mem_top l)) _).mp xx.property⟩
    have hf := hxx _ (mem_map_of_mem ng.marking.toMonoidHom (show
      e.projection l ∈ modelParabolic e.flag edge.side from hl.1))
    have heq : ng.coordinates yy = ng.coordinates xx :=
      (ng.action l (mem_top l) xx yy rfl).trans (congrArg Multiplicative.toAdd hf)
    have hk : yy * xx⁻¹ ∈ ng.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, heq, map_inv, mul_inv_cancel]
    rw [ng.kernel] at hk
    exact hk
  have hrank := rank_one_factor e edge.opposite.dual edge.side hU hJ hseed_normal hfixed hpar
  refine ⟨{
    data := {
      z_le := hZX
      x_le := (canonicalSeed_le e edge.opposite.dual edge.side).trans hJ
      w_le := le_rfl
      x_normal := normal_subgroupOf_of_le_normalizer hseed_normal
      natural := nz
      frattini_le := by
        rw [hgen]
        letI : IsMulCommutative (Multiplicative (Fin 3 → ZMod 2)) := ⟨⟨by
            intro x y
            ext j
            simp [mul_comm]⟩⟩
        letI : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) := {
          exponent_dvd_p := by
            rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
            intro x
            apply Multiplicative.toAdd.injective
            rw [pow_two]
            change x.toAdd + x.toAdd = 0
            ext j
            exact ZModModule.add_self _ }
        letI : Fact (IsPGroup 2 (Multiplicative (Fin 3 → ZMod 2))) :=
          ⟨IsElementaryAbelian.isPGroup 2 _⟩
        let hdual : DualFactor e.projection ⊤ J Z Z edge.opposite.naturalU := by
          simpa [e, EdgeSeedAt.extension, vertexExtension_projection] using edge.opposite.dual
        let ng := (restricted_dual (e := e) hdual).graphNatural
        have hphi : frattini J ≤ (frattini (Multiplicative (Fin 3 → ZMod 2))).comap
            ng.coordinates :=
          frattini_le_comap_frattini_of_surjective ng.surjective
        intro y hy
        obtain ⟨y, hy, rfl⟩ := hy
        have hy0 : ng.coordinates y ∈ (⊥ : Subgroup (Multiplicative (Fin 3 → ZMod 2))) := by
          have hh := hphi hy
          rw [frattini_eq_bot_of_isElementaryAbelian (p := 2)] at hh
          exact hh
        rw [Subgroup.mem_bot] at hy0
        have hyker : y ∈ ng.coordinates.ker := MonoidHom.mem_ker.mpr hy0
        rw [ng.kernel] at hyker
        change (J.subtype y) ∈ Z at hyker
        exact hyker
      commutator_le := by
        simpa only [e, EdgeSeedAt.extension] using hcomm_ext
      commutator_nontrivial := by
        simpa only [e, EdgeSeedAt.extension] using hcomm_ne_ext
      commutator_card_le := by
        rw [hcore]
        simpa only [e, EdgeSeedAt.extension] using edge.small_commutator
      seed_fixed := by
        rw [hC]
        exact (commutator_mono le_rfl (map_subtype_le _)).trans hseedcomm
      rank_one_natural := by
        rw [hC]
        exact Classical.choice hrank }
    generated_eq := hgen
    natural_quotient := by
      rw [hgen, hcore]
      let n := (restricted_dual (e := e) edge.opposite.dual).graphNatural
      refine { n with kernel := ?_ }
      rw [n.kernel]
      ext y
      change (y : S) ∈ Z ↔ (y : S) ∈ centralizer (W : Set S)
      exact ⟨fun hy => hZcentral hy, fun hy => hcentral.le ⟨y.property, hy⟩⟩ }⟩

end EdgeSeedAt

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
