module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneNonneighbors
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.SextetCore

/-!
# The original plane core in Todd coordinates

The original extraspecial core Q maps onto the two-core of the marked
sextet stabilizer: its kernel is E intersect Q of order 128, and its image
has order 64. The canonical Todd lifts of that native core also lie in Q.
Indeed their intersection with Q is invariant, and the irreducible hexacode
action makes it trivial or the whole core. The trivial alternative would
embed a group of order 64 in EQ/Q of order 16. All maps retain the original
Todd splitting and the same marked sextet. These give the pure involution
lifts required in AS91 (6.4), printed p.602.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open LocalGeometry LocalGeometry.LocalSubgroups SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

lemma planeCore_le_point (a : LocalData h) : ambientCore z ≤ a.P.M := by
  have hl : ambientCore z ≤ ambientTwoThreeCore z :=
    map_mono (core_le_twoThreeCore h)
  exact hl.trans ((cubicLift_le_triple a.L h).trans
    (inf_le_left.trans inf_le_left))

noncomputable def planeCoreProjection (a : LocalData h) : ambientCore z →* M24 :=
  a.P.projection.comp (inclusion (planeCore_le_point a))

lemma planeCoreProjection_ker (a : LocalData h) :
    (planeCoreProjection a).ker = a.P.E.subgroupOf (ambientCore z) := by
  ext q
  change a.P.projection ⟨q.val,planeCore_le_point a q.property⟩ = 1 ↔ _
  change (⟨q.val,planeCore_le_point a q.property⟩ : a.P.M) ∈ a.P.projection.ker ↔ _
  rw [a.P.projection_ker]
  rfl

lemma planeCoreProjection_ker_card (a : LocalData h) :
    Nat.card (planeCoreProjection a).ker = 128 := by
  rw [planeCoreProjection_ker,←card_map_of_injective (ambientCore z).subtype_injective,
    subgroupOf_map_subtype,a.radical_core_card]

lemma planeCoreProjection_card (a : LocalData h) :
    Nat.card (planeCoreProjection a).range = 64 := by
  have hc := (planeCoreProjection a).ker.card_mul_index
  have hq : Nat.card (ambientCore z) = 8192 :=
    (Nat.card_congr (coreEquivAmbient z).toEquiv).symm.trans h.core_card
  rw [index_ker,planeCoreProjection_ker_card,hq] at hc
  omega

lemma planeCoreProjection_range (a : LocalData h) :
    (planeCoreProjection a).range =
      ((ambientCore z).subgroupOf a.P.M).map a.P.projection := by
  ext s
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨⟨q,planeCore_le_point a q.property⟩,q.property,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨⟨q,hq⟩,rfl⟩

lemma planeCoreProjection_le (a : LocalData h) :
    (planeCoreProjection a).range ≤ (sextetStabilizer a.sextet).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
  · have hp : IsPGroup 2 (ambientCore z) :=
      (IsPGroup.of_card (p := 2) (n := 13) h.core_card).of_equiv (coreEquivAmbient z)
    exact hp.of_surjective (planeCoreProjection a).rangeRestrict
      (planeCoreProjection a).rangeRestrict_surjective
  · rw [planeCoreProjection_range,←a.plane_image]
    exact map_mono (fun q hq => ambientCore_le z hq)
  · intro g hg
    rw [←a.plane_image] at hg
    obtain ⟨m,hm,rfl⟩ := hg
    rw [planeCoreProjection_range]
    apply le_normalizer_map
    refine ⟨m,?_,rfl⟩
    apply mem_normalizer_iff.mpr
    intro q
    exact mem_normalizer_iff.mp ((normalizer_ambientCore h).symm ▸ hm) q.val

lemma planeCoreProjection_eq (a : LocalData h) :
    (planeCoreProjection a).range = (sextetStabilizer a.sextet).pCoreIn 2 := by
  apply eq_of_le_of_card_ge (planeCoreProjection_le a)
  rw [planeCoreProjection_card,pCoreIn,
    card_map_of_injective (sextetStabilizer a.sextet).subtype_injective,
    MathieuCode.J4Fusion.sextet_core_card]

/-- The canonical Todd complement at the same marked sextet, inside H. -/
noncomputable def planeComplement (a : LocalData h) :
    sextetStabilizer a.sextet →* centralizer z where
  toFun g := ⟨a.P.toddEquiv (SemidirectProduct.inr g.val), by
    apply (a.point_plane_todd_overlap (a.P.toddEquiv (SemidirectProduct.inr g.val))).mpr
    change a.P.projection (a.P.toddEquiv (SemidirectProduct.inr g.val)) ∈
      sextetStabilizer a.sextet
    simpa only [PointData.projection,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply,SemidirectProduct.rightHom_inr] using g.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g k := by apply Subtype.ext; simp

lemma planeComplement_projection (a : LocalData h) (g : sextetStabilizer a.sextet) :
    a.P.projection (a.P.toddEquiv (SemidirectProduct.inr g.val)) = g.val := by
  change (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inr g.val))).right = g.val
  rw [MulEquiv.symm_apply_apply]
  rfl

lemma planeComplement_core_le_sup (a : LocalData h) :
    (pCore 2 (sextetStabilizer a.sextet)).map (planeComplement a) ≤
      core z ⊔ a.P.E.subgroupOf (centralizer z) := by
  rintro _ ⟨s,hs,rfl⟩
  have hr : s.val ∈ (planeCoreProjection a).range := by
    rw [planeCoreProjection_eq]
    exact ⟨s,hs,rfl⟩
  obtain ⟨q,hq⟩ := hr
  let qH : centralizer z := ⟨q.val,ambientCore_le z q.property⟩
  have hqQ : qH ∈ core z := by rw [←ambientCore_subgroupOf]; exact q.property
  let m : a.P.M := a.P.toddEquiv (SemidirectProduct.inr s.val)
  have he : (planeComplement a s)*qH⁻¹ ∈ a.P.E.subgroupOf (centralizer z) := by
    change (m : G)*q.val⁻¹ ∈ a.P.E
    have hk : m * (⟨q.val,planeCore_le_point a q.property⟩ : a.P.M)⁻¹ ∈ a.P.projection.ker := by
      change a.P.projection (_ * _⁻¹) = 1
      rw [map_mul,map_inv,planeComplement_projection]
      change s.val * (planeCoreProjection a q)⁻¹ = 1
      rw [hq,mul_inv_cancel]
    rwa [a.P.projection_ker] at hk
  have hh := (core z ⊔ a.P.E.subgroupOf (centralizer z)).mul_mem
    (mem_sup_right he) (mem_sup_left hqQ)
  simpa only [inv_mul_cancel_right] using hh

lemma planeCore_radical_index (a : LocalData h) :
    (core z).relIndex (a.P.E.subgroupOf (centralizer z)) = 16 := by
  have hc := ((core z).subgroupOf (a.P.E.subgroupOf (centralizer z))).card_mul_index
  have hE : Nat.card (a.P.E.subgroupOf (centralizer z)) = 2048 :=
    (Nat.card_congr (subgroupOfEquivOfLe a.radical_le_plane).toEquiv).trans a.P.E_card
  have hker : Nat.card ((core z).subgroupOf (a.P.E.subgroupOf (centralizer z))) = 128 := by
    let f : (a.P.E.subgroupOf (centralizer z)) ≃* a.P.E :=
      subgroupOfEquivOfLe a.radical_le_plane
    have hm : ((core z).subgroupOf (a.P.E.subgroupOf (centralizer z))).map f.toMonoidHom =
        (ambientCore z).subgroupOf a.P.E := by
      ext v
      constructor
      · rintro ⟨q,hq,rfl⟩
        exact ⟨q.val,hq,rfl⟩
      · intro hv
        refine ⟨f.symm v,?_,f.apply_symm_apply v⟩
        rw [←ambientCore_subgroupOf]
        exact hv
    rw [←card_map_of_injective (f := f.toMonoidHom) f.injective,hm,←a.radicalDesign_ker]
    exact a.radicalDesign_ker_card
  change Nat.card _ * (core z).relIndex (a.P.E.subgroupOf (centralizer z)) = _ at hc
  rw [hker,hE] at hc
  omega

/-- The pure Todd lifts of the sextet two-core already lie in Q. The
index-sixteen quotient excludes a faithful image of its minimal normal E64. -/
lemma planeComplement_core_le (a : LocalData h) :
    (pCore 2 (sextetStabilizer a.sextet)).map (planeComplement a) ≤ core z := by
  let N := (core z).comap (planeComplement a)
  let R := pCore 2 (sextetStabilizer a.sextet)
  rcases MathieuCode.J4Fusion.sextet_core_minimal a.sextet (N ⊓ R) inf_le_right with hb | he
  · have hi : N.relIndex R = 64 := by
      rw [←inf_relIndex_right N R,hb,relIndex_bot_left]
      exact MathieuCode.J4Fusion.sextet_core_card _
    have hupper : N.relIndex R ≤ 16 := by
      rw [show N = (core z).comap (planeComplement a) from rfl,relIndex_comap]
      calc
        (core z).relIndex (R.map (planeComplement a)) ≤
            (core z).relIndex (core z ⊔ a.P.E.subgroupOf (centralizer z)) :=
          relIndex_le_of_le_right (planeComplement_core_le_sup a) (by
            rw [relIndex_sup_left,planeCore_radical_index]; decide)
        _ = 16 := by rw [relIndex_sup_left,planeCore_radical_index]
    omega
  · exact map_le_iff_le_comap.mpr (he.symm.le.trans inf_le_left)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
