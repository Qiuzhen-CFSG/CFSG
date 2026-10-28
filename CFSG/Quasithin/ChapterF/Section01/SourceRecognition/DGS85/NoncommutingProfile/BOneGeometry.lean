module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCores
public import Theory.Representation.BinaryConjugationSection.SharpFixedIndex
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Sylow

/-!
# Constructing the opposite geometry from the marked Chapter 7 action

Choose an element of the actual local actor whose SL₂ image moves the
neighbor Sylow. The two Sylow images generate SL₂ and intersect trivially.
Their literal neighbor centers therefore generate the actor modulo its core,
and the two neighbor cores intersect inside that core. Sharpness of the
Chapter 7 reciprocal index identifies the fixed preimage with the actual
center/core intersection. Complementary Sylow fixed spaces then lift to the
required center span, retaining the full central denominator.

`BOneActionData` records earlier Chapter 6--7 inputs on the shared graph.
It assumes neither the opposite geometry nor Q=Z. The construction and
paired Frattini argument prove both core identities. Path parameters and
the b=2 alternatives remain separate obligations of Chapter 10.

Source: DGS, *Groups and Graphs* (1985), 6.2, 7.1, 10.1 and 10.4--10.5,
printed pp.118--119, 126--127 and 154--156.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

/-- Earlier source data at one oriented edge, with its actual quotient and conjugation section. -/
structure BOneActionData (F : Bool → Subgroup G) (v w : Vertex F)
    (k W : Type*) [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W] where
  adjacent : (graph F).Adj v w
  actor : Subgroup G
  actor_le : actor ≤ stabilizer F v
  core_le : Q F v ≤ actor
  neighbor_core_le : Q F w ≤ actor
  supplement : actor ⊔ (stabilizer F v ⊓ stabilizer F w) = stabilizer F v
  sylow : Sylow 2 (stabilizer F v)
  sylow_le_actor : (sylow : Subgroup (stabilizer F v)).map
    (stabilizer F v).subtype ≤ actor
  quotient : actor →* SL(2,k)
  onto : Function.Surjective quotient
  kernel : quotient.ker = (Q F v).subgroupOf actor
  representation : Representation (ZMod 2) SL(2,k) W
  coordinates : BinaryConjugationSection actor (Z F v) (omegaCenterIn actor)
    (representation.comp quotient)
  imageSylow : Sylow 2 SL(2,k)
  neighbor_image : ((Z F w).subgroupOf actor).map quotient = imageSylow
  core_cover : Q F v ≤ Z F v ⊔ Q F w
  centralizer_intersection : Z F v ⊓ centralizer (Z F w : Set G) = Z F v ⊓ Q F w
  sharp_index : Nat.card (W ⧸ fixedSpace representation imageSylow) = (Q F w).relIndex (Z F v)
  quadratic : IsQuadratic representation imageSylow
  generated : GeneratedByFixedSpace representation imageSylow
  fixed_bot : fixedSpace representation ⊤ = ⊥

private theorem conjugate_le (L A : Subgroup G) (hA : A ≤ L) (g : L) :
    A.map (MulAut.conj (g : G)).toMonoidHom ≤ L := by
  rintro _ ⟨a,ha,rfl⟩
  exact L.mul_mem (L.mul_mem g.property (hA ha)) (L.inv_mem g.property)

private theorem quotient_conjugate (L A : Subgroup G) (hA : A ≤ L)
    {J : Type*} [Group J] (π : L →* J) (g : L) :
    ((A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L).map π =
      ((A.subgroupOf L).map π).map (MulAut.conj (π g)).toMonoidHom := by
  have hc : (A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L =
      (A.subgroupOf L).map (MulAut.conj g).toMonoidHom := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugate_le L A hA g),map_map]
    have he : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp L.subtype := by ext a; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hA]
  rw [hc,map_map,map_map]
  congr 1
  ext a
  exact π.map_mul _ _ |>.trans (by rw [map_mul,map_inv]; rfl)

private theorem sylow_disjoint_of_ne {k : Type*} [Field k] [Finite k] [CharP k 2]
    (S T : Sylow 2 SL(2,k)) (hne : S ≠ T) :
    Disjoint (S : Subgroup SL(2,k)) (T : Subgroup SL(2,k)) := by
  apply disjoint_def.mpr
  intro x hxS hxT
  by_contra hx
  have hgen := Representation.SL2SylowFixedRecognition.sylow_sup_zpowers_eq_top T S hne.symm hxT hx
  have htop : (S : Subgroup SL(2,k)) = ⊤ := by
    simpa only [sup_eq_left.mpr (zpowers_le.mpr hxS)] using hgen
  apply Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S
  change normalizer ((S : Subgroup SL(2,k)) : Set SL(2,k)) = ⊤
  rw [htop]
  exact top_unique (⊤ : Subgroup SL(2,k)).le_normalizer

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Construct every opposite-geometry premise from the earlier marked action. -/
theorem exists_marked_oppositeCenterGeometry (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W) :
    ∃ g : c.actor, ∃ d : OppositeCenterGeometry (family P) v w ((g : G) • w),
      d.actor = c.actor ∧ c.quotient g ∉ normalizer (c.imageSylow : Set SL(2,k)) ∧
        ((g : G) • w) ≠ w := by
  let := finite_endpoints h
  let F := family P
  let : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let L := c.actor
  let π := c.quotient
  let σ := c.representation
  let S := c.imageSylow
  let d := c.coordinates
  obtain ⟨a,ha⟩ := SetLike.exists_not_mem_of_ne_top (normalizer (S : Set SL(2,k)))
    (Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S)
  obtain ⟨g,hg⟩ := c.onto a
  let u := (g : G) • w
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hne : S ≠ π g • S := by
    intro he
    exact ha (hg ▸ Sylow.smul_eq_iff_mem_normalizer.mp he.symm)
  have hcomp := sl2_sylow_fixed_isCompl σ S (π g • S) hne c.quadratic c.generated c.fixed_bot
  have hZQ (x : Vertex F) : Z F x ≤ Q F x := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hz)).1
  have hZwL : Z F w ≤ L := (hZQ w).trans c.neighbor_core_le
  have hZuL : Z F u ≤ L := by
    rw [Z_translate]
    exact conjugate_le L (Z F w) hZwL g
  have hQuL : Q F u ≤ L := by
    rw [Q_translate]
    exact conjugate_le L (Q F w) c.neighbor_core_le g
  have hZu : ((Z F u).subgroupOf L).map π = (π g • S : Sylow 2 SL(2,k)) := by
    rw [Z_translate,quotient_conjugate L (Z F w) hZwL π g,c.neighbor_image]
    rfl
  have hQw : ((Q F w).subgroupOf L).map π = (S : Subgroup SL(2,k)) := by
    apply S.is_maximal'
    · exact ((isPGroup_pCoreIn 2 (stabilizer F w)).of_equiv
        (subgroupOfEquivOfLe c.neighbor_core_le).symm).map π
    · rw [←c.neighbor_image]
      exact map_mono (comap_mono (hZQ w))
  have hQu : ((Q F u).subgroupOf L).map π = (π g • S : Sylow 2 SL(2,k)) := by
    rw [Q_translate,quotient_conjugate L (Q F w) c.neighbor_core_le π g,hQw]
    rfl
  have hsep : D F w u ≤ Q F v := by
    intro x hx
    let xL : L := ⟨x,c.neighbor_core_le hx.1⟩
    have hxS : π xL ∈ (S : Subgroup SL(2,k)) := by
      rw [←hQw]
      exact mem_map_of_mem π (show xL ∈ (Q F w).subgroupOf L from hx.1)
    have hxT : π xL ∈ ((π g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) := by
      rw [←hQu]
      exact mem_map_of_mem π (show xL ∈ (Q F u).subgroupOf L from hx.2)
    have hxker : xL ∈ π.ker := disjoint_def.mp (sylow_disjoint_of_ne S (π g • S) hne) hxS hxT
    exact (show xL ∈ (Q F v).subgroupOf L from c.kernel ▸ hxker)
  have hgen : c.actor = (Z F w ⊔ Z F u) ⊔ Q F v := by
    let R := (Z F w ⊔ Z F u) ⊔ Q F v
    have hRL : R ≤ L := sup_le (sup_le hZwL hZuL) c.core_le
    have hmap : (R.subgroupOf L).map π = ⊤ := by
      rw [subgroupOf_sup (sup_le hZwL hZuL) c.core_le,
        subgroupOf_sup hZwL hZuL,Subgroup.map_sup,Subgroup.map_sup,c.neighbor_image,hZu]
      apply top_unique
      apply le_trans _ le_sup_left
      rw [show ((π g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) =
        (S : Subgroup SL(2,k)).map (MulAut.conj (π g)).toMonoidHom from rfl,
        Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S (hg ▸ ha)]
    have he : R.subgroupOf L = ⊤ :=
      map_injective_of_ker_le π (by rw [c.kernel]; exact comap_mono le_sup_right)
        le_top (hmap.trans (map_top_of_surjective π c.onto).symm)
    have hm := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le hRL,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm.symm
  have hsharp : Nat.card (W ⧸ fixedSpace σ (((Z F w).subgroupOf L).map π)) =
      (centralizer (Z F w : Set G)).relIndex (Z F v) := by
    rw [c.neighbor_image,c.sharp_index,←inf_relIndex_left (Z F v) (Q F w),
      ←inf_relIndex_left (Z F v) (centralizer (Z F w : Set G)),c.centralizer_intersection]
  have hfixed : d.imageSpace (Z F v ⊓ Q F w) = fixedSpace σ S := by
    rw [←c.centralizer_intersection,
      BinaryConjugationSection.image_centralizer_eq_fixed_of_sharp_index σ π d (Z F w) hsharp,
      c.neighbor_image]
  have hZconj : (Z F v).map (MulAut.conj (g : G)).toMonoidHom = Z F v := by
    rw [←Z_translate,hgv]
  have hQconj : (Q F v).map (MulAut.conj (g : G)).toMonoidHom = Q F v := by
    rw [←Q_translate,hgv]
  have hinter : (Z F v ⊓ Q F w).conjBy (g : G) = Z F v ⊓ Q F u := by
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g : G)).injective,hZconj,←Q_translate]
  have hfixed' : d.imageSpace (Z F v ⊓ Q F u) = fixedSpace σ (π g • S : Sylow 2 SL(2,k)) := by
    rw [←hinter,d.imageSpace_conjBy _ inf_le_left g,hfixed]
    exact (Representation.SL2SylowFixedRecognition.fixedSpace_conjugate σ S (π g)).symm
  have hker : omegaCenterIn L ≤ Z F v ⊓ Q F w := by
    intro x hx
    have hxZ := d.kernel_le hx
    have hxfix : (d.coordinates ⟨x,hxZ⟩).toAdd ∈
        fixedSpace σ (((Z F w).subgroupOf L).map π) := by
      have he := (d.coordinates_eq_one_iff ⟨x,hxZ⟩).mpr hx
      rw [he]
      exact Submodule.zero_mem _
    have hxc := (BinaryConjugationSection.fixed_coordinates_iff_of_sharp_index
      σ π d (Z F w) hsharp ⟨x,hxZ⟩).mp hxfix
    exact c.centralizer_intersection ▸ (show x ∈ Z F v ⊓ centralizer (Z F w : Set G) from ⟨hxZ,hxc⟩)
  have hspan : Z F v = (Z F v ⊓ Q F w) ⊔ (Z F v ⊓ Q F u) := by
    apply d.section_eq_sup_of_imageSpace_sup_top _ _ inf_le_left inf_le_left (hker.trans le_sup_left)
    rw [hfixed,hfixed']
    exact hcomp.sup_eq_top
  have hcover : Q F v ≤ Z F v ⊔ Q F u := by
    have hm := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) c.core_cover
    rwa [hQconj,Subgroup.map_sup,hZconj,←Q_translate] at hm
  refine ⟨g, {
    adjacent := c.adjacent
    opposite_adjacent := ?_
    actor := c.actor
    actor_generators := hgen
    supplement := c.supplement
    sylow := c.sylow
    sylow_le_actor := c.sylow_le_actor
    core_cover := c.core_cover
    opposite_cover := hcover
    center_span := hspan
    separated := hsep }, rfl, ?_, ?_⟩
  · have he := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr c.adjacent
    change (graph F).Adj ((g : G) • v) u at he
    rwa [hgv] at he
  · exact hg ▸ ha
  · intro hu
    have he : ((Z F u).subgroupOf L).map π = ((Z F w).subgroupOf L).map π :=
      congrArg (fun x : Vertex F => ((Z F x).subgroupOf L).map π) hu
    rw [hZu,c.neighbor_image] at he
    exact hne (Sylow.ext he).symm
/-- Forget only the chosen conjugator; the marked constructor retains it for D=Z(L). -/
theorem exists_oppositeCenterGeometry (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W) :
    ∃ u : Vertex (family P), Nonempty (OppositeCenterGeometry (family P) v w u) := by
  obtain ⟨g,d,_,_⟩ := exists_marked_oppositeCenterGeometry h c
  exact ⟨(g : G) • w,⟨d⟩⟩

/-- The paired core conclusion of 10.5(b), without an opposite-geometry assumption. -/
theorem paired_cores_eq_centers_of_actions
    {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁) :
    Q (family P) (base (family P) false) = Z (family P) (base (family P) false) ∧
    Q (family P) (base (family P) true) = Z (family P) (base (family P) true) := by
  obtain ⟨u₀,⟨d₀⟩⟩ := exists_oppositeCenterGeometry h c₀
  obtain ⟨u₁,⟨d₁⟩⟩ := exists_oppositeCenterGeometry h c₁
  exact paired_cores_eq_centers h d₀ d₁

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
