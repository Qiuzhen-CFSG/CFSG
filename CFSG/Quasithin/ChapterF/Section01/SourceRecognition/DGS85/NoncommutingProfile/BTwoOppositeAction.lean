module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoOppositeGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCenterAction

/-!
# Constructing opposite geometry without shifted-pair assumptions

The earlier marked natural center action constructs the literal D geometry
for either Chapter 10 branch. Opposite Sylow images separate D from the
local quotient, and complementary fixed spaces split its central supplement.
The intersection of the residual with Z lies in the actual center-section
kernel Omega_1(Z(L_alpha)). No middle-vertex natural action is needed.
Source: DGS, *Groups and Graphs* (1985), 10.1 and 10.4, pp.154--156.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

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

/-- The earlier center action supplies the D geometry in both branches,
including the precise residual-center intersection bound. -/
theorem BTwoCenterActionData.exists_oppositeGeometry (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {v m w t : Vertex (family P)}
    (c : BTwoCenterActionData (family P) v m w k W)
    (g : c.actor) (hmove : (g : G) • m = t)
    (hop : c.quotient g ∉ normalizer (c.imageSylow : Set SL(2,k)))
 :
    ∃ d : BTwoOppositeGeometry (family P) t v m w ((g : G) • w),
      d.actor = c.actor ∧
      d.residual ⊓ Z (family P) v ≤ omegaCenterIn c.actor := by
  let := finite_endpoints h
  let F := family P
  let : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let L := c.actor
  let π := c.quotient
  let σ := c.representation
  let S := c.imageSylow
  let e := c.coordinates
  let z := (g : G) • w
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hne : S ≠ π g • S := fun he => hop (Sylow.smul_eq_iff_mem_normalizer.mp he.symm)
  have hcomp := sl2_sylow_fixed_isCompl σ S (π g • S) hne c.quadratic c.generated c.fixed_bot
  have hZconj : (Z F v).map (MulAut.conj (g : G)).toMonoidHom = Z F v := by
    rw [←Z_translate,hgv]
  have hQconj : (Q F v).map (MulAut.conj (g : G)).toMonoidHom = Q F v := by
    rw [←Q_translate,hgv]
  have hQt : Q F t = (Q F m).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [←Q_translate,hmove]
  have hZm : Z F z ≤ L := by
    rw [Z_translate]
    exact conjugate_le L (Z F w) c.critical_le g
  have hZz : ((Z F z).subgroupOf L).map π = (π g • S : Sylow 2 SL(2,k)) := by
    rw [Z_translate,quotient_conjugate L (Z F w) c.critical_le π g,c.critical_image]
    rfl
  have hQtm : ((Q F t).subgroupOf L).map π = (π g • S : Sylow 2 SL(2,k)) := by
    rw [hQt,quotient_conjugate L (Q F m) c.neighbor_core_le π g,c.neighbor_image]
    rfl
  have hsep : D F m t ≤ Q F v := by
    intro x hx
    let xL : L := ⟨x,c.neighbor_core_le hx.1⟩
    have hxS : π xL ∈ (S : Subgroup SL(2,k)) := by
      rw [←c.neighbor_image]
      exact mem_map_of_mem π (show xL ∈ (Q F m).subgroupOf L from hx.1)
    have hxT : π xL ∈ ((π g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) := by
      rw [←hQtm]
      exact mem_map_of_mem π (show xL ∈ (Q F t).subgroupOf L from hx.2)
    have hxker : xL ∈ π.ker := disjoint_def.mp (sylow_disjoint_of_ne S (π g • S) hne) hxS hxT
    exact (show xL ∈ (Q F v).subgroupOf L from c.kernel ▸ hxker)
  have hgen : c.actor = (Z F w ⊔ Z F z) ⊔ Q F v := by
    let R := (Z F w ⊔ Z F z) ⊔ Q F v
    have hRL : R ≤ L := sup_le (sup_le c.critical_le hZm) c.core_le
    have hmap : (R.subgroupOf L).map π = ⊤ := by
      rw [subgroupOf_sup (sup_le c.critical_le hZm) c.core_le,
        subgroupOf_sup c.critical_le hZm,Subgroup.map_sup,Subgroup.map_sup,c.critical_image,hZz]
      apply top_unique
      apply le_trans _ le_sup_left
      rw [show ((π g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) =
        (S : Subgroup SL(2,k)).map (MulAut.conj (π g)).toMonoidHom from rfl,
        Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S hop]
    have he : R.subgroupOf L = ⊤ :=
      map_injective_of_ker_le π (by rw [c.kernel]; exact comap_mono le_sup_right)
        le_top (hmap.trans (map_top_of_surjective π c.onto).symm)
    have hm := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le hRL,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm.symm
  have hsharp : Nat.card (W ⧸ fixedSpace σ (((Z F w).subgroupOf L).map π)) =
      (centralizer (Z F w : Set G)).relIndex (Z F v) := by
    rw [c.critical_image,c.sharp_index,←inf_relIndex_left (Z F v) (Q F w),
      ←inf_relIndex_left (Z F v) (centralizer (Z F w : Set G)),c.centralizer_intersection]
  have hfixed : e.imageSpace (Z F v ⊓ Q F w) = fixedSpace σ S := by
    rw [←c.centralizer_intersection,
      BinaryConjugationSection.image_centralizer_eq_fixed_of_sharp_index σ π e (Z F w) hsharp,
      c.critical_image]
  have hinter : (Z F v ⊓ Q F w).conjBy (g : G) = Z F v ⊓ Q F z := by
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g : G)).injective,hZconj,←Q_translate]
  have hfixed' : e.imageSpace (Z F v ⊓ Q F z) = fixedSpace σ (π g • S : Sylow 2 SL(2,k)) := by
    rw [←hinter,e.imageSpace_conjBy _ inf_le_left g,hfixed]
    exact (Representation.SL2SylowFixedRecognition.fixedSpace_conjugate σ S (π g)).symm
  have hker : omegaCenterIn L ≤ Z F v ⊓ Q F w := by
    intro x hx
    have hxZ := e.kernel_le hx
    have hxfix : (e.coordinates ⟨x,hxZ⟩).toAdd ∈
        fixedSpace σ (((Z F w).subgroupOf L).map π) := by
      have he := (e.coordinates_eq_one_iff ⟨x,hxZ⟩).mpr hx
      rw [he]
      exact Submodule.zero_mem _
    have hxc := (BinaryConjugationSection.fixed_coordinates_iff_of_sharp_index
      σ π e (Z F w) hsharp ⟨x,hxZ⟩).mp hxfix
    exact c.centralizer_intersection ▸ (show x ∈ Z F v ⊓ centralizer (Z F w : Set G) from ⟨hxZ,hxc⟩)
  have hspan : Z F v = (Z F v ⊓ Q F w) ⊔ (Z F v ⊓ Q F z) := by
    apply e.section_eq_sup_of_imageSpace_sup_top _ _ inf_le_left inf_le_left (hker.trans le_sup_left)
    rw [hfixed,hfixed']
    exact hcomp.sup_eq_top
  have hcover := bTwo_core_cover_of_sylow_product h hS hb c.middle c.terminal c.critical_product
  have hopcover : Q F t ≤ Z F v ⊔ Q F z := by
    have hm := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hcover
    rwa [←hQt,Subgroup.map_sup,hZconj,←Q_translate] at hm
  have hresker : ((D F m t ⊓ Q F w) ⊓ Q F z) ⊓ Z F v ≤ omegaCenterIn L := by
    intro x hx
    let a : Z F v := ⟨x,hx.2⟩
    have hxw : (e.coordinates a).toAdd ∈ e.imageSpace (Z F v ⊓ Q F w) :=
      (e.mem_imageSpace_iff _ _).mpr ⟨a,⟨hx.2,hx.1.1.2⟩,rfl⟩
    have hxz : (e.coordinates a).toAdd ∈ e.imageSpace (Z F v ⊓ Q F z) := by
      exact (e.mem_imageSpace_iff _ _).mpr ⟨a,⟨hx.2,hx.1.2⟩,rfl⟩
    rw [hfixed] at hxw
    rw [hfixed'] at hxz
    have hx0 : (e.coordinates a).toAdd = 0 := by
      exact hcomp.disjoint.le_bot ⟨hxw,hxz⟩
    exact (e.coordinates_eq_one_iff a).mp (Multiplicative.toAdd.injective hx0)
  refine ⟨{
    previous := ?_
    middle := c.middle
    terminal := c.terminal
    opposite := ?_
    actor := c.actor
    actor_generators := hgen
    cover := inf_le_left.trans hcover
    opposite_cover := inf_le_right.trans hopcover
    center_span := hspan
    separated := hsep }, rfl, hresker⟩
  · have he := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr c.middle.symm
    change (graph F).Adj ((g : G) • m) ((g : G) • v) at he
    rwa [hmove,hgv] at he
  · have he := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr c.terminal
    change (graph F).Adj ((g : G) • m) ((g : G) • w) at he
    rwa [hmove] at he


end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
