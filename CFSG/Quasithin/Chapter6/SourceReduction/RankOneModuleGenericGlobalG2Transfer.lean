module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow
public import Theory.GroupTheory.SylowIndexTwoExtension

/-!
# The all-degree G₂ involution catalogue and centralizer lower bound

Generalized Thompson transfer puts every ambient involution into the
original S, without requiring S=T. The compatible local involution
reduction and ambient nonfusion then give exactly the two marked long
and short classes. Both representatives still use the same actual
parabolic comparison and lie in L join O²(H).

The long root centralizes all of the model unipotent group, of order q⁶.
The established four-coordinate calculation gives q⁴ for the short root.
Transport along the same right map computes both centralizers in the
original S. Conjugating these two-groups into any ambient involution
centralizer proves its Sylow two-subgroup has order at least q⁴.

This supplies the lower-bound half of F.4.38 at even degrees. The source
outer involution, its centralizer's Sylow placement and its smaller order
remain to be established; no equality S=T or completion isomorphism is
asserted here. The Chapter 12 companion supplies the literal applications.

Source: Aschbacher–Smith F.4.27, F.4.35 and F.4.37–38, printed
pp.288,292–294, and 5.3.3, p.659 (`refs/quasithin.pdf`). Internal imports
reuse the inverse-Sylow and centralizer transport proofs in this family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The same compatible comparison marks both classes of all ambient
involutions, including even original degrees, without assuming S=T. -/
theorem Preparation.g2_ambient_involution_classes_of_transfer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (G2CompletionFusion.long (1:F))).val ∧
        v.val = (e.right.symm (G2CompletionFusion.short (1:F))).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        ∀ x : G, orderOf x=2 → IsConj z.val x ∨ IsConj v.val x := by
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses⟩ :=
    d.g2_completion_involution_classes h hH hp F he
  refine ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := d.g2_involution_fused_into_sourceS h hH.1.1.2 hp F he x hx
  have hSJ : sourceS L H ≤ L ⊔ residual H :=
    ((d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.2 1).trans le_sup_right
  let yJ : (L ⊔ residual H : Subgroup G) := ⟨y,hSJ hy⟩
  have hy2 : orderOf yJ=2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    change orderOf y=2
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  rcases hclasses yJ hy hy2 with hc | hc
  · exact Or.inl (((L ⊔ residual H : Subgroup G).subtype.map_isConj hc).trans hxy.symm)
  · exact Or.inr (((L ⊔ residual H : Subgroup G).subtype.map_isConj hc).trans hxy.symm)

open Atlas.G2 Atlas.G2.LieParabolicSetup

/-- The marked long and short roots have centralizers in S of orders q⁶ and q⁴.
This is an equality in the original source subgroup, not the full centralizer. -/
theorem Preparation.g2_marked_source_centralizer_orders
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let z : G := (e.right.symm (G2CompletionFusion.long (1:F))).val
    let v : G := (e.right.symm (G2CompletionFusion.short (1:F))).val
    Nat.card (sourceS L H ⊓ centralizer ({z} : Set G) : Subgroup G)=Nat.card F^6 ∧
      Nat.card (sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G)=Nat.card F^4 := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have hS := source_g2_inverse_sylow_image d h hTH e
  have hz := G2ShortSylow.centralizer_card_transport f hf _ hS (G2CompletionFusion.long 1)
  have hv := G2ShortSylow.centralizer_card_transport f hf _ hS (G2CompletionFusion.short 1)
  have hUC : unipotent ≤ centralizer ({rootA (1:F)} : Set (Model F)) := by
    intro u hu
    rw [unipotent_eq_range] at hu
    obtain ⟨t,rfl⟩ := hu
    exact mem_centralizer_singleton_iff.mpr (unipotentProduct_commute_rootA t 1)
  constructor
  · apply hz.trans
    change Nat.card (unipotent ⊓ centralizer ({rootA (1:F)} : Set (Model F)) : Subgroup (Model F)) = _
    rw [inf_eq_left.mpr hUC,card_unipotent]
  · exact hv.trans G2ShortSylow.short_sylow_centralizer_card

private theorem centralizer_sylow_card_lower
    (S : Subgroup G) (hS : IsPGroup 2 S) (x y : G) (hxy : IsConj y x)
    (P : Sylow 2 (centralizer ({x} : Set G))) :
    Nat.card (S ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ Nat.card P := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  let a : G ≃* G := MulAut.conj g
  let U := S ⊓ centralizer ({y} : Set G)
  let C := centralizer ({x} : Set G)
  let D := U.map a.toMonoidHom
  have hDC : D ≤ C := by
    rintro _ ⟨u,hu,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change a u * x=x * a u
    have hh := congrArg a (mem_centralizer_singleton_iff.mp hu.2)
    simpa only [map_mul,show a y=x from hg] using hh
  have hD : IsPGroup 2 D := (hS.to_le (show U ≤ S from inf_le_left)).map _
  have hh := card_le_sylow_two (hD.comap_subtype (K := C)) P
  change Nat.card (D.subgroupOf C) ≤ Nat.card P at hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv,
    show Nat.card D=Nat.card U from card_map_of_injective a.injective] at hh
  exact hh

/-- Every ambient involution centralizer has a Sylow two-subgroup of order
at least q⁴. This is the lower bound used against an outer-involution centralizer. -/
theorem Preparation.g2_involution_centralizer_sylow_lower_bound
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (x : G) (hx : orderOf x=2) (P : Sylow 2 (centralizer ({x} : Set G))) :
    Nat.card F^4 ≤ Nat.card P := by
  obtain ⟨e,z,v,hz,hv,_,_,_,_,hc⟩ := d.g2_ambient_involution_classes_of_transfer h hH hp F he
  obtain ⟨hzcard,hvcard⟩ := d.g2_marked_source_centralizer_orders h hH.1.1.2 F e
  rw [←hz] at hzcard
  rw [←hv] at hvcard
  rcases hc x hx with hzx | hvx
  · have hb := centralizer_sylow_card_lower (sourceS L H) (pCore_isPGroup.map _) x z.val hzx P
    rw [hzcard] at hb
    exact (Nat.pow_le_pow_right (Nat.card_pos : 0<Nat.card F) (by decide : 4≤6)).trans hb
  · have hb := centralizer_sylow_card_lower (sourceS L H) (pCore_isPGroup.map _) x v.val hvx P
    rwa [hvcard] at hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
