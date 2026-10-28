module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.NoStrongSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.TwoSylow

/-!
# Alpha decomposition from the four-dimensional action

The two conjugates of the Thompson image generate the base subgroup.  Their
fixed-space codimensions verify the original hypotheses of B.2.18, giving its
alpha decomposition for the actual odd residual.  This supplies the source
module argument in the proof of Theorem 15.4.12.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
open ChapterB ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]

private theorem maxJ_self_rank (R : Subgroup G) :
    elementaryAbelianMaxJ (elementaryAbelianMaxJ R) = elementaryAbelianMaxJ R ∧
      twoRank (elementaryAbelianMaxJ R) = twoRank R := by
  let J := elementaryAbelianMaxJ R
  have hJR : J ≤ R := sSup_le fun A hA => hA.1
  have hr : twoRank J = twoRank R := twoRank_eq_of_intermediate R J le_rfl hJR
  have ho : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder J :=
    le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R J le_rfl).1
      (elementaryAbelianMaxOrder_le_and_j_le_of_eq J R hJR).1
  exact ⟨le_antisymm (sSup_le fun A hA => hA.1)
    ((elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R J le_rfl).2 ho),hr⟩

theorem alpha_decomposition_from_action
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (d : Action W) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 d.actor.ker)
    (hL : (pResidual 2 G).map d.actor = rotations)
    (hJbase : (elementaryAbelianMaxJ (R : Subgroup G)).map d.actor ≤ base)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map d.actor) = 4) :
    thompsonAlpha (R : Subgroup G) =
      (thompsonAlpha (R : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (W ⊓ centralizer (elementaryAbelianMaxJ (R : Subgroup G) : Set G)) := by
  let J := elementaryAbelianMaxJ (R : Subgroup G)
  let B := J.map d.actor
  obtain ⟨r,hr,hgen⟩ := Concrete.base_four_two_conjugates B hJbase hJcard
  obtain ⟨x,hx,hxr⟩ := hL.ge hr
  let Jx := J.map (MulAut.conj x).toMonoidHom
  let F : Bool → Subgroup G := fun b => if b then Jx else J
  have hJF : J ≤ ⨆ i, F i := by exact le_iSup_of_le false le_rfl
  have hJT : J ≤ (R : Subgroup G) := sSup_le fun A hA => hA.1
  have hJself := (maxJ_self_rank (R : Subgroup G)).1
  have hJrank := (maxJ_self_rank (R : Subgroup G)).2
  have hkR : d.actor.ker ≤ (R : Subgroup G) := hker.le_sylow_of_normal R
  have hCQ : (R : Subgroup G) ⊓ centralizer (W : Set G) = d.actor.ker := by
    rw [←Action.kernel d]
    exact inf_eq_right.mpr hkR
  have hcore : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ d.actor.ker := by
    let L := pResidual 2 G
    let C := (pCore 2 L).map L.subtype
    have hCp : IsPGroup 2 (C.map d.actor) := (pCore_isPGroup.map L.subtype).map d.actor
    have hCl : C.map d.actor ≤ rotations := (map_mono (map_subtype_le _)).trans_eq hL
    have hRp : IsPGroup 3 rotations := IsPGroup.of_card (n := 2) Concrete.rotations_card
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (C.map d.actor) rotations hCp hRp
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp ((le_inf le_rfl hCl).trans (disjoint_iff.mp hd).le))
  let q := actionMap W
  let e := Action.faithfulQuotient d
  let f := d.actor.range.subtype.comp e.toMonoidHom
  have hfi : Function.Injective f := d.actor.range.subtype_injective.comp e.injective
  have hfq : f.comp q = d.actor := by apply MonoidHom.ext; intro g; rfl
  have hmap (A : Subgroup G) : (A.map q).map f = A.map d.actor := by rw [map_map,hfq]
  have hconj : Jx.map d.actor = B.map (MulAut.conj r).toMonoidHom := by
    change (J.map (MulAut.conj x).toMonoidHom).map d.actor =
      (J.map d.actor).map (MulAut.conj r).toMonoidHom
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro g
    change d.actor (x*g*x⁻¹) = r*d.actor g*r⁻¹
    rw [map_mul,map_mul,map_inv,hxr]
  have hJxbase : Jx.map d.actor ≤ base := by rw [hconj]; exact (le_sup_right : B.map (MulAut.conj r).toMonoidHom ≤ _).trans_eq hgen
  have hJxcard : Nat.card (Jx.map d.actor) = 4 := by rw [hconj,card_map_of_injective (MulAut.conj r).injective]; exact hJcard
  have hcod (i : Bool) : fixedCodim W (F i) = 2 := by
    have hw : Nat.card W = 16 := by
      rw [Nat.card_congr d.coordinates.toEquiv,Nat.card_eq_fintype_card]
      decide +kernel
    have hfixed : Nat.card (FixedVectors ((F i).map d.actor)) = 4 := by
      cases i
      · exact Concrete.base_four_fixed_card B hJbase hJcard
      · exact Concrete.base_four_fixed_card _ hJxbase hJxcard
    unfold fixedCodim
    rw [Nat.card_congr (Action.fixedEquiv d (F i)),hfixed,hw]
    norm_num
  have hcodL : fixedCodim W (pResidual 2 G) = 4 := by
    have hw : Nat.card W = 16 := by
      rw [Nat.card_congr d.coordinates.toEquiv,Nat.card_eq_fintype_card]
      decide +kernel
    have hfixed : Nat.card (FixedVectors rotations) = 1 := by
      -- The independent nonzero rotations have no common nonzero fixed vector.
      have hzero : ∀ v : FixedVectors rotations, v.val = 0 := by
        intro v
        have h1 := v.property (rotationHom (Multiplicative.ofAdd (1,1))) ⟨_,rfl⟩
        exact (show ∀ v : Space, rotation (Multiplicative.ofAdd (1,1)) v = v → v = 0 by decide +kernel) v.val h1
      let : Subsingleton (FixedVectors rotations) := ⟨fun a b => Subtype.ext ((hzero a).trans (hzero b).symm)⟩
      let : Nonempty (FixedVectors rotations) := ⟨⟨0,fun g _ => g.val.map_zero⟩⟩
      exact Nat.card_unique
    unfold fixedCodim
    rw [Nat.card_congr (Action.fixedEquiv d (pResidual 2 G)),hL,hfixed,hw]
    norm_num
  have hh : HypothesesAD W (R : Subgroup G) F :=
    { R_two := R.isPGroup'
      V_le_R := hWR
      core_le := hCQ.symm ▸ hcore
      normalizes := by
        change pResidual 2 G ≤ normalizer (((R : Subgroup G) ⊓ centralizer (W : Set G) : Subgroup G) : Set G)
        rw [hCQ]
        exact le_normalizer_of_normal
      centralizer_le_frattini := by
        intro g hg
        have hgL : g ∈ pResidual 2 G := hg.1
        have hgker : g ∈ d.actor.ker := (Action.kernel d).ge hg.2
        have hp : IsPGroup 2 (d.actor.ker.subgroupOf (pResidual 2 G)) := hker.comap_subtype
        have hle : d.actor.ker.subgroupOf (pResidual 2 G) ≤ pCore 2 (pResidual 2 G) :=
          le_sSup ⟨inferInstance,hp⟩
        refine mem_map.mpr ⟨⟨g,hgL⟩,?_,rfl⟩
        change QuotientGroup.mk' (pCore 2 (pResidual 2 G)) ⟨g,hgL⟩ ∈ frattini _
        have hk : QuotientGroup.mk' (pCore 2 (pResidual 2 G)) (⟨g,hgL⟩ : pResidual 2 G) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (hle hgker)
        exact hk.symm ▸ one_mem _
      no_strong := Action.noStrong d _
      conjugate_into := by
        intro i
        cases i
        · refine ⟨1,one_mem _,?_⟩
          rintro _ ⟨j,hj,rfl⟩
          simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,one_mul,inv_one,mul_one] using hJT hj
        · refine ⟨x⁻¹,(pResidual 2 G).inv_mem hx,?_⟩
          have he : Jx.map (MulAut.conj x⁻¹).toMonoidHom = J := by
            rw [map_map]
            have hh : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
              apply MonoidHom.ext
              intro g
              simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,MonoidHom.id_apply,inv_inv]
              group
            rw [hh,map_id]
          exact he.le.trans hJT
      self_thompson := by
        intro i
        cases i
        · exact hJself
        · exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj x) J).trans (congrArg (map (MulAut.conj x).toMonoidHom) hJself)
      rank_eq := by
        intro i
        cases i
        · exact hJrank
        · exact (twoRank_map_equiv (MulAut.conj x) J).trans hJrank
      image_generation := by
        apply (map_le_map_iff_of_injective hfi).mp
        rw [hmap, hL, Subgroup.map_iSup]
        change rotations ≤ ⨆ i, ((F i).map q).map f
        simp only [hmap]
        simp only [iSup_bool_eq, F, Bool.false_eq_true, if_false, if_true]
        rw [hconj,show J.map d.actor = B from rfl]
        simpa only [sup_comm] using Concrete.rotations_le_base.trans_eq hgen.symm
      codimension_sum := by simp only [hcod,hcodL]; decide }
  exact lemma_B_2_18_2 W (R : Subgroup G) F hh hJF

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
