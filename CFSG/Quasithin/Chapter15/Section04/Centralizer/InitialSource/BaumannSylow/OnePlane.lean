module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.ResidualLift
public import CFSG.Quasithin.ChapterB.Section02.Baumann
public import Theory.GroupAction.KleinFourAlphaGeometry
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The one-plane Baumann argument

On an actual normal four-group, the two cubic-conjugate Thompson images
have fixed codimension one and generate the action; the residual has
fixed codimension two. These facts verify all hypotheses of B.2.18 and
then give the Baumann Sylow conclusion of B.6.10.

Source: Aschbacher--Smith, B.2.18 and B.6.10, printed pp.81 and117.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open ChapterB ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private noncomputable def fixedEquiv (W : Subgroup G) [W.Normal] (A : Subgroup G) :
    (W ⊓ centralizer (A : Set G) : Subgroup G) ≃
      FixedPoints.subgroup (A.map (MulAut.conjNormal : G →* MulAut W)) W where
  toFun w := ⟨⟨w,w.property.1⟩, by
    rw [FixedPoints.mem_subgroup]
    rintro ⟨a,⟨g,hg,rfl⟩⟩
    apply Subtype.ext
    change g*(w:G)*g⁻¹=w
    exact mul_inv_eq_iff_eq_mul.mpr (w.property.2 g hg)⟩
  invFun w := ⟨w.val,w.val.property, by
    intro a ha
    have hw := (FixedPoints.mem_subgroup
      (M := A.map (MulAut.conjNormal : G →* MulAut W)) (α := W) (a := w.val)).mp
      w.property ⟨MulAut.conjNormal a,mem_map_of_mem _ ha⟩
    have hh := congrArg (fun x : W => (x:G)) hw
    change a*(w.val:G)*a⁻¹=w.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Finite G] in
private noncomputable def faithfulQuotient (W : Subgroup G) [W.Normal] :
    (G ⧸ centralizer (W : Set G)) ≃* (MulAut.conjNormal : G →* MulAut W).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (MulAut.conjNormal_ker_eq_centralizer W).symm).trans
      (QuotientGroup.quotientKerEquivRange MulAut.conjNormal)

private theorem noStrong (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 4) (R : Subgroup G) : NoStrongOffenders W R := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour W := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  intro A _ hAe _
  let ρ := (MulAut.conjNormal : G →* MulAut W)
  let e := faithfulQuotient W
  let f := ρ.range.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := ρ.range.subtype_injective.comp e.injective
  have he : f.comp (actionMap W) = ρ := by
    apply MonoidHom.ext
    intro g
    rfl
  have hm : (A.map (actionMap W)).map f = A.map ρ := by rw [map_map,he]
  have hc : Nat.card (A.map ρ) = Nat.card (A.map (actionMap W)) := by
    rw [←hm,card_map_of_injective hf]
  let : IsElementaryAbelian 2 (A.map ρ) := hm ▸ hAe.map f
  have hh := IsKleinFour.two_subgroup_rank_le_fixed_codim (A.map ρ)
    (IsElementaryAbelian.isPGroup 2 _)
  rw [hc,←Nat.card_congr (fixedEquiv W A)] at hh
  unfold fixedCodim
  rw [hcard]
  exact hh

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

theorem alpha_decomposition_from_one_plane
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 4) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 (centralizer (W : Set G)))
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 3)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map
      (MulAut.conjNormal : G →* MulAut W)) = 2) :
    thompsonAlpha (R : Subgroup G) =
      (thompsonAlpha (R : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (W ⊓ centralizer (elementaryAbelianMaxJ (R : Subgroup G) : Set G)) := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour W := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  let ρ := (MulAut.conjNormal : G →* MulAut W)
  have hk : IsPGroup 2 ρ.ker := (MulAut.conjNormal_ker_eq_centralizer W).symm ▸ hker
  let J := elementaryAbelianMaxJ (R : Subgroup G)
  let B := J.map ρ
  let C := (pResidual 2 G).map ρ
  obtain ⟨r,hr,hgen⟩ := IsKleinFour.two_three_two_conjugates B C hJcard hLcard
  obtain ⟨x,hx,hxr⟩ := hr
  let Jx := J.map (MulAut.conj x).toMonoidHom
  let F : Bool → Subgroup G := fun b => if b then Jx else J
  have hJF : J ≤ ⨆ i, F i := by exact le_iSup_of_le false le_rfl
  have hJT : J ≤ (R : Subgroup G) := sSup_le fun A hA => hA.1
  have hJself := (maxJ_self_rank (R : Subgroup G)).1
  have hJrank := (maxJ_self_rank (R : Subgroup G)).2
  have hkR : ρ.ker ≤ (R : Subgroup G) := hk.le_sylow_of_normal R
  have hCQ : (R : Subgroup G) ⊓ centralizer (W : Set G) = ρ.ker := by
    rw [←MulAut.conjNormal_ker_eq_centralizer W]
    exact inf_eq_right.mpr hkR
  have hpL : IsPGroup 3 ((pResidual 2 G).map ρ) :=
    IsPGroup.of_card (n := 1) (by simpa using hLcard)
  have hcore := residual_core_le_kernel ρ hpL
  let q := actionMap W
  let e := faithfulQuotient W
  let f := ρ.range.subtype.comp e.toMonoidHom
  have hfi : Function.Injective f := ρ.range.subtype_injective.comp e.injective
  have hfq : f.comp q = ρ := by apply MonoidHom.ext; intro g; rfl
  have hmap (A : Subgroup G) : (A.map q).map f = A.map ρ := by rw [map_map,hfq]
  have hconj : Jx.map ρ = B.map (MulAut.conj r).toMonoidHom := by
    change (J.map (MulAut.conj x).toMonoidHom).map ρ =
      (J.map ρ).map (MulAut.conj r).toMonoidHom
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro g
    change ρ (x*g*x⁻¹) = r*ρ g*r⁻¹
    rw [map_mul,map_mul,map_inv,hxr]
  have hJxcard : Nat.card (Jx.map ρ) = 2 := by
    rw [hconj,card_map_of_injective (MulAut.conj r).injective]
    exact hJcard
  have hcod (i : Bool) : fixedCodim W (F i) = 1 := by
    have hc : Nat.card ((F i).map ρ) = 2 := by
      cases i
      · exact hJcard
      · exact hJxcard
    unfold fixedCodim
    rw [Nat.card_congr (fixedEquiv W (F i)),
      IsKleinFour.two_fixed_card _ hc,hcard]
    norm_num
  have hcodL : fixedCodim W (pResidual 2 G) = 2 := by
    unfold fixedCodim
    rw [Nat.card_congr (fixedEquiv W (pResidual 2 G)),
      IsKleinFour.three_fixed_card _ hLcard,hcard]
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
        have hgker : g ∈ ρ.ker := (MulAut.conjNormal_ker_eq_centralizer W).ge hg.2
        have hp : IsPGroup 2 (ρ.ker.subgroupOf (pResidual 2 G)) := hk.comap_subtype
        have hle : ρ.ker.subgroupOf (pResidual 2 G) ≤ pCore 2 (pResidual 2 G) :=
          le_sSup ⟨inferInstance,hp⟩
        refine mem_map.mpr ⟨⟨g,hgL⟩,?_,rfl⟩
        change QuotientGroup.mk' (pCore 2 (pResidual 2 G)) ⟨g,hgL⟩ ∈ frattini _
        have hk : QuotientGroup.mk' (pCore 2 (pResidual 2 G)) (⟨g,hgL⟩ : pResidual 2 G) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (hle hgker)
        exact hk.symm ▸ one_mem _
      no_strong := noStrong W hcard _
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
        rw [hmap,Subgroup.map_iSup]
        change C ≤ ⨆ i, ((F i).map q).map f
        simp only [hmap,iSup_bool_eq,F,Bool.false_eq_true,if_false,if_true]
        rw [hconj,show J.map ρ = B from rfl,sup_comm,hgen]
        exact le_top
      codimension_sum := by simp only [hcod,hcodL]; decide }
  exact lemma_B_2_18_2 W (R : Subgroup G) F hh hJF


/-- The one-plane action discharges B.6.10's actual Sylow conclusion. -/
theorem sylow_from_one_plane
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 4) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 (centralizer (W : Set G)))
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 3)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map
      (MulAut.conjNormal : G →* MulAut W)) = 2) :
    Chapter1.IsSylowIn 2 (baumann (R : Subgroup G))
      (pResidual 2 G ⊔ baumann (R : Subgroup G)) := by
  have hk : IsPGroup 2 (MulAut.conjNormal : G →* MulAut W).ker :=
    (MulAut.conjNormal_ker_eq_centralizer W).symm ▸ hker
  have hp : IsPGroup 3 ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) :=
    IsPGroup.of_card (n := 1) (by simpa using hLcard)
  exact sylow_of_alpha R W MulAut.conjNormal hk
    (MulAut.conjNormal_ker_eq_centralizer W) hp
    (alpha_decomposition_from_one_plane R W hcard hWR hker hLcard hJcard)

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
