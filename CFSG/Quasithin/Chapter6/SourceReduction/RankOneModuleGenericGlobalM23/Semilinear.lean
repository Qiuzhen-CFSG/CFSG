module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Orders
public import Theory.GroupTheory.Recognition.QuasithinM23.SemilinearQuotient
/-!
# The actual ΓL₂(4) quotient of the original maximal local

The compatible linear comparison identifies L as the special affine plane
group over the selected field E. Nonmaximality gives |E| = 4, and an actual
field equivalence transports those coordinates to the native four-field.
The original M = N_G(L) acts on O₂(M) = O₂(L); its full centralizer is
O₂(M), so the quotient action is faithful. The original L image is exactly
natural SL₂(4). The exact natural normalizer and the proved quotient order
360 identify M/O₂(M) with ΓL₂(4), retaining both the L image and the
pointwise conjugation equation on the entire core.

This proves Aschbacher–Smith 5.2.11(3), printed pp.653–654
(`refs/quasithin.pdf`). Both original amalgam orientations are retained.
It supplies local structure for 5.2.15, not ambient M₂₃ recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {X : Type*} [Group X] [Finite X]
private theorem affine_normalizer_quotient
    (K : Subgroup X) [K.Normal] (eK : K ≃* Matrix.SL2.Affine F)
    (hc : K.pCoreIn 2 = pCore 2 X)
    (hC : centralizer (pCore 2 X : Set X) = pCore 2 X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 360) :
    ∃ e : (X ⧸ pCore 2 X) ≃* Gamma,
      K.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) = special.range ∧
      ∃ b : Multiplicative V ≃* pCore 2 X,
        ∀ (x : X) (v : Multiplicative V),
          (b (Multiplicative.ofAdd (natural (e (QuotientGroup.mk' (pCore 2 X) x)) v.toAdd)) : X) =
            x * (b v : X) * x⁻¹ := by
  let c := ChapterC.SL2Affine.coreEquiv eK
  let b : Multiplicative V ≃* pCore 2 X := c.trans
    (((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hc))
  let a : X →* BinaryGL := QuasithinM23.binaryAutEquiv.toMonoidHom.comp
    ((MulAut.congr b.symm).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut (pCore 2 X)))
  have ha (x : X) (v : Multiplicative V) :
      (b (Multiplicative.ofAdd (a x v.toAdd)) : X) = x * (b v : X) * x⁻¹ := by
    change (b (Multiplicative.ofAdd (QuasithinM23.binaryAutEquiv
      ((MulAut.congr b.symm) ((MulAut.conjNormal : X →* MulAut (pCore 2 X)) x)) v.toAdd)) : X) = _
    rw [QuasithinM23.binaryAutEquiv_apply]
    change (b (b.symm ((MulAut.conjNormal x) (b v))) : X) = _
    rw [b.apply_symm_apply]
    rfl
  have hk : a.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ QuasithinM23.binaryAutEquiv.toMonoidHom
      QuasithinM23.binaryAutEquiv.injective,
      MonoidHom.ker_comp_of_injective _ (MulAut.congr b.symm).toMonoidHom
        (MulAut.congr b.symm).injective,
      MulAut.conjNormal_ker_eq_centralizer,hC]
  have hmark (k : K) : a (k : X) = action (eK k).right := by
    apply LinearEquiv.ext
    intro v
    apply Multiplicative.ofAdd.injective
    apply b.injective
    apply Subtype.ext
    have h := congrArg (fun t : K => (t : X)) (ChapterC.SL2Affine.coreEquiv_action eK k
      (Multiplicative.ofAdd v))
    change (b (Multiplicative.ofAdd (a (k : X) v)) : X) =
      (b (Matrix.SL2.naturalAction F (eK k).right (Multiplicative.ofAdd v)) : X)
    exact (ha (k : X) (Multiplicative.ofAdd v)).trans h.symm
  have hmap : K.map a = action.range := by
    ext g
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨(eK ⟨k,hk⟩).right,(hmark ⟨k,hk⟩).symm⟩
    · rintro ⟨k,rfl⟩
      let u := eK.symm (SemidirectProduct.inr k)
      refine ⟨u,u.property,?_⟩
      rw [hmark,eK.apply_symm_apply]
      rfl
  obtain ⟨e,he,hmap⟩ := QuasithinM23.gamma_quotient_of_natural_image (pCore 2 X) K a hk hmap hcard
  exact ⟨e,hmap,b,fun x v => by rw [he]; exact ha x v⟩
variable {G : Type*} [Group G] [Finite G]
/-- Source 5.2.11(3), retaining the actual conjugation action on O₂(M). -/
theorem Preparation.linear_nonmaximal_semilinear_quotient
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ e : ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))) ≃* Gamma,
      (L.subgroupOf (normalizer (L : Set G))).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) = special.range ∧
      ∃ b : Multiplicative V ≃* pCore 2 (normalizer (L : Set G)),
        ∀ (x : normalizer (L : Set G)) (v : Multiplicative V),
          (b (Multiplicative.ofAdd (natural (e (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))) x)) v.toAdd)) : normalizer (L : Set G)) =
            x * (b v : normalizer (L : Set G)) * x⁻¹ := by
  obtain ⟨_,_,hE4,hcores,hcore,_,hC,_,_,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp E hm hE he hnonmax
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional h hH hp E hm hE he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  have hcard := (d.linear_exceptional_left_orders h hH hp E hm hE he hJ hKJ).2.2
  have ha : Nonempty (L ≃* Matrix.SL2.Affine E) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp E hm hE 0 true e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine E)⟩
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp E hm hE 0 false e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine E)⟩
  let := Fintype.ofFinite E
  let f : E ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hE4,card_field])
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let eK : K ≃* Matrix.SL2.Affine F := (subgroupOfEquivOfLe L.le_normalizer).trans
    (ha.some.trans (QuasithinM23.affineFieldEquiv f))
  let : K.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hc : K.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn_subgroupOf 2 L M L.le_normalizer,←hcore]
    exact comap_map_eq_self_of_injective M.subtype_injective _
  have hcent : centralizer (pCore 2 M : Set M) = pCore 2 M := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ centralizer (L.pCoreIn 2 : Set G) := by
        rw [←hcore]
        rintro y ⟨u,hu,rfl⟩
        exact congrArg Subtype.val (hx u hu)
      rw [hC,←hcore] at hh
      exact (mem_map_iff_mem M.subtype_injective).mp hh
    · intro x hx y hy
      have hx' : (x : G) ∈ L.pCoreIn 2 := hcore ▸ mem_map_of_mem M.subtype hx
      have hy' : (y : G) ∈ L.pCoreIn 2 := hcore ▸ mem_map_of_mem M.subtype hy
      let : IsElementaryAbelian 2 (pCore 2 L) := (hcores 0).1
      let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
      exact Subtype.ext (setLike_mul_comm hy' hx')
  exact affine_normalizer_quotient K eK hc hcent hcard

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
