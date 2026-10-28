module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinarySquares
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.HexadLocals.BlockExclusion
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The actual binary M₂₂ hexad intersection

The fixed hexad of the source involution has a full preimage I in L with
an elementary kernel of order 32 and quotient A₆. The original S normalizes
this preimage: H normalizes L, and S fixes the canonical square projection.
Adjoining all of S retains characteristic two, since I is normal with a
two-group upper quotient. The literal A₆ section excludes every χ₀ block.
Therefore the source block condition puts I ∨ S in M; native hexad maximality
then identifies the original intersection L ∩ M with I.

Neither C_S(L) nor the possible outer action is factored away. This is the
binary residual intersection, not the direct M₂₂ conclusion of 2.3.9(7)(f).
Source: Aschbacher--Smith I.2.2(6), 2.3.8(4), and 2.3.9(7), pp.412,523,526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers
open M22Local Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {C : GroupClass}
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

omit [Finite G] in
private theorem hexad_normalized_of_fixed
    (e : (L ⧸ center L) ≃* M22) (t : L) (ht : orderOf (projection e t) = 2)
    (A : Subgroup G) (hAL : A ≤ normalizer (L : Set G))
    (hfix : ∀ a ∈ A, a * (t : G) = (t : G) * a) :
    A ≤ normalizer ((hexadPreimage e (m22FixedPoints (projection e t))).map L.subtype : Set G) := by
  let I := hexadPreimage e (m22FixedPoints (projection e t))
  intro s hs
  let a := L.normalizerMonoidHom ⟨s,hAL hs⟩
  let b := MulAut.centralQuotientAction e a
  have hat : a t = t := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix s hs)
  have hb : b (projection e t) = projection e t := by
    change MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center L) t)) = _
    rw [MulAut.centralQuotientAction_apply,hat]
    rfl
  have hmap := m22FixedPoints_stabilizer_map (projection e t) ht b hb
  have hI : I.map a.toMonoidHom = I := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change projection e (a x) ∈ MulAction.stabilizer M22 (m22FixedPoints (projection e t))
      change e (QuotientGroup.mk' (center L) (a x)) ∈ _
      rw [← MulAut.centralQuotientAction_apply]
      rw [← hmap]
      exact mem_map_of_mem b.toMonoidHom hx
    · intro x hx
      refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
      have hy : b.symm (projection e x) ∈ MulAction.stabilizer M22 (m22FixedPoints (projection e t)) := by
        rw [← mem_map_equiv,hmap]
        exact hx
      have he : projection e (a.symm x) = b.symm (projection e x) := by
        apply b.injective
        rw [b.apply_symm_apply]
        change MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center L) (a.symm x))) = _
        rw [MulAut.centralQuotientAction_apply,a.apply_symm_apply]
        rfl
      change projection e (a.symm x) ∈ MulAction.stabilizer M22 (m22FixedPoints (projection e t))
      rw [he]
      exact hy
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (I.map L.subtype).map (MulAut.conj s).toMonoidHom = I.map L.subtype
  have he : (MulAut.conj s).toMonoidHom.comp L.subtype = L.subtype.comp a.toMonoidHom := rfl
  rw [map_map,he,← map_map,hI]

private theorem hexad_characteristic_two
    (e : (L ⧸ center L) ≃* M22) (hZ : IsPGroup 2 (center L))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    centralizer (pCore 2 (hexadPreimage e B) : Set (hexadPreimage e B)) ≤
      pCore 2 (hexadPreimage e B) := by
  apply (localProjection e (MulAction.stabilizer M22 B)).centralizer_pCore_le_of_surjective_pKernel
    (localProjection_surjective e _)
  · rw [localProjection_ker]
    exact hZ.comap_subtype
  · exact m22Hexad_stabilizer_core_selfCentralizing hB

private theorem hexad_surjection
    (e : (L ⧸ center L) ≃* M22) (hZ : Nat.card (center L) = 2)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ f : hexadPreimage e B →* alternatingGroup (Fin 6),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let N := (hexadRadical e B).subgroupOf (hexadPreimage e B)
  let f := (hexadQuotientEquiv e hB).toMonoidHom.comp (QuotientGroup.mk' N)
  refine ⟨f,(hexadQuotientEquiv e hB).surjective.comp (QuotientGroup.mk'_surjective N),?_⟩
  change IsPGroup 2 ((hexadQuotientEquiv e hB).toMonoidHom.comp (QuotientGroup.mk' N)).ker
  rw [MonoidHom.ker_comp_of_injective _ _ (hexadQuotientEquiv e hB).injective,QuotientGroup.ker_mk']
  let : IsElementaryAbelian 2 (hexadRadical e B) := hexadRadical_elementary e hZ hB
  exact (IsElementaryAbelian.isPGroup 2 (hexadRadical e B)).comap_subtype

omit [Finite G] in
private theorem normalized_join_alternating
    (I A : Subgroup G) (hp : IsPGroup 2 A) (hn : A ≤ normalizer (I : Set G))
    (f : I →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    AlternatingPowerTwoExtension (I ⊔ A : Subgroup G) 6 := by
  let X := I ⊔ A
  let N := I.subgroupOf X
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le I.le_normalizer hn)
  let e : N ≃* I := subgroupOfEquivOfLe (show I ≤ X from le_sup_left)
  let b := (MulEquiv.funUnique (Fin 1) (alternatingGroup (Fin 6))).symm
  let F : N →* (Fin 1 → alternatingGroup (Fin 6)) := b.toMonoidHom.comp (f.comp e.toMonoidHom)
  have hgen : N ⊔ A.subgroupOf X = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ← MonoidHom.range_eq_map,range_subtype]
  refine ⟨N,inferInstance,isPGroup_quotient_of_sup_eq_top N _ hp.comap_subtype hgen,
    1,F,b.surjective.comp (hf.comp e.surjective),?_⟩
  change IsPGroup 2 (b.toMonoidHom.comp (f.comp e.toMonoidHom)).ker
  rw [MonoidHom.ker_comp_of_injective _ _ b.injective,← MonoidHom.comap_ker]
  exact hk.comap_of_injective e.toMonoidHom e.injective

/-- The source block premise forces the entire binary fixed-hexad join,
including the full original S, into M. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_hexad_join_le
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      let I := (hexadPreimage e B).map L.subtype
      B ∈ m22Blocks ∧
      (I ⊔ (S : Subgroup H).map H.subtype) ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) ∧
      AlternatingPowerTwoExtension (I ⊔ (S : Subgroup H).map H.subtype : Subgroup G) 6 ∧
      I ⊔ (S : Subgroup H).map H.subtype ≤ M := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  obtain ⟨t,ht,hto,htn,htS,_⟩ := BinaryAmbient.source_square_projection c hG structural115Input sourceC d hc
  have hZ : Nat.card (center L) = 2 := by simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  have hZp : IsPGroup 2 (center L) := IsPGroup.of_card (n := 1) (by simpa using hZ)
  have hqt : orderOf (projection e t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow,show t ^ 2 = 1 by simpa only [hto] using pow_orderOf_eq_one t,map_one]
    · intro he
      exact htn (projection_ker e ▸ he)
  let B := m22FixedPoints (projection e t)
  have hB : B ∈ m22Blocks := m22FixedPoints_mem_blocks _ hqt
  let I := (hexadPreimage e B).map L.subtype
  let A := (S : Subgroup H).map H.subtype
  have hk : pCore 2 L ≠ ⊥ := by intro hb; rw [hb,card_bot] at hc; omega
  have hAN : A ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans (h.mathieuTwentyTwo_normalized hG.quasithin d.quotientIso hk)
  have hAI : A ≤ normalizer (I : Set G) := hexad_normalized_of_fixed e t hqt A hAN
    (fun s hs => mem_centralizer_iff.mp htS s hs)
  let ei : hexadPreimage e B ≃* I := (hexadPreimage e B).equivMapOfInjective L.subtype L.subtype_injective
  have hIc : centralizer (pCore 2 I : Set I) ≤ pCore 2 I :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 ei).mp (hexad_characteristic_two e hZp hB)
  have hXc := centralizer_pCore_sup_le 2 I A hIc (S.isPGroup'.map H.subtype) hAI
  have hXe : (I ⊔ A : Subgroup G) ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr hXc
  have hXO : (I ⊔ A : Subgroup G) ∈ Chapter1.HeOver G (A : Set G) := by
    refine ⟨hXe,?_,fun x hx => (show A ≤ I ⊔ A from le_sup_right) hx⟩
    intro hb
    change _ ⊓ centralizer _ ≤ _ at hXe
    rw [hb] at hXe
    have hz1 : z = 1 := hXe ⟨(show A ≤ I ⊔ A from le_sup_right) h.mem_sylow,by
      intro y hy
      have hy1 : y = 1 := hy
      simp [hy1]⟩
    simpa [hz1] using h.involution
  obtain ⟨f,hf,hfk⟩ := hexad_surjection e hZ hB
  let fi := f.comp ei.symm.toMonoidHom
  have hfik : IsPGroup 2 fi.ker := by
    change IsPGroup 2 (f.comp ei.symm.toMonoidHom).ker
    rw [← MonoidHom.comap_ker]
    exact hfk.comap_of_injective ei.symm.toMonoidHom ei.symm.injective
  have hshape := normalized_join_alternating I A (S.isPGroup'.map H.subtype) hAI
    fi (hf.comp ei.symm.surjective) hfik
  refine ⟨t,ht,hto,htn,hB,hXO,hshape,?_⟩
  by_contra hn
  obtain ⟨b⟩ := h.blocks (I ⊔ A) (sup_le_sup (map_subtype_le _) le_rfl) hXO hn
  obtain ⟨K,ha,hout,hmov⟩ := b.exists_escapingBlock hn
  exact hout (blockObstruction_of_a6PowerTwoExtension M A _ hshape K ha hmov)


/-- The original intersection is exactly the full binary hexad preimage.
Its elementary kernel has order 32, so this result does not substitute the
order-16 kernel of the direct M₂₂ model. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_intersection
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ B, B ∈ m22Blocks ∧ M.subgroupOf L = hexadPreimage e B ∧
      Nonempty (M.subgroupOf L ≃* BinaryPermutation.SixCoreExtension.Model) ∧
      ∃ U : Subgroup (M.subgroupOf L), ∃ _ : U.Normal,
        IsElementaryAbelian 2 U ∧ Nat.card U = 32 ∧
        Nonempty (((M.subgroupOf L) ⧸ U) ≃* alternatingGroup (Fin 6)) := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  let := h.quasisimple
  obtain ⟨t,ht,hto,htn,hB,_,_,hle⟩ := c.mathieuTwentyTwo_binary_hexad_join_le hG sourceC d hc
  let B := m22FixedPoints (projection e t)
  have hleI : hexadPreimage e B ≤ M.subgroupOf L := by
    intro x hx
    exact hle ((show (hexadPreimage e B).map L.subtype ≤
        (hexadPreimage e B).map L.subtype ⊔ (S : Subgroup H).map H.subtype from le_sup_left)
      (mem_map_of_mem L.subtype hx))
  have hmax : IsCoatom (hexadPreimage e B) :=
    isCoatom_comap_of_surjective (projection_surjective e) (m22_hexad_stabilizer_isCoatom B hB)
  have hproper : M.subgroupOf L ≠ ⊤ := fun hn => h.outside (subgroupOf_eq_top.mp hn)
  have heq : M.subgroupOf L = hexadPreimage e B := (hmax.le_iff_eq hproper).mp hleI
  refine ⟨B,hB,heq,?_,?_⟩
  · obtain ⟨r⟩ := M22Local.Binary.exists_hexadRecognition_of_perfect e hZ hB
    exact ⟨(MulEquiv.subgroupCongr heq).trans r.modelEquiv⟩
  · rw [heq]
    let U := (hexadRadical e B).subgroupOf (hexadPreimage e B)
    let : U.Normal := hexadRadical_normal e B
    let : IsElementaryAbelian 2 (hexadRadical e B) := hexadRadical_elementary e hZ hB
    have heU : IsElementaryAbelian 2 U :=
      IsElementaryAbelian.of_surjective
        (subgroupOfEquivOfLe (hexadRadical_le e B)).symm.toMonoidHom
        (subgroupOfEquivOfLe (hexadRadical_le e B)).symm.surjective
    refine ⟨U,inferInstance,heU,?_,⟨hexadQuotientEquiv e hB⟩⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe (hexadRadical_le e B)).toEquiv,
      hexadRadical_card e hB,hZ]

end CFSG.Quasithin.Chapter2.ComponentRefinement
