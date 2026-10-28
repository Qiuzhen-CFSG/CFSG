module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsSecondAction
public import Theory.Representation.BinarySevenCode.WeightFourNatural

/-!
# The entire natural seed of the second terminal block residual

The omega splitting reduces movement to the chosen module. The residual
fixes the four support letters, so its moved seed vanishes there. The
existing nonzero weight-two point and the transitive A₃ action give every
word on the three complementary letters. Thus the entire seed is the
natural two-dimensional module through the original quotient marking.
It has order four and centralizer equal to the residual's two-core.

The final application supplies the local-factor record's quotient,
natural-module and weight-two fields, conditional on the still pending
literal residual identification, intersection identity and Thompson
identity. Those remain with qt-d-1231-terminal-product; this is not a
constructor of ProductAnalysis. ComponentAnalysis is discharged by the
final terminal assembly, qt-d-1231-terminal.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.812.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)
 theorem secondResidual_commutator_le_chosen
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ⁅P.Z,P.secondPointResidual⁆ ≤ ⁅V,P.secondPointResidual⁆ := by
  have hRL : P.secondPointResidual ≤ L :=
    (P.secondPointResidual_le_Le structural escape C).trans ((map_subtype_le _).trans inf_le_left)
  have hMV : ⁅V,P.secondPointResidual⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp (hRL.trans S.chosen.normalizes)
  rw [P.omega_split structural escape]
  apply commutator_sup_le_of_relative_normal
    ((P.Z ⊓ centralizer (L : Set G)) ⊔ (P.Z ⊓ V))
    (P.Z ⊓ centralizer (L : Set G)) (P.Z ⊓ V) P.secondPointResidual ⁅V,P.secondPointResidual⁆
    (sup_le ((inf_le_right.trans (centralizer_le (hMV.trans S.chosen.le_component))).trans
      (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans (normalizer_commutator_ge_left V P.secondPointResidual)))
    le_sup_left le_sup_right ?_ (commutator_mono inf_le_right le_rfl)
  rw [commutator_eq_bot_iff_le_centralizer.mpr (inf_le_right.trans (centralizer_le hRL))]
  exact bot_le

theorem secondResidual_moved_support_zero
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (x : V) (hx : (x : G) ∈ ⁅P.Z,P.secondPointResidual⁆) :
    ∀ i ∈ WeightTwoGeometry.support (D.model.coordinates P.point).toAdd,
      (D.model.coordinates x).toAdd.val i = 0 := by
  have hRL : P.secondPointResidual ≤ L :=
    (P.secondPointResidual_le_Le structural escape C).trans ((map_subtype_le _).trans inf_le_left)
  intro i hi
  let eval : V →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative
      ((Pi.evalAddMonoidHom (fun _ : Fin 7 => ZMod 2) i).comp evenWords.subtype.toAddMonoidHom)).comp
        D.model.coordinates.toMonoidHom
  let N := eval.ker.map V.subtype
  have hVN : ⁅V,P.secondPointResidual⁆ ≤ N := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr y hy
    let n := inclusion inf_le_left
      (inclusion P.secondPointResidual_le_pointNormalizer ⟨r,hr⟩)
    have hpi : (D.model.permutation n).symm i = i :=
      (Equiv.symm_apply_eq _).mpr (P.secondResidual_fixes_support ⟨r,hr⟩ ⟨i,hi⟩).symm
    let y' : V := ⟨y,hy⟩
    let c : V := V.normalizerMonoidHom n y' * y'⁻¹
    refine ⟨c,?_,rfl⟩
    change (D.model.coordinates c).toAdd.val i = 0
    have he := D.model.equivariant n y'
    dsimp only [c]
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv]
    change ((D.model.coordinates (V.normalizerMonoidHom _ y')).toAdd +
      -(D.model.coordinates y').toAdd).val i = 0
    rw [he]
    change (D.model.coordinates y').toAdd.val ((D.model.permutation n).symm i) +
      -(D.model.coordinates y').toAdd.val i = 0
    rw [hpi,add_neg_cancel]
  obtain ⟨y,hy,he⟩ := hVN (P.secondResidual_commutator_le_chosen structural escape C hx)
  have hey : y = x := Subtype.ext he
  subst y
  exact hy

theorem secondResidual_moved_le_V
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ⁅P.Z,P.secondPointResidual⁆ ≤ V :=
  (P.secondResidual_commutator_le_chosen structural escape C).trans
    (le_normalizer_iff_commutator_le_left.mp
      (((P.secondPointResidual_le_Le structural escape C).trans
        ((map_subtype_le _).trans inf_le_left)).trans S.chosen.normalizes))

theorem secondResidual_support_zero_mem_moved
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (x : V) (hx : ∀ i ∈ WeightTwoGeometry.support (D.model.coordinates P.point).toAdd,
      (D.model.coordinates x).toAdd.val i = 0) :
    (x : G) ∈ ⁅P.Z,P.secondPointResidual⁆ := by
  by_cases hx1 : x = 1
  · simpa only [hx1,OneMemClass.coe_one] using
      (one_mem (⁅P.Z,P.secondPointResidual⁆ : Subgroup G))
  obtain ⟨v,hv1,_,hvm⟩ := P.exists_weight_two_in_secondPointResidual_commutator structural escape C
  let w := (D.model.coordinates P.point).toAdd
  obtain ⟨a,ha⟩ := (WeightFourNatural.range_extendThree w P.weight_four
    (D.model.coordinates v).toAdd).mpr
      (P.secondResidual_moved_support_zero structural escape C v hvm)
  obtain ⟨b,hb⟩ := (WeightFourNatural.range_extendThree w P.weight_four
    (D.model.coordinates x).toAdd).mpr hx
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hv1
    apply D.model.coordinates.injective
    apply Multiplicative.toAdd.injective
    simpa only [ha0,map_zero,map_one,toAdd_one] using ha.symm
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hx1
    apply D.model.coordinates.injective
    apply Multiplicative.toAdd.injective
    simpa only [hb0,map_zero,map_one,toAdd_one] using hb.symm
  obtain ⟨g,hg⟩ := WeightFourNatural.threeCore_transitive a b ha0 hb0
  obtain ⟨r,hr⟩ := P.secondResidualProjection_surjective structural escape g
  let n := inclusion P.secondPointResidual_le_pointNormalizer r
  have he := WeightFourNatural.extendThree_equivariant w P.weight_four
    (D.model.pointPermutation P.point n) a
  have hperm : (WeightFourLocal.pointEquiv w P.weight_four
      (D.model.pointPermutation P.point n)).2 = g.val := congrArg Subtype.val hr
  rw [hperm] at he
  change WeightFourNatural.extendThree w P.weight_four
    (BinaryPermutation.alternatingCoreRepresentation (Fin 3) g a) = _ at he
  rw [hg,ha,hb] at he
  have hcoords := D.model.equivariant ⟨n,n.property.1⟩ v
  have hfix : V.normalizerMonoidHom ⟨n,n.property.1⟩ v = x :=
    D.model.coordinates.injective (Multiplicative.toAdd.injective (hcoords.trans he.symm))
  have hnorm := normalizer_commutator_ge_right P.Z P.secondPointResidual r.property
  have hm := (mem_normalizer_iff.mp hnorm (v : G)).mp hvm
  exact (congrArg Subtype.val hfix) ▸ hm

def secondResidual_natural
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Representation.BinaryConjugationSection P.secondPointResidual ⁅P.Z,P.secondPointResidual⁆ ⊥
      ((BinaryPermutation.alternatingCoreRepresentation (Fin 3)).comp
        ((P.secondResidualQuotientEquiv structural escape C).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 P.secondPointResidual)))) := by
  let M := ⁅P.Z,P.secondPointResidual⁆
  let w := (D.model.coordinates P.point).toAdd
  have hMV : M ≤ V := P.secondResidual_moved_le_V structural escape C
  let f : Multiplicative (BinaryPermutation.core (Fin 3)) →* M :=
    (((V.subtype.comp D.model.coordinates.symm.toMonoidHom).comp
      (AddMonoidHom.toMultiplicative (WeightFourNatural.extendThree w P.weight_four).toAddMonoidHom))).codRestrict M (by
        intro a
        apply P.secondResidual_support_zero_mem_moved structural escape C
          (D.model.coordinates.symm (Multiplicative.ofAdd
            (WeightFourNatural.extendThree w P.weight_four a.toAdd)))
        have hh := (WeightFourNatural.range_extendThree w P.weight_four
          (WeightFourNatural.extendThree w P.weight_four a.toAdd)).mp ⟨a.toAdd,rfl⟩
        rw [D.model.coordinates.apply_symm_apply]
        exact hh)
  have hf (a : Multiplicative (BinaryPermutation.core (Fin 3))) :
      (D.model.coordinates ⟨(f a : G),hMV (f a).property⟩).toAdd =
        WeightFourNatural.extendThree w P.weight_four a.toAdd := by
    exact congrArg Multiplicative.toAdd (D.model.coordinates.apply_symm_apply _)
  have hfi : Function.Injective f := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    apply WeightFourNatural.extendThree_injective w P.weight_four
    exact (hf a).symm.trans ((congrArg
      (fun x : M => (D.model.coordinates ⟨(x : G),hMV x.property⟩).toAdd) hab).trans (hf b))
  have hfs : Function.Surjective f := by
    intro x
    let xV : V := ⟨x,hMV x.property⟩
    have hx := P.secondResidual_moved_support_zero structural escape C xV x.property
    obtain ⟨a,ha⟩ := (WeightFourNatural.range_extendThree w P.weight_four
      (D.model.coordinates xV).toAdd).mpr hx
    refine ⟨Multiplicative.ofAdd a,?_⟩
    apply Subtype.ext
    change (D.model.coordinates.symm (Multiplicative.ofAdd
      (WeightFourNatural.extendThree w P.weight_four a)) : G) = x
    have he : D.model.coordinates.symm (Multiplicative.ofAdd
        (WeightFourNatural.extendThree w P.weight_four a)) = xV :=
      D.model.coordinates.injective ((D.model.coordinates.apply_symm_apply _).trans
        (congrArg Multiplicative.ofAdd ha))
    exact congrArg Subtype.val he
  let e : Multiplicative (BinaryPermutation.core (Fin 3)) ≃* M := MulEquiv.ofBijective f ⟨hfi,hfs⟩
  have hecoord (a : M) : WeightFourNatural.extendThree w P.weight_four (e.symm a).toAdd =
      (D.model.coordinates ⟨(a : G),hMV a.property⟩).toAdd := by
    calc
      _ = (D.model.coordinates ⟨(f (e.symm a) : G),hMV (f (e.symm a)).property⟩).toAdd := (hf _).symm
      _ = _ := congrArg (fun x : M => (D.model.coordinates ⟨(x : G),hMV x.property⟩).toAdd)
        (e.apply_symm_apply a)
  have hn : P.secondPointResidual ≤ normalizer (M : Set G) :=
    normalizer_commutator_ge_right P.Z P.secondPointResidual
  refine {
    section_le := le_normalizer_iff_commutator_le_right.mp
      ((show P.Z ≤ (T : Subgroup G) from fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).1).trans
        ((P.sylow_le_pointNormalizer structural).trans P.secondPointResidual_normalized))
    kernel_le := bot_le
    normalized := hn
    coordinates := e.symm.toMonoidHom
    onto := e.symm.surjective
    kernel_eq := by
      ext a
      change e.symm a = 1 ↔ (a : G) = 1
      rw [e.symm.map_eq_one_iff]
      exact Subtype.ext_iff
    equivariant := ?_ }
  intro r a
  apply WeightFourNatural.extendThree_injective w P.weight_four
  change WeightFourNatural.extendThree w P.weight_four
    (e.symm ⟨(r : G)*a*(r : G)⁻¹,(mem_normalizer_iff.mp (hn r.property) a).mp a.property⟩).toAdd = _
  rw [hecoord]
  change _ = WeightFourNatural.extendThree w P.weight_four
    (BinaryPermutation.alternatingCoreRepresentation (Fin 3)
      (P.secondResidualQuotientEquiv structural escape C (QuotientGroup.mk' _ r)) (e.symm a).toAdd)
  rw [secondResidualQuotientEquiv_apply]
  change _ = WeightFourNatural.extendThree w P.weight_four
    (BinaryPermutation.coreRepresentation (Fin 3)
      (WeightFourLocal.pointEquiv w P.weight_four
        (D.model.pointPermutation P.point (inclusion P.secondPointResidual_le_pointNormalizer r))).2
          (e.symm a).toAdd)
  rw [WeightFourNatural.extendThree_equivariant,hecoord]
  exact D.model.equivariant (inclusion inf_le_left
    (inclusion P.secondPointResidual_le_pointNormalizer r)) ⟨a,hMV a.property⟩

theorem secondResidual_moved_card
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Nat.card (⁅P.Z,P.secondPointResidual⁆ : Subgroup G) = 4 := by
  have h := (P.secondResidual_natural structural escape C).card_section
  simpa only [WeightFourNatural.threeCore_card,card_bot,mul_one] using h

theorem secondResidual_moved_centralizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.secondPointResidual ⊓ centralizer (⁅P.Z,P.secondPointResidual⁆ : Subgroup G) =
      P.secondPointResidual.pCoreIn 2 := by
  let N := P.secondResidual_natural structural escape C
  let f := P.secondResidualProjection structural escape
  have hi : Function.Injective N.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [N.kernel_eq,bot_subgroupOf]
  have he (r : P.secondPointResidual) (a : (⁅P.Z,P.secondPointResidual⁆ : Subgroup G)) :=
    N.equivariant r a
  apply le_antisymm
  · rintro r ⟨hr,hc⟩
    have hf : f ⟨r,hr⟩ = 1 := by
      apply WeightFourNatural.threeCore_faithful
      intro x
      obtain ⟨a,ha⟩ := N.onto (Multiplicative.ofAdd x)
      have hconj : r * (a : G) * r⁻¹ = a :=
        mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc) _ a.property).symm
      have h := he ⟨r,hr⟩ a
      have ha' : (⟨r * (a : G) * r⁻¹,
          (mem_normalizer_iff.mp (N.normalized hr) a).mp a.property⟩ :
          (⁅P.Z,P.secondPointResidual⁆ : Subgroup G)) = a := Subtype.ext hconj
      rw [ha'] at h
      change (N.coordinates a).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 3) (f ⟨r,hr⟩) (N.coordinates a).toAdd at h
      rw [ha] at h
      exact h.symm
    have hk : (⟨r,hr⟩ : P.secondPointResidual) ∈ pCore 2 P.secondPointResidual :=
      (P.secondResidualProjection_ker structural escape C) ▸ hf
    exact mem_map_of_mem P.secondPointResidual.subtype hk
  · rintro r ⟨s,hs,rfl⟩
    refine ⟨s.property,mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have hs' : s ∈ f.ker := by
      change s ∈ (P.secondResidualProjection structural escape).ker
      rw [P.secondResidualProjection_ker structural escape C]
      exact hs
    have h := he s ⟨a,ha⟩
    change (N.coordinates ⟨(s : G) * a * (s : G)⁻¹,_⟩).toAdd =
      BinaryPermutation.alternatingCoreRepresentation (Fin 3) (f s) (N.coordinates ⟨a,ha⟩).toAdd at h
    rw [show f s = 1 from hs',map_one,Module.End.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp
      (congrArg Subtype.val (hi (Multiplicative.toAdd.injective h)))).symm

/-- Once the source intersection calculation identifies R₂ with the literal
L₂, this supplies the exact quotient and natural-action fields of both
terminal analyses, together with their original weight-two witness. The
identification remains with qt-d-1231-terminal-product. -/
theorem second_seed_of_residual_eq
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hR : P.secondPointResidual = P.L2) :
    ∃ q : (P.L2 ⧸ pCore 2 P.L2) ≃* alternatingGroup (Fin 3),
      Nonempty (Representation.BinaryConjugationSection P.L2 ⁅P.Z,P.L2⁆ ⊥
        ((BinaryPermutation.alternatingCoreRepresentation (Fin 3)).comp
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.L2))))) ∧
      ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
        (v : G) ∈ ⁅P.Z,P.L2⁆ := by
  rw [← hR]
  exact ⟨P.secondResidualQuotientEquiv structural escape C,
    ⟨P.secondResidual_natural structural escape C⟩,
    P.exists_weight_two_in_secondPointResidual_commutator structural escape C⟩

/-- The second natural seed now discharges its literal fields in the local
factor analysis. The three remaining geometric premises are retained with
this task's assembly owner, qt-d-1231-terminal-product. -/
theorem localFactorAnalysis_of_residual_identifications
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hR : P.secondPointResidual = P.L2)
    (hinter : P.L1 =
      (primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
        (P.K ⊓ normalizer (L : Set G)).subtype)
    (hthompson : ⁅P.L2, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2) :
    Nonempty P.LocalFactorAnalysis := by
  obtain ⟨q,⟨N⟩,hv⟩ := P.second_seed_of_residual_eq structural escape C hR
  exact ⟨{
    omega_split := P.omega_split structural escape
    normalizer_image := D.permutation_range_eq_top structural escape
    local_product := by rw [← hR]; exact P.Le_eq_L1_sup_secondPointResidual structural escape C
    intersection_residual := hinter
    second_quotient := q
    second_natural := N
    second_thompson := hthompson
    weight_two := hv }⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
