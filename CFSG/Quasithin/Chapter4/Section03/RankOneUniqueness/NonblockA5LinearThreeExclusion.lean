module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5FieldFour
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSDoubledMarking
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# Excluding the actual linear-three star row in the original A₅ context

The original marked permutation core lies in the initial moved omega layer.
The source MS pair marks that layer as one or two natural SL₃ modules and
marks the original L-image as the line local group. Its radical fixes the
original module, so both natural coordinates lie in the SL₂ plane. A cubic
element fixes a nonzero vector in the original permutation core, whereas its
faithful SL₂ image fixes no nonzero vector in either plane.

All actions below use the original L and its original A₅ marking. In
particular the original module is not assumed invariant under K, and no
whole-core alternatives or star-row selection are inputs.
Source: Aschbacher–Smith, original 4.3.8–10, pp.616–617; the permutation
core obstruction also occurs in the proof of 16.4.7, p.1187.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem line_fixed_cubic_eq_zero {F : Type*} [Field F] [CharP F 2]
    (g : lineLocalSL F) (hg : orderOf (lineLocalAffineEquiv F g).right = 3)
    (v : Fin 3 → F)
    (hr : ∀ r ∈ lineRadicalSL F, r.val.val *ᵥ v = v)
    (hv : g.val.val *ᵥ v = v) : v = 0 := by
  let r := affineToLine F (⟨Multiplicative.ofAdd ![1,0],1⟩ : Matrix.SL2.Affine F)
  have hrr : r ∈ lineRadicalSL F := by
    rw [mem_lineRadicalSL_iff]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have hv2 : v 2 = 0 := by
    have h := congrArg (fun w : Fin 3 → F => w 0) (hr r hrr)
    have hh : v 0 + v 2 = v 0 := by
      simpa [r,affineToLine,Matrix.mulVec,dotProduct,Fin.sum_univ_three] using h
    exact add_left_cancel (hh.trans (add_zero (v 0)).symm)
  have hp : ![v 0,v 1] = (0 : Fin 2 → F) := by
    apply Matrix.SL2.cubic_fixed_eq_zero (lineLocalAffineEquiv F g).right hg
    ext i
    fin_cases i
    · have h := congrArg (fun w : Fin 3 → F => w 0) hv
      simpa [lineLocalAffineEquiv,lineToAffine,Matrix.mulVec,dotProduct,
        Fin.sum_univ_two,Fin.sum_univ_three,hv2] using h
    · have h := congrArg (fun w : Fin 3 → F => w 1) hv
      simpa [lineLocalAffineEquiv,lineToAffine,Matrix.mulVec,dotProduct,
        Fin.sum_univ_two,Fin.sum_univ_three,hv2] using h
  ext i
  fin_cases i
  · exact congrFun hp 0
  · exact congrFun hp 1
  · exact hv2

omit [Finite G] in
private theorem line_map
    (c : SourceConfiguration T L) {F : Type*} [Field F] [Finite F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (he : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ∃ q : L →* lineLocalSL F, Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ∀ l : L, (q l).val = linearThreeActor e ⟨l,c.le_component l.property⟩ := by
  let A := L.subgroupOf (K c)
  let a : A ≃* L := subgroupOfEquivOfLe c.le_component
  let f := linearThreeActor e
  let q : L →* lineLocalSL F := (MulEquiv.subgroupCongr he).toMonoidHom.comp
    ((f.subgroupMap A).comp a.symm.toMonoidHom)
  have hq : Function.Surjective q := (MulEquiv.subgroupCongr he).surjective.comp
    ((f.subgroupMap_surjective A).comp a.symm.surjective)
  let i : L →* K c := A.subtype.comp a.symm.toMonoidHom
  have hi : Function.Injective i := A.subtype_injective.comp a.symm.injective
  have hk : q.ker = (pCore 2 (K c)).comap i := by
    ext l
    change q l = 1 ↔ i l ∈ pCore 2 (K c)
    rw [Subtype.ext_iff]
    change e (QuotientGroup.mk' (pCore 2 (K c)) (i l)) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (i l)
  refine ⟨q,hq,?_,fun _ => rfl⟩
  rw [hk]
  exact pCore_isPGroup.comap_of_injective i hi

private theorem a5_line_coordinates_impossible
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) (hVA : V ≤ A)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (he : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F)
    (f : A → (Fin 3 → F) × (Fin 3 → F)) (hf : Function.Injective f)
    (hf1 : f 1 = 0)
    (hact : ∀ (k : K c) (u v : A), (v : G) = k * (u : G) * (k : G)⁻¹ →
      f v = ((linearThreeActor e k).val *ᵥ (f u).1,
        (linearThreeActor e k).val *ᵥ (f u).2)) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q,hq,hqk,hqval⟩ := line_map c e he
  let t := (q.pCoreQuotientEquiv hq hqk).trans (lineLocalSLCoreQuotientEquiv F)
  have ht (l : L) : t (QuotientGroup.mk' (pCore 2 L) l) =
      (lineLocalAffineEquiv F (q l)).right := rfl
  let b := d.quotient.symm.trans t
  have hb (l : L) : b (d.flag.module.action l) =
      (lineLocalAffineEquiv F (q l)).right := by
    rw [←d.quotient_mk l]
    exact (congrArg t (d.quotient.symm_apply_apply _)).trans (ht l)
  let s : BinaryPermutation.core (Fin 5) → A := fun v =>
    ⟨d.flag.module.map (Multiplicative.ofAdd v),hVA
      (d.flag.module.range_eq.le ⟨_,rfl⟩)⟩
  have hs : Function.Injective s := by
    intro u v huv
    exact Multiplicative.ofAdd.injective (d.flag.module.injective (congrArg Subtype.val huv))
  have hs0 : s 0 = 1 := Subtype.ext d.flag.module.map.map_one
  have hsact (l : L) (v : BinaryPermutation.core (Fin 5)) :
      f (s (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.module.action l).val v)) =
        ((q l).val.val *ᵥ (f (s v)).1,(q l).val.val *ᵥ (f (s v)).2) := by
    rw [hqval]
    apply hact
    exact (d.flag.module.equivariant l v).symm
  obtain ⟨a,ha,v,hv,hav⟩ := BinaryPermutation.AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  obtain ⟨l,hl⟩ := d.flag.module.onto a
  have hord : orderOf (lineLocalAffineEquiv F (q l)).right = 3 := by
    rw [←hb,hl]
    exact (orderOf_injective b.toMonoidHom b.injective a).trans ha
  have hfix : ((q l).val.val *ᵥ (f (s v)).1,
      (q l).val.val *ᵥ (f (s v)).2) = f (s v) := by
    have h := hsact l v
    rw [hl,hav] at h
    exact h.symm
  have hrad (r : lineLocalSL F) (hr : r ∈ lineRadicalSL F) :
      (r.val.val *ᵥ (f (s v)).1,r.val.val *ᵥ (f (s v)).2) = f (s v) := by
    obtain ⟨j,hj⟩ := hq r
    have hjcore : j ∈ pCore 2 L := by
      rw [←q.comap_pCore_of_ker_isPGroup hq hqk]
      change q j ∈ pCore 2 (lineLocalSL F)
      rw [hj,lineLocalSL_twoCore_eq]
      exact hr
    have hjone : d.flag.module.action j = 1 := by
      change j ∈ d.flag.module.action.ker
      rwa [d.flag.action_kernel]
    have h := hsact j v
    rw [hjone,hj] at h
    simpa using h.symm
  have hz1 := line_fixed_cubic_eq_zero (q l) hord (f (s v)).1
    (fun r hr => congrArg Prod.fst (hrad r hr)) (congrArg Prod.fst hfix)
  have hz2 := line_fixed_cubic_eq_zero (q l) hord (f (s v)).2
    (fun r hr => congrArg Prod.snd (hrad r hr)) (congrArg Prod.snd hfix)
  have hz : f (s v) = f (s 0) := by
    rw [hs0,hf1]
    exact Prod.ext hz1 hz2
  exact hv (hs (hf hz))

/-- The actual SL₃ star row is impossible for the original marked A₅ module.
The initial-layer marking is constructed from the source MS pair. -/
theorem not_linearThree_star_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) : False := by
  let E := linearThree_fullQuotientEquiv_of_a5 d c hf F e
  obtain ⟨mark,hm,hL,_⟩ := DoubledMarking.initial_line_and_centralizer d.chosen hf
    F.degree (linearThree_degree_gt_one_of_a5 d c hf F e) F.card_eq E
  have hVA : V ≤ movedCoreOmega c :=
    (Section02.Unitary.chosen_le_fullModule d.chosen).trans (InitialCenter.fullModule_le_initial hf)
  rcases hm with hm | hm
  · rw [HasSectionModel,bot_subgroupOf] at hm
    obtain ⟨_,_,_,hn,g,hg⟩ := hm
    let := hn
    let f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F.Carrier) :=
      QuotientGroup.quotientBot.symm.trans g
    apply a5_line_coordinates_impossible d c (movedCoreOmega c) hVA mark hL
      (fun u => ((f u).toAdd,0))
    · intro u v huv
      exact f.injective (Multiplicative.toAdd.injective (congrArg Prod.fst huv))
    · exact Prod.ext (congrArg Multiplicative.toAdd f.map_one) rfl
    · intro k u v hv
      apply Prod.ext
      · exact hg k u v hv
      · exact (Matrix.mulVec_zero (m := Fin 3) (n := Fin 3) _).symm
  · rw [HasSectionModel,bot_subgroupOf] at hm
    obtain ⟨_,_,_,hn,g,hg⟩ := hm
    let := hn
    let f : movedCoreOmega c ≃* Multiplicative ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)) :=
      QuotientGroup.quotientBot.symm.trans g
    exact a5_line_coordinates_impossible d c (movedCoreOmega c) hVA mark hL
      (fun u => (f u).toAdd) (Multiplicative.toAdd.injective.comp f.injective)
      (congrArg Multiplicative.toAdd f.map_one) hg

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
