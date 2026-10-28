module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingModels
public import CFSG.Quasithin.ChapterD.Section02.CyclicEndpoints
public import Theory.GroupTheory.PResidual.IndexThreeCommutator
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Cyclic-overlap endgame for the moving cubic reduction

The involution support classification eliminates the cyclic and elementary-nine
residuals, leaving only the extraspecial order-27 case. Marking its two cubic
axes and applying the binary norm kernel argument forces the residual center to
be trivial, contradicting extraspeciality.

The final consumer constructs escape from the same proper invariant quotient
and retains the original actor. Source: Aschbacher–Smith, 14.5.9–13 and the
following norm argument, printed pp.1015–1017; 14.7.2(3), printed p.1043,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem cubic_generated_cyclic_action_involution_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let U := W.subgroupOf D
    letI : U.Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 U :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (U : Set D)
    let q := QuotientGroup.mk' C
    let S := ((T : Subgroup G).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ t : D ⧸ C, orderOf t = 2 ∧ zpowers t = S ∧
      fixedCodim ρ (zpowers t) ≤ 2 ∧ pCore 3 (D ⧸ C) ⊔ zpowers t = ⊤ := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  let S := ((T : Subgroup G).subgroupOf D).map q
  let X := ((F.Li L 2).subgroupOf D).map q
  let P := pCore 3 (D ⧸ C)
  have hcore := cubic_generated_action_three_core_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT hout he
  have hYP : (Y.subgroupOf D).map q ≤ P := le_sup_right.trans hcore.2.1.le
  have hmove : ¬ X ≤ centralizer (P : Set (D ⧸ C)) := by
    intro hc
    apply cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hm hYp
    exact (hYP.trans (le_centralizer_iff.mp hc)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨A,hA,hB,hcod,t,ht,ht2,_,_,_⟩ :=
    cubic_generated_moved_prime_actor_of_moving_plane
      h hab structural previous faithful Y hYH hm hYp hYT hout he
      3 Nat.prime_three P inferInstance (by decide) pCore_isPGroup hmove
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  let B := (A.subgroupOf D).map q
  have hBS : B ≤ S := map_mono (subgroupOf_mono D hA.1)
  have hSc : Nat.card S = 2 := by
    obtain ⟨e⟩ := cubic_generated_action_sylow_order_two_of_moving_plane
      h hab structural previous faithful Y hYH hm hYp hYT hout he
    rw [Nat.card_congr e.toEquiv]
    simp
  have htS : zpowers t = S := eq_of_le_of_card_ge (zpowers_le.mpr (hBS ht))
    (by rw [hSc,Nat.card_zpowers,ht2])
  have hBt : B = zpowers t := le_antisymm (hBS.trans htS.ge) (zpowers_le.mpr ht)
  have hrank : rank B = 1 := by
    change Nat.log 2 (Nat.card B) = 1
    rw [hBt,Nat.card_zpowers,ht2]
    decide
  dsimp only
  refine ⟨t,ht2,htS,?_,?_⟩
  · change fixedCodim _ B ≤ rank B + 1 at hcod
    rw [hrank,hBt] at hcod
    exact hcod
  · rw [htS,←hcore.1]
    exact pResidual_sup_sylow_eq_top ((T.subtype hTD).mapSurjective (QuotientGroup.mk'_surjective C))


private theorem four_plane_full_commutator
    {D : Type*} [Group D] [Finite D] (P X : Subgroup D)
    (hp : Nat.card P = 4) (hX : IsPPerfect 2 X)
    (hn : X ≤ normalizer (P : Set D)) (hm : ⁅P,X⁆ ≠ ⊥) : ⁅P,X⁆ = P := by
  let B := ⁅P,X⁆
  have hBP : B ≤ P := le_normalizer_iff_commutator_le_left.mp hn
  have hcard : Nat.card B ∣ 2^2 := by simpa only [hp,show (2:ℕ)^2=4 from rfl] using card_dvd_of_le hBP
  obtain ⟨k,hk,hB⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcard
  by_cases h2 : k = 2
  · exact eq_of_le_of_card_ge hBP (by rw [hB,h2,hp]; decide)
  have hk0 : k ≠ 0 := by
    intro hz
    have hb : Nat.card B = 1 := by rw [hB,hz,pow_zero]
    exact hm (card_eq_one.mp hb)
  have hk1 : k = 1 := by omega
  have hcB : Nat.card B = 2 := by rw [hB,hk1,pow_one]
  have hXC : X ≤ centralizer (B : Set D) :=
    (normalizer_commutator_ge_right P X).trans (normalizer_le_centralizer_of_card_two B hcB)
  let a : X →* MulAut P := P.normalizerMonoidHom.comp (inclusion hn)
  have hi : (B.subgroupOf P).index ≤ 2 := by
    change B.relIndex P ≤ 2
    have hh := relIndex_mul_card_of_le hBP
    rw [hp,hcB] at hh
    omega
  have ha (x : X) : a x = 1 :=
    MulAut.eq_one_of_pPerfect_of_fixed_index_le_two a hX
      (IsPGroup.of_card (p := 2) (n := 2) hp) (B.subgroupOf P) hi (by
        intro x v hv
        apply Subtype.ext
        change (x : D) * (v : D) * (x : D)⁻¹ = (v : D)
        rw [←mem_centralizer_iff.mp (hXC x.property) v hv,mul_inv_cancel_right]) x
  apply (hm ?_).elim
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro x hx p hp
  have hh := congrArg (fun f : MulAut P => (f ⟨p,hp⟩ : D)) (ha ⟨x,hx⟩)
  change x*p*x⁻¹=p at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem plane_residual_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ⁅F.Vi 2,F.Li L 2⁆ = F.Vi 2 := by
  have hX : IsPPerfect 2 (F.Li L 2) := by
    rw [←plane_parabolic_residual h structural]
    exact isPPerfect_embedded_pResidual 2 (F.P L)
  apply four_plane_full_commutator _ _ (by simpa using F.card 2 (by decide)) hX
    ((F.Li_le L 2).trans inf_le_right)
  intro hz
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hn : F.Li L 2 ≤ normalizer (F.Vi 1 : Set G) :=
    (hc.trans (centralizer_le (F.monotone (by decide : 1 ≤ 2)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hh : F.Vi 2 ≤ F.Vi 1 := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_le le_rfl hn
  have hcard := card_le_of_le hh
  rw [F.card 2 (by decide),F.card 1 (by decide)] at hcard
  norm_num at hcard

theorem cubic_generated_span_residual_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    ⁅W.subgroupOf D,pResidual 2 D⁆ = W.subgroupOf D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let N := ⁅U,pResidual 2 D⁆
  let : N.Normal := inferInstanceAs (⁅U,pResidual 2 D⁆ : Subgroup D).Normal
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  have hXD : F.Li L 2 ≤ D := by
    rw [show D = F.P L ⊔ (Y ⊔ (T : Subgroup G)) from rfl,plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hPW : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_mono le_rfl hXD
  have hXR : F.Li L 2 ≤ (pResidual 2 D).map D.subtype := by
    rw [←plane_parabolic_residual h structural]
    exact embedded_pResidual_mono 2 le_sup_left
  have hPN : F.Vi 2 ≤ N.map D.subtype := by
    rw [show N = ⁅U,pResidual 2 D⁆ from rfl,map_commutator,
      show U.map D.subtype = W from map_subgroupOf_eq_of_le hWD,
      ←plane_residual_commutator h structural]
    exact commutator_mono hPW hXR
  have hDN : D ≤ normalizer (N.map D.subtype : Set G) := by
    have hh := (map_mono (f := D.subtype) (show (⊤ : Subgroup D) ≤ normalizer (N : Set D) from le_normalizer_of_normal)).trans
      (N.le_normalizer_map D.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  have hWN : W ≤ N.map D.subtype :=
    conjugateSpanBy_le ((F.monotone (by decide : 1 ≤ 2)).trans hPN) hDN
  apply le_antisymm (commutator_le_left _ _)
  intro w hw
  obtain ⟨n,hn,he⟩ := hWN hw
  exact (D.subtype_injective he) ▸ hn

private theorem cubic_vertex_residual_commutator
    {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 3)) :
    ⁅pResidual 2 D,(S : Subgroup D)⁆ = pResidual 2 D := by
  apply residual_commutator_of_index_three S (SymmetricThreeTwoCore.sylow_index_three e S)
    _ le_rfl (S : Subgroup D).le_normalizer
  intro hc
  have heq := le_antisymm hc (pCore_isPGroup.le_sylow_of_normal S)
  have hi := SymmetricThreeTwoCore.sylow_index_three e S
  rw [heq,SymmetricThreeTwoCore.core_index e] at hi
  omega

private theorem goldschmidt_residual_commutator
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) :
    ⁅pResidual 2 D,A ⊓ B⁆ = pResidual 2 D := by
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hlocal (J : Subgroup D) (hSJ : (S : Subgroup D) ≤ J)
      (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) :
      (pResidual 2 J).map J.subtype ≤ ⁅pResidual 2 D,A ⊓ B⁆ := by
    have hh := congrArg (map J.subtype) (cubic_vertex_residual_commutator (S.subtype hSJ) e)
    rw [map_commutator,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSJ] at hh
    rw [←hh,←hS]
    exact commutator_mono (map_pResidual_le 2 J.subtype) le_rfl
  apply le_antisymm (commutator_le_left _ _)
  apply ht.twoResidual_eq_sup.le.trans
  exact sup_le (hlocal A (hS.symm.le.trans inf_le_left) ht.quotient_left.some)
    (hlocal B (hS.symm.le.trans inf_le_right) ht.quotient_right.some)


open MarkedCubicRecognition in
private theorem heisenberg_marking_of_two_cubics
    {P : Type*} [Group P] [Finite P] (A B : Subgroup P)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hgen : A ⊔ B = ⊤)
    (hcard : Nat.card P = 27) (hpow : ∀ x : P, x ^ 3 = 1)
    (hclass : _root_.commutator P ≤ center P) :
    ∃ e : HeisenbergPrime 3 ≃* P,
      MarkedCubicRecognition.leftAxis.range.map e.toMonoidHom = A ∧
      MarkedCubicRecognition.rightAxis.range.map e.toMonoidHom = B := by
  obtain ⟨x, hxA, hx, hxgen⟩ := exists_cubic_generator A hA
  obtain ⟨y, hyB, hy, hygen⟩ := exists_cubic_generator B hB
  let c := ⁅y, x⁆
  have hc : c ∈ center P := hclass
    (Subgroup.commutator_mem_commutator (mem_top y) (mem_top x))
  have hs : y * x = c * x * y := by simp [c, commutatorElement_def, mul_assoc]
  let f := HeisenbergPrime.evaluateHom x y c hc hs hx hy (hpow c)
  have hfx : f leftGenerator = x := by
    simp [f, HeisenbergPrime.evaluateHom, leftGenerator, ZMod.val_one]
  have hfy : f rightGenerator = y := by
    simp [f, HeisenbergPrime.evaluateHom, rightGenerator, ZMod.val_one]
  have hfA : A ≤ f.range := by
    rw [← hxgen]
    exact zpowers_le.mpr ⟨leftGenerator, hfx⟩
  have hfB : B ≤ f.range := by
    rw [← hygen]
    exact zpowers_le.mpr ⟨rightGenerator, hfy⟩
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp
    (top_unique (hgen ▸ sup_le hfA hfB))
  have hbij : Function.Bijective f := hsurj.bijective_of_nat_card_le
    (by rw [HeisenbergPrime.card, hcard]; decide)
  let e := MulEquiv.ofBijective f hbij
  have heA : leftAxis.range.map e.toMonoidHom = A := by
    rw [← MonoidHom.range_comp]
    have heq : e.toMonoidHom.comp leftAxis = cyclicHom x hx := by
      ext z
      simp [e, f, HeisenbergPrime.evaluateHom, leftAxis, cyclicHom]
    rw [heq, cyclicHom_range (by decide), hxgen]
  have heB : rightAxis.range.map e.toMonoidHom = B := by
    rw [← MonoidHom.range_comp]
    have heq : e.toMonoidHom.comp rightAxis = cyclicHom y hy := by
      ext z
      simp [e, f, HeisenbergPrime.evaluateHom, rightAxis, cyclicHom]
    rw [heq, cyclicHom_range (by decide), hygen]
  exact ⟨e,heA,heB⟩
private theorem commutative_of_marking {A B : Type*} [Group A] [Group B]
    [IsMulCommutative B] (e : A ≃* B) : IsMulCommutative A :=
  IsMulCommutative.of_comm fun x y => e.injective
    ((map_mul e x y).trans ((mul_comm (e x) (e y)).trans (map_mul e y x).symm))

theorem cubic_generated_cyclic_action_extraspecial_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let R := pResidual 2 (D ⧸ centralizer (W.subgroupOf D : Set D))
    IsExtraspecial 3 R ∧ Nat.card R = 27 ∧ Monoid.exponent R = 3 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  let R := pResidual 2 (D ⧸ C)
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hf := NormalElementaryQuotient.representation_injective U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hcore := cubic_generated_action_three_core_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT hout he
  have hR : IsPGroup 3 R := by
    change IsPGroup 3 (pResidual 2 (D ⧸ C))
    rw [hcore.1]
    exact pCore_isPGroup
  have hnc : ¬ IsMulCommutative R := by
    change ¬ IsMulCommutative (pResidual 2 (D ⧸ C))
    rw [hcore.1]
    exact hcore.2.2.1
  have hne : R ≠ ⊥ := by
    intro hz
    apply hnc
    rw [hz]
    infer_instance
  have hodd : Nat.Coprime 2 (Nat.card R) := by
    obtain ⟨n,hn⟩ := hR.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  obtain ⟨t,ht,htS,hcod,hgen⟩ := cubic_generated_cyclic_action_involution_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT hout he
  obtain ⟨hi,htriple,_⟩ := cubic_generated_action_triple_of_moving_plane
    h hab structural previous Y hYH hm hYp hYT he
  have hcomm : ⁅R,zpowers t⁆ = R := by
    have hh := goldschmidt_residual_commutator htriple
    rw [hi,←htS] at hh
    exact hh
  have hgenR : R ⊔ zpowers t = ⊤ := by
    change pResidual 2 (D ⧸ C) ⊔ zpowers t = ⊤
    rw [hcore.1]
    exact hgen
  have hfull : subspaceCommutator ρ ⊤ R = ⊤ := by
    change subspaceCommutator ρ ⊤ (pResidual 2 (D ⧸ C)) = ⊤
    rw [←map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective C),
      ←NormalElementaryQuotient.commutatorSpace_eq U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)]
    ext v
    change (v.toMul : D) ∈ ⁅U,pResidual 2 D⁆ ↔ True
    rw [cubic_generated_span_residual_commutator h structural Y]
    exact iff_true_intro v.toMul.property
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative (Additive U)) := BinaryGroupAction.elementary
  let : FaithfulSMul (D ⧸ C) (Multiplicative (Additive U)) := BinaryGroupAction.faithful ρ hf
  have hfgroup : fixingSubgroup (D ⧸ C) (Set.univ : Set (Multiplicative (Additive U))) = ⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α := Multiplicative (Additive U))
    intro v
    simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := D ⧸ C)).mp hg v trivial)
  have hfullgroup : commutatorAction R (Multiplicative (Additive U)) = ⊤ := by
    rw [BinaryGroupAction.commutator_eq,hfull]
    exact OrderIso.map_top _
  have hindex : Nat.card (Multiplicative (Additive U)) ≤
      4 * Nat.card (FixedPoints.subgroup (zpowers t) (Multiplicative (Additive U))) := by
    rw [Nat.card_congr Multiplicative.toAdd, BinaryGroupAction.fixedPoints_eq,
      BinaryGroupAction.card_submoduleEquivSubgroup,
      Module.natCard_eq_pow_finrank (K := ZMod 2),
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      ←fixedCodim_add_finrank ρ (zpowers t),pow_add]
    change fixedCodim ρ (zpowers t) ≤ 2 at hcod
    have hh : (2 : ℕ)^fixedCodim ρ (zpowers t) ≤ 4 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcod
    norm_num [Module.finrank_self]
    have hfix : (2 : ℕ) ^ Module.finrank (ZMod 2)
        (fixedSpace ρ (zpowers t)) = Nat.card ↥(fixedSpace ρ (zpowers t)) := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := fixedSpace ρ (zpowers t))).symm
    rw [hfix]
    exact Nat.mul_le_mul_right _ hh
  have hti : IsInvolution t := ⟨fun he => by simp [he] at ht,by simpa only [ht] using pow_orderOf_eq_one t⟩
  rcases ChapterD.Section02.smallSupportClassification R hne 3 hR hodd t hti hgenR hcomm
    hfullgroup hindex hfgroup with h3 | h5 | h9 | hex
  · exact False.elim (hnc (commutative_of_marking h3.kernel_equiv.some))
  · exact False.elim (hnc (commutative_of_marking h5.kernel_equiv.some))
  · exact False.elim (hnc (commutative_of_marking h9.kernel_equiv.some))
  · exact ⟨hex.kernel_extraspecial,hex.card_kernel,hex.exponent_kernel⟩

theorem cubic_moving_plane_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    False := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  let R := pResidual 2 (D ⧸ C)
  let X₀ := ((F.Li L 2).subgroupOf D).map q
  let Y₀ := (Y.subgroupOf D).map q
  obtain ⟨hex,hcard,hexp⟩ := cubic_generated_cyclic_action_extraspecial_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT hout he
  let : IsExtraspecial 3 R := hex
  have hcore := cubic_generated_action_three_core_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT hout he
  have hR : IsPGroup 3 R := by
    change IsPGroup 3 (pResidual 2 (D ⧸ C))
    rw [hcore.1]
    exact pCore_isPGroup
  have hjoin : X₀ ⊔ Y₀ = R := hcore.2.1.trans hcore.1.symm
  have hXR : X₀ ≤ R := le_sup_left.trans hjoin.le
  have hYR : Y₀ ≤ R := le_sup_right.trans hjoin.le
  obtain ⟨_,ht,_⟩ := cubic_generated_action_triple_of_moving_plane
    h hab structural previous Y hYH hm hYp hYT he
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have hXcard : Nat.card X₀ = 3 := by
    have hh := ChapterF.Noncyclic.local_residual_card_three ht hR
    rw [←map_embedded_pResidual,hr.1] at hh
    exact hh
  have hYcard : Nat.card Y₀ = 3 := by
    have hh := ChapterF.Noncyclic.local_residual_card_three ht.symm hR
    rw [←map_embedded_pResidual,hr.2] at hh
    exact hh
  obtain ⟨e,heX,heY⟩ := heisenberg_marking_of_two_cubics
    (X₀.subgroupOf R) (Y₀.subgroupOf R)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hXR).toEquiv]; exact hXcard)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hYR).toEquiv]; exact hYcard)
    (by rw [←subgroupOf_sup hXR hYR,hjoin,subgroupOf_self]) hcard
    (fun r => by rw [←hexp]; exact Monoid.pow_exponent_eq_one r)
    (IsExtraspecial.commutator_eq_center (p := 3)).le
  have hX : MarkedCubicRecognition.leftAxis.range.map (R.subtype.comp e.toMonoidHom) = X₀ := by
    rw [←map_map,heX,map_subgroupOf_eq_of_le hXR]
  have hY : MarkedCubicRecognition.rightAxis.range.map (R.subtype.comp e.toMonoidHom) = Y₀ := by
    rw [←map_map,heY,map_subgroupOf_eq_of_le hYR]
  let β := NormalElementaryQuotient.conjugationAut U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hβ : β.comp q = MulAut.conjNormal := by
    ext d u
    simpa [β] using congrArg D.subtype
      (NormalElementaryQuotient.conjugationAut_apply U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) d u)
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hPD : F.Vi 2 ≤ D := (F.le_seed 2).trans (h.chosen.le_sylow.trans hTD)
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hPW : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_mono le_rfl hXD
  have hXP : (F.Li L 2).subgroupOf D ≤ normalizer ((F.Vi 2).subgroupOf D : Set D) := by
    intro x hx
    apply le_normalizer_comap D.subtype
    exact (F.Li_le L 2 hx).2
  have hYZ : Y.subgroupOf D ≤ centralizer ((F.Vi 1).subgroupOf D : Set D) := by
    intro y hy
    apply mem_centralizer_iff.mpr
    intro z hz
    apply Subtype.ext
    exact mem_centralizer_iff.mp
      ((hYH.trans (normalizer_le_centralizer_of_card_two _
        (by simpa using F.card 1 (by decide)))) hy) z hz
  have hplane : conjugateSpanBy ((F.Vi 1).subgroupOf D) ((F.Li L 2).subgroupOf D) =
      (F.Vi 2).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hZD,map_subgroupOf_eq_of_le hXD,
      map_subgroupOf_eq_of_le hPD,plane_eq_point_residual_span h structural]
  have hspan : conjugateSpanBy ((F.Vi 1).subgroupOf D) ⊤ = U := by
    apply map_injective D.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hZD,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZD)]
  have hc := MarkedCubicRecognition.center_kernel_of_point_plane U
    ((F.Vi 1).subgroupOf D) ((F.Vi 2).subgroupOf D) ((F.Li L 2).subgroupOf D)
    (Y.subgroupOf D) q (QuotientGroup.mk'_surjective _) β hβ R e hX hY
    (subgroupOf_mono D (F.monotone (by decide : 1 ≤ 2))) (subgroupOf_mono D hPW)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv]; simpa using F.card 1 (by decide))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv]; simpa using F.card 2 (by decide))
    hXP hYZ hplane hspan
  have hkβ : β.ker = ⊥ := by
    apply bot_unique
    intro r hr
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective C r
    have hd : d ∈ C := by
      intro u hu
      have hh := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : D)) hr
      change (β (q d) ⟨u,hu⟩ : D) = u at hh
      rw [NormalElementaryQuotient.conjugationAut_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact (QuotientGroup.eq_one_iff d).mpr hd
  have hz : center R = ⊥ := by
    apply bot_unique
    intro r hr
    have hh := hc (mem_map_of_mem R.subtype hr)
    rw [hkβ] at hh
    exact Subtype.ext (mem_bot.mp hh)
  have hcR := IsExtraspecial.center_order_p 3 R
  rw [hz] at hcR
  simp at hcR

/-! The preceding contradiction is applied to the literal failed quotient
lift. This is the source-level cyclic-overlap consumer: its escape witness is
constructed from the original intertwining map, so the actor and quotient are
unchanged. -/
theorem original_quotient_plane_lifting_cyclic_overlap_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) :
    False := by
  have hout := quotient_plane_moving_actor_escapes_at h (structural G T)
    c p hp Y hYH hYp hfix hm
  exact cubic_moving_plane_impossible h hab structural previous faithful Y hYH hm hYp
    hYT hout he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
