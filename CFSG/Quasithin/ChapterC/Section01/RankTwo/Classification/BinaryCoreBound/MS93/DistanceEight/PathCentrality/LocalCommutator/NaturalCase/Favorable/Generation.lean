module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable.Transport
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Generating the favorable local pairing in MS93 (4.4.1)

The literal image of W is the normal closure of the image of Z_a. Its natural
coordinates and the original noncentral displacement permit selection of an
element with both properties. The neighboring kernel Q_a centralizes Z_a,
whereas its image normally generates the local residual. This transfers a
centralizer bound from [W,Ltilde_c] to W.

After the genuine (1.7)(i) application, that transfer and the three-subgroups
lemma show that the entire fixed part W intersect B_c centralizes Q_c modulo
D_c. Only then do we prove the seed's origin and generation bounds. Natural
coordinates also give actual fixed points on WB_c/B_c for the selected flag.

The normalization calculation adapts the generator argument in
Reduction/SectionThree/NormalizationTransfer.lean to W, retaining its actual
neighboring kernel and relative normal closure.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), pp.890--891, applying (1.7)(i) as on p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
open RankOnePairing Escape.PairingControl.FirstPairing
open Orientation.QuotientApplication NaturalGeneration
private theorem commutator_normalized_of_triple_eq_bot {G : Type*} [Group G]
    (A V Y L : Subgroup G) [Y.Normal] (hAV : A ≤ V)
    (htriple : ⁅⁅V,L⁆,Y⁆ = ⊥) : L ≤ normalizer (⁅A,Y⁆ : Subgroup G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a, ha, y, hy, rfl⟩
  have hy' : l * y * l⁻¹ ∈ Y := (inferInstance : Y.Normal).conj_mem y hy l
  have hc : ⁅l,a⁆ ∈ ⁅V,L⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hl (hAV ha)
  have hcy : Commute ⁅l,a⁆ (l * y * l⁻¹) :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _ hy').symm
  have hck : Commute ⁅l,a⁆ ⁅a,l * y * l⁻¹⁆ :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _
      (commutator_le_right A Y (commutator_mem_commutator ha hy'))).symm
  rw [conjugate_commutatorElement, show l * a * l⁻¹ = ⁅l,a⁆ * a by
    simp [commutatorElement_def, mul_assoc]]
  rw [commutatorElement_mul_left_eq_conj_mul, hcy.commutator_eq,
    hck.eq, mul_inv_cancel_right, mul_one]
  exact commutator_mem_commutator ha hy'

private theorem normalizes_commutator {G : Type*} [Group G] (B A Y : Subgroup G)
    (hBA : B ≤ normalizer A) (hBY : B ≤ normalizer Y) :
    B ≤ normalizer (⁅A,Y⁆ : Subgroup G) := by
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hBA hb),
    mem_normalizer_iff_map_conj_eq.mp (hBY hb)]


/-- The local generating subgroup transfers centralization from the moving part. -/
private theorem transfer_from_moving {G : Type*} [Group G]
    (Q E H A J Y : Subgroup G) [Q.Normal] [Y.Normal]
    (hcover : Q ⊔ E = ⊤) (hHQ : H ≤ Q) (hYQ : Y ≤ Q)
    (hHA : H = generated A) (hQA : Q ≤ normalizer A)
    (hAJ : ⁅A,J⁆ = ⊥) (hJE : E ≤ generated J)
    (hfaithful : Q ⊓ centralizer (E : Set G) = ⊥)
    (ht : ⁅⁅H,E⁆,Y⁆ = ⊥) : ⁅H,Y⁆ = ⊥ := by
  have hAH : A ≤ H := hHA ▸ le_normalClosure
  let K := ⁅A,Y⁆
  have hKA : K ≤ A := le_normalizer_iff_commutator_le_left.mp (hYQ.trans hQA)
  have hEK : E ≤ normalizer K :=
    commutator_normalized_of_triple_eq_bot A H Y E hAH ht
  have hQK : Q ≤ normalizer K := normalizes_commutator Q A Y hQA le_normalizer_of_normal
  let : K.Normal := normalizer_eq_top_iff.mp (top_unique
    (hcover ▸ sup_le hQK hEK))
  have hKJ : ⁅K,J⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hKA le_rfl).trans hAJ.le)
  have hKE : ⁅K,E⁆ = ⊥ := le_bot_iff.mp ((commutator_mono le_rfl hJE).trans
    (commutator_normalClosure_le_of_normal K J ⊥ hKJ.le))
  have hK : K = ⊥ := le_bot_iff.mp (hfaithful ▸ le_inf (hKA.trans (hAH.trans hHQ))
    (commutator_eq_bot_iff_le_centralizer.mp hKE))
  rw [hHA]
  exact le_bot_iff.mp (generated_commutator_le A Y ⊥ hK.le)

/-- Irreducibility gives generation modulo the coordinate kernel. -/
private theorem natural_generation {G : Type*} [Group G] {π : G →* SL}
    {H N : Subgroup G} [H.Normal] [N.Normal]
    (n : NaturalFactor π ⊤ H N) (hπ : Function.Surjective π)
    (hNH : N ≤ H) (X : Subgroup G) (hXH : X ≤ H)
    (x : G) (hx : x ∈ X) (hne : n.coordinates ⟨x,hXH hx⟩ ≠ 1) :
    H = generated X ⊔ N := by
  let J := generated X ⊔ N
  have hJH : J ≤ H := sup_le (generated_le X H hXH) hNH
  rcases Escape.Initial.Natural.naturalFactor_dichotomy n hπ J le_sup_right hJH with h | h
  · have hxn : x ∈ N := h ▸ (show x ∈ J from (show generated X ≤ J from le_sup_left) (le_normalClosure hx))
    have hk : (⟨x,hXH hx⟩ : H) ∈ n.coordinates.ker := by rw [n.kernel]; exact hxn
    exact (hne hk).elim
  · exact h.symm

/-- The fixed summand is fixed modulo the seed, so moving elements lie in its closure. -/
private theorem moving_le_generated {G : Type*} [Group G]
    {π : G →* SL} {H N Z E : Subgroup G} [H.Normal] [N.Normal]
    (n : NaturalFactor π ⊤ H N) (hπ : Function.Surjective π)
    (hNH : N ≤ H)
    (hNZ : ⁅N,E⁆ ≤ Z) (X : Subgroup G) (hXH : X ≤ H) (hZX : Z ≤ X)
    (x : G) (hx : x ∈ X) (hne : n.coordinates ⟨x,hXH hx⟩ ≠ 1) :
    ⁅H,E⁆ ≤ generated X := by
  have heq := natural_generation n hπ hNH X hXH x hx hne
  have hNE : ⁅N,E⁆ ≤ generated X := hNZ.trans (hZX.trans le_normalClosure)
  have hGE : ⁅generated X,E⁆ ≤ generated X := commutator_le_left _ _
  rw [heq]
  have hpre : generated X ⊔ N ≤ commutatorPreimage ⊤ E (generated X) :=
    sup_le (le_commutatorPreimage le_top hGE) (le_commutatorPreimage le_top hNE)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

omit [Finite M] in
/-- The quotient of the literal orbit span is the ambient normal closure. -/
theorem span_eq_generated (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) :
    quotientImage c (localZSpan R a c) = generated (quotientImage c (Z R a)) := by
  let S := stabilizer R c
  have hAS : Z R a ≤ S := (Z_le_localZSpan R a c).trans
    ((localZSpan_le_Q R hc hd.le hb).trans (fun _ hx => hx.1))
  let J := (generated (quotientImage c (Z R a))).comap (quotientMap c)
  let := quotientImage_normal c (localZSpan R a c) (localZSpan_normalized R a c)
  apply le_antisymm
  · have hW : localZSpan R a c ≤ J.map S.subtype := by
      rw [span_eq_conjugates, NormalizerTransfer.conjugatesIn]
      apply iSup_le
      intro g
      rintro _ ⟨z,hz,rfl⟩
      let zS : S := ⟨z,hAS hz⟩
      have hzJ : zS ∈ J := le_normalClosure (mem_map_of_mem (quotientMap c) hz)
      have hj : (g⁻¹ * zS * g : S) ∈ J := by
        simpa only [inv_inv] using (inferInstance : J.Normal).conj_mem zS hzJ g⁻¹
      refine ⟨g⁻¹ * zS * g, hj, ?_⟩
      simp [zS]
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨j,hj,he⟩ := hW hx
    have hje : j = x := Subtype.ext he
    subst j
    exact hj
  · exact generated_le _ _ (map_mono (comap_mono (Z_le_localZSpan R a c)))

private theorem residual_le_generated {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (J : Subgroup G) (hJ : ¬ J ≤ π.ker) :
    pResidual 2 G ≤ generated J := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let N := generated J
  have hn : (N.map π).Normal := (inferInstance : N.Normal).map π hπ
  have hm : N.map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (hJ ((le_normalClosure (H := J)).trans ((Subgroup.map_eq_bot_iff _).mp h))).elim
    · exact h
  have hsup : N ⊔ π.ker = ⊤ := by
    have hh := congrArg (fun A => A.comap π) hm
    simpa only [comap_map_eq, comap_top] using hh
  exact sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N π.ker hp hsup⟩

/-- The neighboring kernel supplies the source normalization transfer for W. -/
theorem span_transfer (source : LocalSource L R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (flag : SL)
    (Y : Subgroup (LocalQuotient c)) [Y.Normal]
    (hY : Y ≤ quotientImage c (Q R c))
    (ht : ⁅⁅quotientImage c (localZSpan R a c),component f.projection flag⁆,Y⁆ = ⊥) :
    ⁅quotientImage c (localZSpan R a c),Y⁆ = ⊥ := by
  let := quotientImage_normal c (Q R c) (Q_normalized R c)
  let S := stabilizer R c
  have hQS : Q R c ≤ S := fun _ hx => hx.1
  have hAS : Z R a ≤ S := (Z_le_localZSpan R a c).trans
    ((localZSpan_le_Q R hc hd.le hb).trans hQS)
  have hJS : Q R a ≤ S := Q_le_stabilizer_of_dist_le_two a c ha hc hd.le
  have hQA : Q R c ≤ normalizer (Z R a) :=
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm]; exact hd.le)).trans
      (Z_normalized R a)
  have hker : f.projection.ker = quotientImage c (Q R c) := quotientProjection_kernel c _ _
  have hnot : ¬ quotientImage c (Q R a) ≤ f.projection.ker := by
    intro h
    rw [hker, quotientImage_le_iff c _ _ hJS hQS,
      sup_eq_left.mpr (show fixedCore R c ≤ Q R c from inf_le_left)] at h
    let := finite_stabilizer R c
    let : Finite (Q R c) := Finite.of_injective (inclusion hQS) (inclusion_injective hQS)
    have he : Q R a = Q R c := eq_of_le_of_card_ge h (by
      rw [source.Q_card a ha, source.Q_card c hc])
    exact hn (by rw [← he, Z_centralizes_Q R a ha]; exact bot_le)
  have hcover : quotientImage c (Q R c) ⊔ component f.projection flag = ⊤ := by
    rw [← hker, sup_comm, ← comap_map_eq, component_map f.projection
      (quotientProjection_surjective c _ f.sectionData.module_section.projection_surjective _) flag,
      comap_top]
  apply transfer_from_moving (quotientImage c (Q R c)) (component f.projection flag)
    (quotientImage c (localZSpan R a c)) (quotientImage c (Z R a))
    (quotientImage c (Q R a)) Y hcover
    (map_mono (comap_mono (localZSpan_le_Q R hc hd.le hb))) hY
    (span_eq_generated hc hd hb)
  · exact (map_mono ((comap_mono hQA).trans (le_normalizer_comap S.subtype))).trans
      (le_normalizer_map (quotientMap c))
  · rw [← quotientImage_commutator c _ _ hAS hJS, Z_centralizes_Q R a ha]
    simp [quotientImage]
  · rw [component_eq_residual source hc]
    exact residual_le_generated f.projection
      (quotientProjection_surjective c _ f.sectionData.module_section.projection_surjective _)
      (quotientProjection_kernel_isPGroup source c hc _ _) _ hnot
  · rw [← hker]
    exact kernel_fixed_eq_bot source hc f flag
  · exact ht

private theorem exists_outside_two {G : Type*} [Group G] (A N C : Subgroup G)
    (hN : ¬ A ≤ N) (hC : ¬ A ≤ C) : ∃ x ∈ A, x ∉ N ∧ x ∉ C := by
  classical
  obtain ⟨u,hu,huN⟩ := SetLike.not_le_iff_exists.mp hN
  obtain ⟨v,hv,hvC⟩ := SetLike.not_le_iff_exists.mp hC
  by_cases huC : u ∈ C
  · by_cases hvN : v ∈ N
    · refine ⟨u*v,A.mul_mem hu hv,?_,?_⟩
      · intro h
        exact huN (by simpa only [mul_inv_cancel_right] using N.mul_mem h (N.inv_mem hvN))
      · intro h
        exact hvC (by simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem huC) h)
    · exact ⟨v,hv,hvN,hvC⟩
  · exact ⟨u,hu,huN,huC⟩

/-- Choose an actual generator having both nonzero natural coordinate and displacement. -/
theorem exists_selected (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c) (f : FrameAt a c) :
    ∃ x ∈ quotientImage c (Z R a), x ∉ fixedSpan geometry a c ∧
      ⁅zpowers x,quotientImage c (Q R c)⁆ ≠ ⊥ := by
  let N := fixedSpan geometry a c
  let A := quotientImage c (Z R a)
  let H := quotientImage c (localZSpan R a c)
  let Qc := quotientImage c (Q R c)
  let := fixedSpan_normal (geometry := geometry) (a := a) (c := c)
  have hAN : ¬ A ≤ N := by
    intro h
    have hHN : H ≤ N := (span_eq_generated hc hd hb).le.trans (generated_le A N h)
    let n := quotientNaturalW source hc hd hb f
    obtain ⟨v,hv⟩ := n.surjective (Multiplicative.ofAdd ![1,0,0])
    have hk : v ∈ n.coordinates.ker := by rw [n.kernel]; exact hHN v.property
    have hh : Multiplicative.ofAdd (![1,0,0] : Fin 3 → ZMod 2) = 1 := hv.symm.trans hk
    exact (by decide : Multiplicative.ofAdd (![1,0,0] : Fin 3 → ZMod 2) ≠ 1) hh
  have hAC : ¬ A ≤ centralizer (Qc : Set (LocalQuotient c)) := by
    intro h
    have hzero := commutator_eq_bot_iff_le_centralizer.mpr h
    have hQS : Q R c ≤ stabilizer R c := fun _ hx => hx.1
    have hAS := (Z_le_localZSpan R a c).trans
      ((localZSpan_le_Q R hc hd.le hb).trans hQS)
    exact hn ((quotient_commutator_eq_bot_iff c _ _ hAS hQS).mp hzero)
  obtain ⟨x,hx,hxN,hxC⟩ := exists_outside_two A N _ hAN hAC
  exact ⟨x,hx,hxN,fun h => hxC (commutator_eq_bot_iff_le_centralizer.mp h (mem_zpowers x))⟩

/-- After (1.7)(i), the entire fixed part of W centralizes the second pairing group. -/
theorem fixedSpan_centralizes_of_pairing (source : LocalSource L R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c) (f : FrameAt a c)
    (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool)
    (X : Subgroup (LocalQuotient c))
    (d : let := quotientImage_normal c (Z R c) (Z_normalized R c)
         let := quotientImage_normal c (Q R c) (Q_normalized R c)
         SourceData (f.extension source hc flag hflag) i
           (quotientImage c (Z R c)) (quotientImage c (Q R c)) X)
    (hf : quotientImage c (Z R c) ⊓ centralizer
      (localResidual (localParabolic (f.extension source hc flag hflag) i) : Set (LocalQuotient c)) ≠ ⊥)
    (hXH : X ≤ quotientImage c (localZSpan R a c))
    (x : LocalQuotient c) (hx : x ∈ X) (hxN : x ∉ fixedSpan geometry a c) :
    fixedSpan geometry a c ≤ centralizer (quotientImage c (Q R c) : Set (LocalQuotient c)) := by
  let := quotientImage_normal c (Z R c) (Z_normalized R c)
  let := quotientImage_normal c (Q R c) (Q_normalized R c)
  let := quotientImage_normal c (localZSpan R a c) (localZSpan_normalized R a c)
  let := fixedSpan_normal (geometry := geometry) (a := a) (c := c)
  let E := component f.projection flag
  let : E.Normal := by
    dsimp [E]
    rw [component_eq_residual source hc]
    infer_instance
  let Qc := quotientImage c (Q R c)
  let H := quotientImage c (localZSpan R a c)
  let Zc := quotientImage c (Z R c)
  let N := fixedSpan geometry a c
  let n := quotientNaturalW source hc hd hb f
  have hne : n.coordinates ⟨x,hXH hx⟩ ≠ 1 := by
    intro h
    have hk : (⟨x,hXH hx⟩ : H) ∈ n.coordinates.ker := h
    rw [n.kernel] at hk
    exact hxN hk
  have hNG : ⁅H,E⁆ ≤ generated X := moving_le_generated n
    (quotientProjection_surjective c _ f.sectionData.module_section.projection_surjective _)
    fixedSpan_le (fixedSpan_commutator source hc hd f flag) X hXH d.z_le x hx hne
  have ht : ⁅⁅Qc,E⁆,generated X⁆ = ⊥ := (theorem_1_7_i d hf).2.1
  have hHZ : ⁅H,⁅Qc,E⁆⁆ = ⊥ := span_transfer source ha hc hd hb hn f flag _
    (commutator_le_left _ _) (by
      rw [commutator_comm]
      exact le_bot_iff.mp ((commutator_mono le_rfl hNG).trans ht.le))
  have hNQE : ⁅⁅N,Qc⁆,E⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply commutator_commutator_le_of_rotate
    · rw [commutator_comm]
      exact (commutator_mono fixedSpan_le le_rfl).trans hHZ.le
    · rw [commutator_comm E N]
      exact (commutator_mono (fixedSpan_commutator source hc hd f flag) le_rfl).trans
        (commutator_eq_bot_iff_le_centralizer.mpr (by
          change quotientImage c (Z R c) ≤ centralizer (quotientImage c (Q R c) : Set _)
          rw [← quotientProjection_kernel c f.sectionData.projection
            f.sectionData.module_section.projection_kernel]
          exact Z_centralizes_kernel (geometry := geometry) hc f)).le
  have hzero : ⁅N,Qc⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hfaithful : Qc ⊓ centralizer (E : Set (LocalQuotient c)) = ⊥ := by
      dsimp [Qc]
      rw [← quotientProjection_kernel c f.sectionData.projection
        f.sectionData.module_section.projection_kernel]
      exact kernel_fixed_eq_bot source hc f flag
    rw [← hfaithful]
    exact le_inf (commutator_le_right _ _) (commutator_eq_bot_iff_le_centralizer.mp hNQE)
  exact commutator_eq_bot_iff_le_centralizer.mp hzero

private theorem localGenerated_le_sup {G : Type*} [Group G] (P A N : Subgroup G)
    [N.Normal] (h : ⁅A,P⁆ ≤ N) : localGenerated P A ≤ A ⊔ N := by
  let q := QuotientGroup.mk' N
  have hc : P.map q ≤ centralizer (A.map q : Set (G ⧸ N)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [commutator_comm, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h
  have hp := ((map_le_iff_le_comap.mp (hc.trans (Subgroup.centralizer_le_normalizer _))).trans
    (le_normalizer_comap q))
  rw [comap_map_eq, QuotientGroup.ker_mk'] at hp
  exact Incidence.localGenerated_le_of_normalizes P A (A ⊔ N) hp le_sup_left

/-- Fixed-part centralization gives both the origin and the generation fields. -/
theorem seed_bounds (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool)
    (x : LocalQuotient c) (hx : x ∈ quotientImage c (Z R a))
    (hne : (quotientNaturalW source hc hd hb f).coordinates
      ⟨x,map_mono (comap_mono (Z_le_localZSpan R a c)) hx⟩ ≠ 1)
    (hfix : ∀ g ∈ modelParabolic flag i,
      ((quotientNaturalW source hc hd hb f).marking g).val.mulVec
        ((quotientNaturalW source hc hd hb f).coordinates
          ⟨x,map_mono (comap_mono (Z_le_localZSpan R a c)) hx⟩).toAdd =
        ((quotientNaturalW source hc hd hb f).coordinates
          ⟨x,map_mono (comap_mono (Z_le_localZSpan R a c)) hx⟩).toAdd)
    (hNC : fixedSpan geometry a c ≤
      centralizer (quotientImage c (Q R c) : Set (LocalQuotient c))) :
    seed f flag i x ≤ quotientImage c (Z R a) ⊔
      centralizer (quotientImage c (Q R c) : Set (LocalQuotient c)) ∧
    quotientImage c (localZSpan R a c) ≤ generated (seed f flag i x) ⊔
      centralizer (quotientImage c (Q R c) : Set (LocalQuotient c)) := by
  let := quotientImage_normal c (Z R c) (Z_normalized R c)
  let := quotientImage_normal c (localZSpan R a c) (localZSpan_normalized R a c)
  let := fixedSpan_normal (geometry := geometry) (a := a) (c := c)
  have hxW := map_mono (comap_mono (Z_le_localZSpan R a c)) hx
  let d := naturalSeedData source hc hd hb f flag hflag i x hxW hne hfix
  constructor
  · apply sup_le
    · exact (Z_le_fixedSpan hc hd hb).trans (hNC.trans le_sup_right)
    · exact (localGenerated_le_sup _ _ _ (Seed.cyclic_fixed d)).trans
        (sup_le_sup (zpowers_le.mpr hx) hNC)
  · have hh := natural_generation d.natural d.projection_surjective d.fixed_le_group
      d.seed (Seed.le_group d) x (Seed.cyclic_le d (mem_zpowers x)) hne
    exact hh.le.trans (sup_le_sup_left hNC _)

/-- A fixed nonzero natural coordinate is a genuine fixed point in WB_c/B_c. -/
theorem barSpan_fixed_ne_bot (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (flag : SL) (i : Bool) (v : Fin 3 → ZMod 2) (hv : v ≠ 0)
    (hfix : ∀ g ∈ modelParabolic flag i,
      (f.sectionData.module_section.natural.marking g).val.mulVec v = v) :
    Opposite.barSpan geometry a c ⊓ centralizer
      ((parabolic f.sectionData.projection flag i).map (Opposite.fixedQuotientMap geometry c) :
        Set (Opposite.FixedQuotient geometry c)) ≠ ⊥ := by
  let := Opposite.fixed_normal (geometry := geometry) c
  let n := Opposite.spanNatural source hc hd hb f
  obtain ⟨x,hx⟩ := n.surjective (Multiplicative.ofAdd v)
  let q := Opposite.fixedQuotientMap geometry c
  have hqx : q (x : stabilizer R c) ≠ 1 := by
    intro h
    have hB : (x : stabilizer R c) ∈
        (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c) :=
      (QuotientGroup.eq_one_iff _).mp h
    have hker : x ∈ n.coordinates.ker := by rw [n.kernel]; exact hB
    exact hv (congrArg Multiplicative.toAdd (hx.symm.trans hker))
  have hcentral : q (x : stabilizer R c) ∈ centralizer
      ((parabolic f.sectionData.projection flag i).map q : Set (Opposite.FixedQuotient geometry c)) := by
    rintro _ ⟨g,hg,rfl⟩
    let y : (localZSpan R a c).subgroupOf (stabilizer R c) :=
      ⟨g * (x : stabilizer R c) * g⁻¹,
        (mem_normalizer_iff.mp (n.normalized (mem_top g)) _).mp x.property⟩
    have he : n.coordinates y = n.coordinates x := by
      apply Multiplicative.toAdd.injective
      rw [n.action g (mem_top _) x y rfl, hx]
      exact hfix _ hg
    have hker : y*x⁻¹ ∈ n.coordinates.ker := by
      change n.coordinates (y*x⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [n.kernel] at hker
    have hcomm : q ⁅g,(x : stabilizer R c)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hker
    rw [map_commutatorElement] at hcomm
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
  intro hbot
  exact hqx (mem_bot.mp (hbot ▸ (show q (x : stabilizer R c) ∈
    Opposite.barSpan geometry a c ⊓ centralizer
      ((parabolic f.sectionData.projection flag i).map q : Set (Opposite.FixedQuotient geometry c))
    from ⟨mem_map_of_mem q x.property,hcentral⟩)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
