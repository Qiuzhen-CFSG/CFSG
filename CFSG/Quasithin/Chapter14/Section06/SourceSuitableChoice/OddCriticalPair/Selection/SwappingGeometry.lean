module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Fusion.Lifts

public import Theory.GroupAction.BinaryWreathSwappingObstruction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.CoreRank

/-!
# Excluding plane interchange using the actual abelian span

A swapping involution has a point-stabilizer commutator which moves its
own displacement space. The actual two-core moves every noncentral point
of the orthogonal moved group, so quotient stabilizers lift to centralizers
of the same point. Inside a conjugate of the abelian Mc-span, these
commutators must centralize the endpoint module, giving the contradiction.

Only the fitting preimage of H is used here; no conclusion of 14.6.14--16
is needed. The selected-endpoint application supplies the point's membership
in the moved group in Selection.SwappingSource.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open Stellmacher OddNormalizer SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The actual odd residual lies above the fitting subgroup of the original quotient. -/
theorem residual_le_local_fitting {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) :
    residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H := by
  have hprime : p.Prime := by rcases d.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hp : IsPGroup p (pResidual 2 (H ⧸ pCore 2 H)) := IsPGroup.of_card d.residual_card
  have hr : pResidual 2 (H ⧸ pCore 2 H) ≤ pCore p (H ⧸ pCore 2 H) :=
    le_sSup ⟨inferInstance,hp⟩
  apply map_mono
  apply map_le_iff_le_comap.mp
  rw [map_pResidual_quotient]
  exact hr.trans ((pCore_le_fitting _ p).trans (fitting_le_generalizedFitting _))

attribute [local instance] orthogonalAction FourGroupMatrixCoordinates.naturalAction
/-- A point moved by the original core has every quotient stabilizer element
represented by a lift centralizing that same point. -/
theorem point_centralizer_surjects {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u : (⁅D.UH,D.H⁆ : Subgroup G))
    (hm : ¬ D.QH ≤ centralizer ({(u : G)} : Set G))
    (y : OrthogonalActor) (hy : y • o.coordinates u = o.coordinates u) :
    ∃ k : D.H, (k : G) ∈ centralizer ({(u : G)} : Set G) ∧ o.actor k = y := by
  obtain ⟨x,hx⟩ := o.onto y
  let v := (⁅D.UH,D.H⁆).normalizerMonoidHom
    ⟨(x⁻¹ : D.H),normalizer_commutator_ge_right D.UH D.H (x⁻¹).property⟩ u
  have he : o.coordinates u = o.coordinates v := by
    rw [show o.coordinates v = o.actor x⁻¹ • o.coordinates u from o.compatible x⁻¹ u,
      map_inv,hx]
    exact (inv_smul_eq_iff.mpr hy.symm).symm
  obtain ⟨q,hq,hqv⟩ := same_coordinate_lifts_conjugate h o u v hm he
  let qH : D.H := ⟨q,pCoreIn_le 2 D.H hq⟩
  have hqker : o.actor qH = 1 := by
    change qH ∈ o.actor.ker
    rw [o.actor_kernel]
    exact hq
  refine ⟨x*qH,?_,by rw [map_mul,hqker,mul_one,hx]⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (MulAut.conj (x : G)) hqv
  have heq : (x : G)*q*(u : G)*((x : G)*q)⁻¹ = (u : G) := by
    simpa [v,MulAut.conj_apply,mul_assoc] using hh
  exact (mul_inv_eq_iff_eq_mul.mp heq)

/-- The abelian ambient span rules out a swapping actor once the original
point centralizer lifts onto its model stabilizer. -/
theorem swapping_impossible_of_abelian_envelope
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (B A : Subgroup G) [IsMulCommutative A]
    (hBA : B ≤ A) (hn : D.UH ≤ normalizer (B : Set G))
    (z : (⁅D.UH,D.H⁆ : Subgroup G)) (hzB : (z : G) ∈ B) (hzZ : (z : G) ∉ D.V₁)
    (hzcore : ¬ D.QH ≤ centralizer ({(z : G)} : Set G))
    (hC : D.H ⊓ centralizer ({(z : G)} : Set G) ≤ normalizer (A : Set G))
    (x : D.H) (hxB : (x : G) ∈ B) (hx2 : x ^ 2 = 1) :
    (o.actor x).right = 1 := by
  by_contra hs
  have hzz : o.coordinates z ≠ 1 := by
    intro he
    have hk : z ∈ o.coordinates.ker := he
    rw [o.vector_kernel] at hk
    exact hzZ hk
  have hab : A ≤ centralizer (A : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hxz : (x : G) ∈ centralizer ({(z : G)} : Set G) :=
    (hab.trans (centralizer_le (Set.singleton_subset_iff.mpr (hBA hzB)))) (hBA hxB)
  have hfixed : o.actor x • o.coordinates z = o.coordinates z := by
    apply (o.fixed_iff_commutator_mem x z).mpr
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_singleton_iff.mp hxz).symm]
    exact one_mem _
  obtain ⟨y,hy,v,hv⟩ := BinaryWreathPointStabilizer.swapping_point_stabilizer_obstruction
    (o.actor x) (o.coordinates z) hs (by rw [←map_pow,hx2,map_one]) hzz hfixed
  obtain ⟨k,hk,hky⟩ := point_centralizer_surjects h o z hzcore y hy
  obtain ⟨w,hw⟩ := o.surjective v
  let s : D.H := ⁅x,k⁆
  let w' := (⁅D.UH,D.H⁆).normalizerMonoidHom
    ⟨x,normalizer_commutator_ge_right D.UH D.H x.property⟩ w * w⁻¹
  have hw' : (w' : G) = ⁅(x : G),(w : G)⁆ := by
    rfl
  have hwB : (w' : G) ∈ B := by
    rw [hw']
    exact (le_normalizer_iff_commutator_le_left.mp hn)
      (commutator_mem_commutator hxB
        ((le_normalizer_iff_commutator_le_left.mp o.normalized) w.property))
  have hsA : (s : G) ∈ A :=
    (le_normalizer_iff_commutator_le_left.mp hC)
      (commutator_mem_commutator (hBA hxB) ⟨k.property,hk⟩)
  have hfix : o.actor s • o.coordinates w' = o.coordinates w' := by
    apply (o.fixed_iff_commutator_mem s w').mpr
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab hsA _ (hBA hwB))]
    exact one_mem _
  have hcoord : o.coordinates w' = o.actor x • v * v⁻¹ := by
    rw [map_mul,map_inv,o.compatible,hw]
  rw [hcoord] at hfix
  have hactor : o.actor s = ⁅o.actor x,y⁆ := by
    change o.actor ⁅x,k⁆ = _
    rw [map_commutatorElement,hky]
  exact hv (hactor ▸ hfix)

omit [Finite G] in
/-- An actor with no permutation of the coordinates preserves each covering plane. -/
theorem plane_normalized_of_no_shift {H U Z Q : Subgroup G}
    (o : SourceOrthogonalFourAction H U Z Q) (x : H)
    (hx : (o.actor x).right = 1) (i : OrthogonalPlaneIndex) :
    (x : G) ∈ normalizer (o.plane i : Set G) := by
  have hc (k : H) (hk : (o.actor k).right = 1)
      (v : G) (hv : v ∈ o.plane i) : k*v*k⁻¹ ∈ o.plane i := by
    let w : (⁅U,H⁆ : Subgroup G) := ⟨v,o.plane_le i hv⟩
    let w' := (⁅U,H⁆).normalizerMonoidHom
      ⟨k,normalizer_commutator_ge_right U H k.property⟩ w
    apply (o.mem_plane_iff i w').mpr
    rw [show o.coordinates w' = o.actor k • o.coordinates w from o.compatible k w]
    intro j hj
    change (o.actor k).left j • o.coordinates w ((o.actor k).right⁻¹*j) = 1
    rw [hk,inv_one,one_mul,(o.mem_plane_iff i w).mp hv j hj,smul_one]
  apply mem_normalizer_iff.mpr
  intro v
  constructor
  · exact hc x hx v
  · intro hv
    have hk : (o.actor x⁻¹).right = 1 := by
      rw [map_inv]
      change (o.actor x).right⁻¹ = 1
      rw [hx,inv_one]
    have hh := hc x⁻¹ hk (x*v*x⁻¹) hv
    simpa only [coe_inv,inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel,inv_mul_cancel,mul_one] using hh

omit [Finite G] in
/-- A lift of an actor exchanging the original summands really has nontrivial
permutation part in any coordinates marking the first summand. -/
theorem exchanging_actor_has_shift {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2))
    (i : OrthogonalPlaneIndex) (hi : o.plane i = firstSupport a H1)
    (x : H)
    (hs : (subspaceCommutator a.representation ⊤ (actorImage H H1)).map
      (a.representation (QuotientGroup.mk' (pCore 2 H) x)) =
        subspaceCommutator a.representation ⊤ (actorImage H H2)) :
    (o.actor x).right ≠ 1 := by
  intro hx
  have he := mem_normalizer_iff_map_conj_eq.mp (plane_normalized_of_no_shift o x hx i)
  rw [hi] at he
  have he' : (firstSupport a H1).map (MulAut.conj (x : G)).toMonoidHom = firstSupport a H2 := by
    unfold firstSupport
    rw [supportPreimage_conjugate,hs]
  have hsame : firstSupport a H1 = firstSupport a H2 := he.symm.trans he'
  have hsep := supportPreimage_disjoint_modulo a _ _ d.disjoint
  change firstSupport a H1 ⊓ firstSupport a H2 ≤ Z at hsep
  rw [←hsame,inf_idem] at hsep
  have hnon : subspaceCommutator a.representation ⊤ (actorImage H H1) ≠ ⊥ := by
    intro hb
    have hd := d.first_dimension
    rw [hb,finrank_bot] at hd
    omega
  exact (kernel_lt_supportPreimage a _ hnon).not_ge hsep

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- Already before 14.6.14, the original core centralizer in the orthogonal
moved group is exactly Z. Here only the fitting preimage inside H is used. -/
theorem source_orthogonal_moved_core_centralizer
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i : OrthogonalPlaneIndex) (hi : o.plane i = firstSupport a H1) :
    ⁅conjugateSpanBy (localModule T M) H,H⁆ ⊓ centralizer (H.pCoreIn 2 : Set G) =
      centralInvolutions T := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  obtain ⟨u,hu,hu2,_,_,k,hk,hku⟩ := source_exists_fixed_moving_in_support
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d
  have huK : u ∈ ⁅D.UH,D.H⁆ := o.plane_le i (hi.symm ▸ hu)
  apply orthogonal_moved_centralizer h o u huK
  intro hc
  have huOmega : u ∈ omegaOneCenterAmbient D.QH :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.UH_le_QH ((le_normalizer_iff_commutator_le_left.mp o.normalized) huK),hu2,
        fun q hq => mem_centralizer_singleton_iff.mp (hc hq)⟩
  have hR := residual_le_local_fitting a (T : Subgroup G) p H0 H1 H2 d
  have hF := source_generalizedFittingPreimage_centralizes_omegaCore hG T hempty hH h.H_centralizes
  have he := hF (hR hk) u huOmega
  exact hku (by rw [commutatorElement_eq_one_iff_mul_comm.mpr he]; exact one_mem _)

/-- The actual conjugate of the abelian Mc-span supplies the envelope in
14.6.13. The source point and its conjugator are unchanged. -/
theorem source_swapping_impossible_of_point_in_moved
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i : OrthogonalPlaneIndex) (hi : o.plane i = firstSupport a H1)
    (g : G)
    (hreverse : conjugateSpanBy (localModule T M) H ≤ H.map (MulAut.conj g).toMonoidHom)
    (z : G) (hz : z ∈ (centralInvolutions T).map (MulAut.conj g).toMonoidHom)
    (hzn : z ≠ 1) (hzZ : z ∉ centralInvolutions T)
    (hzK : z ∈ ⁅conjugateSpanBy (localModule T M) H,H⁆)
    (x : H) (hx : (x : G) ∈ (conjugateSpanBy (localModule T M) H).map
      (MulAut.conj g).toMonoidHom) (hx2 : x ^ 2 = 1) : (o.actor x).right = 1 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  let A := (conjugateSpanBy (localModule T M) Mc).map (MulAut.conj g).toMonoidHom
  let B := D.UH.map (MulAut.conj g).toMonoidHom
  let : IsMulCommutative (conjugateSpanBy (localModule T M) Mc) := hab
  let : IsMulCommutative A := inferInstance
  have hZB : (centralInvolutions T).map (MulAut.conj g).toMonoidHom ≤ B :=
    map_mono (h.point_lt.le.trans (le_conjugateSpanBy _ _))
  have hCg : centralizer ({z} : Set G) = Mc.map (MulAut.conj g).toMonoidHom := by
    have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
      (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hline : zpowers z = (centralInvolutions T).map (MulAut.conj g).toMonoidHom := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr hz)
      have hc : Nat.card ((centralInvolutions T).map (MulAut.conj g).toMonoidHom) = 2 := by
        rw [card_map_of_injective (MulAut.conj g).injective,h.point_card]
      rw [hc]
      exact Nat.succ_le_of_lt ((zpowers z).one_lt_card_iff_ne_bot.mpr (by simpa using hzn))
    rw [←centralizer_closure,←zpowers_eq_closure,hline,hMc]
    apply le_antisymm ?_ (map_centralizer_le_centralizer_image _ _)
    intro w hw
    refine ⟨(MulAut.conj g).symm w,?_,(MulAut.conj g).apply_symm_apply w⟩
    intro t ht
    apply (MulAut.conj g).injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using
      hw ((MulAut.conj g) t) (mem_map_of_mem _ ht)
  have hnA : Mc.map (MulAut.conj g).toMonoidHom ≤ normalizer (A : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      (le_normalizer_conjugateSpanBy (localModule T M) Mc)
    rwa [map_equiv_normalizer_eq] at hh
  have hnB : D.UH ≤ normalizer (B : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) o.normalized
    rw [map_equiv_normalizer_eq] at hh
    exact hreverse.trans hh
  apply swapping_impossible_of_abelian_envelope h o B A
    (map_mono (conjugateSpanBy_mono le_rfl hHMc)) hnB ⟨z,hzK⟩ (hZB hz) hzZ
    _ (inf_le_right.trans (hCg ▸ hnA)) x hx hx2
  intro hc
  apply hzZ
  rw [←source_orthogonal_moved_core_centralizer hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d o i hi]
  exact ⟨hzK,fun q hq => mem_centralizer_singleton_iff.mp (hc hq)⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
