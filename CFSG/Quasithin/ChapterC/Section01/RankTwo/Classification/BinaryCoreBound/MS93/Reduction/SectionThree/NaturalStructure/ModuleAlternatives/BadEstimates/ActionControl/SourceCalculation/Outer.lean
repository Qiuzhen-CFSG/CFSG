module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Outer
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The source-(3.3) calculation in the outer extension

In printed (3.2)(v), Z is the direct sum of the fixed part and the natural
three-space U, and [X:Z] = 2. The index makes the local action on X/Z trivial;
two-residual commutator idempotence then puts [X,G] in U.

At a critical pair put D = [X_a,X_a']. A nontrivial critical involution and
the already proved displacement bound give |D| ≥ 4. Since D ≤ U_a' and
|U_a'| = 8, D has index at most two in U_a'. For any subgroup Y of the
endpoint stabilizer, D[D,Y] is Y-invariant and still has index at most two.
Thus [U_a',Y] ≤ D[D,Y]. The fixed part contributes no commutator, and
D ≤ X_a ∩ Q_a' gives the required bound with its literal orientation.

This proves the outer-branch containment directly; it does not treat the
printed failure alternatives as a universal containment theorem. It keeps
X distinct from Z and retains D throughout. No offender uniqueness or
later source-(3.8) exclusion enters the argument.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation (3.0), printed p.859; (3.2)(v), p.863; (3.3), pp.866–868.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Outer

private theorem commutator_le_sup_of_index_le_two {G : Type*} [Group G]
    (V D Y : Subgroup G) [Finite V] (hDV : D ≤ V)
    (hindex : D.relIndex V ≤ 2) (hY : Y ≤ normalizer (V : Set G)) :
    ⁅V, Y⁆ ≤ D ⊔ ⁅D, Y⁆ := by
  let K := D ⊔ ⁅D, Y⁆
  have hKV : K ≤ V := sup_le hDV
    ((commutator_mono hDV le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hY))
  have hn : Y ≤ normalizer (K : Set G) := by
    apply le_normalizer_iff.mpr
    intro y hy x hx
    have hmap : D.map (MulAut.conj y).toMonoidHom ≤ K := by
      rintro _ ⟨d,hd,rfl⟩
      have hc : ⁅y,d⁆ ∈ ⁅D, Y⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator hy hd
      have hh := K.mul_mem (mem_sup_right hc) (mem_sup_left hd)
      simpa [commutatorElement_def, mul_assoc] using hh
    have hm : K.map (MulAut.conj y).toMonoidHom ≤ K := by
      rw [Subgroup.map_sup]
      exact sup_le hmap ((mem_normalizer_iff_map_conj_eq.mp
        (normalizer_commutator_ge_right D Y hy)).le.trans le_sup_right)
    exact hm (mem_map_of_mem (MulAut.conj y).toMonoidHom hx)
  have hi : K.relIndex V ≤ 2 := (Nat.le_of_dvd
    (Nat.pos_of_ne_zero ((D.subgroupOf V).index_ne_zero_of_finite))
    (relIndex_dvd_of_le_left V (show D ≤ K from le_sup_left))).trans hindex
  have hpos : K.relIndex V ≠ 0 := (K.subgroupOf V).index_ne_zero_of_finite
  have hc : K.relIndex V = 1 ∨ K.relIndex V = 2 := by omega
  rcases hc with hc | hc
  · exact (le_normalizer_iff_commutator_le_left.mp hY).trans (relIndex_eq_one.mp hc)
  · exact commutator_le_of_normalized_index_two V K Y hKV hc hY hn

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem X_residual_idempotent (a : Vertex R) :
    ⁅⁅X R a, Ltilde R a⁆, Ltilde R a⁆ = ⁅X R a, Ltilde R a⁆ := by
  let S := stabilizer R a
  let W := (X R a).subgroupOf S
  let := finite_stabilizer R a
  let := X_elementary R a
  have hXS : X R a ≤ S := (omegaCenter_le _).trans (fun _ hx => hx.1)
  let : W.Normal := X_normal R a
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hXS
  have h := commutator_isPPerfect_idempotent (pResidual 2 S) W
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 W) le_normalizer_of_normal
  have hm := congrArg (Subgroup.map S.subtype) h
  simpa only [map_commutator, map_subgroupOf_eq_of_le hXS, Ltilde, W, S] using hm

/-- The entire local action on X has its displacement in U in the outer case. -/
theorem X_commutator_le_U (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source)
    (a : Vertex R) (ha : color R a = false) : ⁅X R a, stabilizer R a⁆ ≤ U R a := by
  obtain ⟨frame⟩ := exists_frame a ha
  have hZX : Z R a ≤ X R a := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]; exact hb)
  have hi := (outerExtension_at source h a frame).2.2.2
  have hXZ := commutator_le_of_normalized_index_two (X R a) (Z R a) (stabilizer R a)
    hZX hi (X_normalized R a) (Z_normalized R a)
  have he : ⁅X R a, Ltilde R a⁆ = ⁅X R a, stabilizer R a⁆ :=
    commutator_eq_of_centralizing_sup
      (by rw [sup_comm]; exact source.local_generation a ha)
      (Q_le_centralizer_X R a) ((Ltilde_le_stabilizer a).trans (X_normalized R a))
  rw [← he, ← X_residual_idempotent a]
  exact commutator_mono ((commutator_mono le_rfl (Ltilde_le_stabilizer a)).trans hXZ) le_rfl

/-- The auxiliary commutator stays inside both natural moving subgroups. -/
theorem critical_commutator_le_U (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅X R a, X R a'⁆ ≤ U R a' := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl (critical_X_le_stabilizer source geometry hb a ha a' hc)).trans
    (X_commutator_le_U source geometry hb h a' (critical_endpoint_color R a ha _ hc))


/-- A critical actor moves at least four points of X, all in the auxiliary
commutator. The bound comes from the actual marked outer extension. -/
theorem four_le_card_critical_commutator (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    4 ≤ Nat.card (⁅X R a, X R a'⁆ : Subgroup (FreeAmalgam R)) := by
  classical
  let := X_elementary R (alpha R)
  let := X_elementary R a
  let := finite_X R (alpha R)
  let := finite_X R a'
  let D := ⁅X R a, X R a'⁆
  let : Finite D := Finite.of_injective
    (Subgroup.inclusion ((critical_commutator_le_intersection source geometry hb a ha a' hc).trans
      inf_le_right)) (Subgroup.inclusion_injective _)
  obtain ⟨frame⟩ := exists_frame a' (critical_endpoint_color R a ha _ hc)
  have hZX : Z R a ≤ X R a := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]; exact hb)
  obtain ⟨z,hz,hzQ⟩ := Set.not_subset.mp hc.2
  have hzX : z ∈ X R a := hZX hz
  have hzS : z ∈ stabilizer R a' := critical_X_le_stabilizer source geometry hb a ha a' hc hzX
  let m : M := frame.localEquiv.symm ⟨z,hzS⟩
  have hm : (frame.localEquiv m : FreeAmalgam R) = z :=
    congrArg Subtype.val (frame.localEquiv.apply_symm_apply ⟨z,hzS⟩)
  have hz2 : z ^ 2 = 1 := by
    exact congrArg Subtype.val ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (X R a))) (⟨z,hzX⟩ : X R a))
  have hm2 : m ^ 2 = 1 := by
    apply frame.localEquiv.injective
    apply Subtype.ext
    simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, hm] using hz2
  have hg2 : (source.projection m) ^ 2 = 1 := by rw [← map_pow,hm2,map_one]
  have hgne : source.projection m ≠ 1 := by
    intro hg
    have hk : frame.localEquiv m ∈ (frame.projection source).ker := by
      change frame.projection source (frame.localEquiv m) = 1
      rwa [frame.projection_localEquiv]
    rw [frame.projection_kernel] at hk
    exact hzQ (hm ▸ hk)
  let ρ := Offenders.linearize (xAction source)
  let W := LinearMap.range (ρ (source.projection m) - LinearMap.id)
  have hdim : 2 ≤ Module.finrank (ZMod 2) W := by
    have hi := Models.outerExtension_involutionBound source geometry hb h
      (source.projection m) hg2 hgne
    rwa [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hi
  have hmem (v : W) : frame.conjugation (v.val.toMul : FreeAmalgam R) ∈ D := by
    obtain ⟨w,hw⟩ := v.property
    rw [← hw]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, toMul_sub, div_eq_mul_inv,
      Subgroup.coe_mul, Subgroup.coe_inv]
    change frame.conjugation
      ((xAction source (source.projection m) w.toMul : FreeAmalgam R) *
        (w.toMul : FreeAmalgam R)⁻¹) ∈ D
    rw [xAction,layerAction_apply,map_mul,map_mul,map_mul,map_inv,map_inv,
      ← frame.localEquiv_val,hm]
    exact commutator_mem_commutator hzX (by
      rw [← frame.map_X]
      exact mem_map_of_mem _ w.toMul.property)
  let f : W → D := fun v => ⟨frame.conjugation (v.val.toMul : FreeAmalgam R),hmem v⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact frame.conjugation.injective (congrArg Subtype.val he)
  have hcard := Nat.card_le_card_of_injective f hf
  have hW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  rw [Nat.card_zmod] at hW
  have hpow : 4 ≤ Nat.card W := by
    rw [hW]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim)
  exact hpow.trans hcard


/-- The natural moving subgroup has at most two cosets modulo the critical
auxiliary commutator. This keeps X and Z distinct. -/
theorem critical_commutator_index_le_two (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    (⁅X R a, X R a'⁆).relIndex (U R a') ≤ 2 := by
  obtain ⟨frame⟩ := exists_frame a' (critical_endpoint_color R a ha _ hc)
  obtain ⟨model⟩ := (outerExtension_at source h a' frame).1
  have hDU := critical_commutator_le_U source geometry hb h a ha a' hc
  have hsize := ((⁅X R a, X R a'⁆).subgroupOf (U R a')).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDU).toEquiv,model.card] at hsize
  have hlow := four_le_card_critical_commutator source geometry hb h a ha a' hc
  change (⁅X R a, X R a'⁆).relIndex (U R a') * Nat.card (⁅X R a, X R a'⁆ : Subgroup (FreeAmalgam R)) = 8 at hsize
  nlinarith

/-- The outer-case calculation holds for every actor in the endpoint
stabilizer, hence in particular for the printed centralizing edge actor. -/
theorem bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ stabilizer R a') :
    ⁅Z R a', Y⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆ := by
  let := X_elementary R a'
  let := finite_X R a'
  have ha' := critical_endpoint_color R a ha _ hc
  have hZX := (critical_endpoint_choice source geometry hb a ha a' hc).1
  have hUX := (U_le_Z a').trans hZX
  let : Finite (U R a') := Finite.of_injective (inclusion hUX) (inclusion_injective _)
  let D := ⁅X R a, X R a'⁆
  let K := D ⊔ ⁅D, Y⁆
  have hDU := critical_commutator_le_U source geometry hb h a ha a' hc
  have hnU := hY.trans (U_normalized a')
  have hUK : ⁅U R a', Y⁆ ≤ K := commutator_le_sup_of_index_le_two
    (U R a') D Y hDU (critical_commutator_index_le_two source geometry hb h a ha a' hc) hnU
  have hKX : K ≤ X R a' := (sup_le hDU
    ((commutator_mono hDU le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hnU))).trans hUX
  have hXK : X R a' ≤ normalizer (K : Set (FreeAmalgam R)) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx k hk
    exact congrArg Subtype.val (mul_comm (⟨k,hKX hk⟩ : X R a') ⟨x,hx⟩)
  have hfixed : fixedAt R a' ≤ centralizer (Y : Set (FreeAmalgam R)) := by
    intro c hc y hy
    exact ((source.X_fixed_eq_stabilizer_fixed a' ha').le hc).2 y (hY hy)
  obtain ⟨frame⟩ := exists_frame a' ha'
  have hsum := (outerExtension_at source h a' frame).2.1
  have hpre : Z R a' ≤ commutatorPreimage (X R a') Y K := by
    rw [hsum]
    exact sup_le
      (le_commutatorPreimage (show fixedAt R a' ≤ X R a' from inf_le_left)
        ((commutator_eq_bot_iff_le_centralizer.mpr hfixed).le.trans bot_le))
      (le_commutatorPreimage hUX hUK)
  have hbound : ⁅Z R a', Y⁆ ≤ K :=
    (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le (X R a') Y K hXK)
  have hDA : D ≤ X R a ⊓ Q R a' :=
    (critical_commutator_le_intersection source geometry hb a ha a' hc).trans
      (inf_le_inf le_rfl (omegaCenter_le _))
  exact hbound.trans (sup_le_sup le_rfl (commutator_mono hDA le_rfl))

/-- MS93 (3.3) in the index-two outer extension, with the literal actor
Q_t ∩ C([Z_a,Z_a']) and the source orientation of X_a ∩ Q_a'. -/
theorem source33Bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source) : Source33Bound R geometry := by
  intro a ha a' hc t hat _ Y hY
  apply bound source geometry hb h a ha a' hc Y
  intro y hy
  exact (hY hy).1.2 a' (adjacent_symm R hat)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Outer
