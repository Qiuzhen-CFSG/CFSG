module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualSource
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
/-!
# Residual-factor control for the original second normalizer

In the branch K_z = O²(H), the residual factors are subnormal in M_c.
Their two-perfectness makes O₂(M_c) normalize both, so the index-two
intersection with N_G(K₂) has the same two-core.

On the literal H/O₂(H)-module, the first residual actor is cyclic of
order five and has no nonzero fixed point on the first support modulo Z.
The opposite actor centralizes that support. Thus an order-five element
of K fixing a point of the first support outside Z belongs to K₂.
Using the original critical-pair element g gives the required identity
θ(K_z^g ∩ C_G(Z)) = K₂^g, with the actual ambient conjugation map.

The final consumers discharge these two fields of NormalizerGeometry.
The point-centralizer closure and index in M_c remain explicit obligations
of qt-e-14615-quintic-exclusion, as do the exchanged PSL₂(16) branch and
remaining component comparisons. The earlier 14.6.12--14 inputs retain
final discharge with qt-e-suitable-odd-normalizer. This does not prove p=3.

Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion ComponentExclusion.ContainedComparison
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
private theorem residual_factor_subnormal {B : Subgroup G}
    (hBK : B ≤ residual H)
    (hn : H0 ≤ normalizer (B : Set G))
    (hc : residualClosure H Mc = residual H) : (B.subgroupOf Mc).IsSubnormal := by
  have hKH0 : residual H ≤ H0 := by
    rw [←residual_factors_join a s.factors]
    exact sup_le ((residual_le H1).trans s.factors.first_le)
      ((residual_le H2).trans s.factors.second_le)
  have hKN : Mc ≤ normalizer (residual H : Set G) := by
    rw [←hc]
    exact le_normalizer_conjugateSpanBy _ _
  let : ((residual H).subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hKN
  have hn' : ((residual H).subgroupOf Mc) ≤ normalizer (B.subgroupOf Mc : Set Mc) :=
    (comap_mono (hKH0.trans hn)).trans (le_normalizer_comap Mc.subtype)
  exact IsSubnormal.step _ _ (subgroupOf_mono Mc hBK)
    (inferInstance : ((residual H).subgroupOf Mc).Normal).isSubnormal
    (normal_subgroupOf_of_le_normalizer hn')

omit [Finite G] in
private theorem core_normalizes_subnormal {B : Subgroup G}
    (hB : B ≤ Mc) (hsub : (B.subgroupOf Mc).IsSubnormal) (hp : IsPPerfect 2 B) :
    Mc.pCoreIn 2 ≤ normalizer (B : Set G) := by
  have hp' : IsPPerfect 2 (B.subgroupOf Mc) := hp.of_surjective
    (subgroupOfEquivOfLe hB).symm.toMonoidHom (subgroupOfEquivOfLe hB).symm.surjective
  have hn := le_normalizer_of_isSubnormal_isPPerfect (B.subgroupOf Mc) (pCore 2 Mc)
    hsub hp' pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
  have hm := (map_mono hn (f := Mc.subtype)).trans (le_normalizer_map Mc.subtype)
  rwa [map_subgroupOf_eq_of_le hB] at hm

include s in
/-- The partner two-core normalizes each original residual factor. -/
theorem source_residual_core_normalizes_factors (hc : residualClosure H Mc = residual H) :
    Mc.pCoreIn 2 ≤ normalizer (residual H1 : Set G) ∧
    Mc.pCoreIn 2 ≤ normalizer (residual H2 : Set G) := by
  have hHM : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
      s.many s.module_card s.action H s.outside.1 s.outside.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have h1 : residual H1 ≤ Mc := (residual_le H1).trans
    ((s.factors.first_le.trans s.factors.zero_le).trans hHM)
  have h2 : residual H2 ≤ Mc := (residual_le H2).trans
    ((s.factors.second_le.trans s.factors.zero_le).trans hHM)
  have hj := residual_factors_join a s.factors
  constructor
  · exact core_normalizes_subnormal h1 (residual_factor_subnormal s
      (hj ▸ le_sup_left) (s.factors.normalizes_first.trans
        (normalizer_le_normalizer_characteristic_image H1 (pResidual 2 H1))) hc)
      (isPPerfect_embedded_pResidual 2 H1)
  · exact core_normalizes_subnormal h2 (residual_factor_subnormal s
      (hj ▸ le_sup_right) (s.factors.normalizes_second.trans
        (normalizer_le_normalizer_characteristic_image H2 (pResidual 2 H2))) hc)
      (isPPerfect_embedded_pResidual 2 H2)

include s in
/-- The index-two second-normalizer intersection has the original partner core. -/
theorem source_residual_intersection_core (hc : residualClosure H Mc = residual H)
    (hi : (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2) :
    (Mc ⊓ normalizer (residual H2 : Set G)).pCoreIn 2 = Mc.pCoreIn 2 := by
  let B := Mc ⊓ normalizer (residual H2 : Set G)
  let : (B.subgroupOf Mc).Normal := normal_of_index_eq_two hi
  have hQB : Mc.pCoreIn 2 ≤ B := le_inf (pCoreIn_le 2 Mc)
    (source_residual_core_normalizes_factors s hc).2
  exact le_antisymm (pCoreIn_mono_of_normalizes inf_le_left
    (le_normalizer_of_normal_subgroupOf (show B ≤ Mc from inf_le_left)))
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Mc) hQB
      (inf_le_left.trans (Mc.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))))

private theorem prime_first_stabilizer {D : Type*} [Group D] [Finite D]
    (A B C : Subgroup D) (hc : Nat.card A = 5) (hn : A ≤ normalizer (B : Set D))
    (hB : B ≤ C) (hA : ¬ A ≤ C) : (A ⊔ B) ⊓ C ≤ B := by
  let : Fact (Nat.Prime (Nat.card A)) := ⟨by rw [hc]; decide⟩
  have hbot : C.subgroupOf A = ⊥ := by
    rcases (C.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
    · exact hb
    · exact (hA (fun x hx => ht.ge (mem_top (⟨x,hx⟩ : A)))).elim
  intro x hx
  have hprod : x ∈ (A : Set D) * (B : Set D) := by
    rw [←coe_mul_of_left_le_normalizer_right A B hn]
    exact hx.1
  obtain ⟨a,ha,b,hb,rfl⟩ := hprod
  have haC : a ∈ C := by
    have hh := C.mul_mem hx.2 (C.inv_mem (hB hb))
    simpa using hh
  have ha1 : a = 1 := congrArg Subtype.val
    (show (⟨a,ha⟩ : A) = 1 from hbot.le haC)
  change a*b ∈ B
  rw [ha1,one_mul]
  exact hb

private theorem residual_actor_eq (H B : Subgroup G) (hB : B ≤ H) :
    actorImage H (residual B) =
      (pResidual 2 (actorImage H B)).map (actorImage H B).subtype := by
  have he : (residual B).subgroupOf H =
      (pResidual 2 (B.subgroupOf H)).map (B.subgroupOf H).subtype := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((residual_le B).trans hB),map_embedded_pResidual,
      map_subgroupOf_eq_of_le hB]
    rfl
  unfold actorImage
  rw [he,map_embedded_pResidual]


include s in
/-- The first residual acts through an actual cyclic subgroup of order five. -/
theorem source_residual_first_actor_card : Nat.card (actorImage H (residual H1)) = 5 := by
  rw [residual_actor_eq H H1 (s.factors.first_le.trans s.factors.zero_le),
    card_map_of_injective (actorImage H H1).subtype_injective]
  apply card_twoResidual_of_card_twice_odd_prime (by decide : Odd 5)
  rw [Nat.card_congr s.factors.first_model.some.toEquiv,DihedralGroup.nat_card]

include s in
/-- A quintic element fixing a noncentral first-support point lies in the second residual. -/
theorem source_residual_quintic_fixed_point {u x : G}
    (hu : u ∈ firstSupport a H1) (hun : u ∉ centralInvolutions T)
    (hx : x ∈ residual H) (ho : orderOf x = 5)
    (hfix : ⁅x,u⁆ ∈ centralInvolutions T) : x ∈ residual H2 := by
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let q := QuotientGroup.mk' (pCore 2 H)
  have huU : u ∈ U := supportPreimage_le a _ hu
  let v := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,huU⟩)
  let C : Subgroup (H ⧸ pCore 2 H) := {
    carrier := {k | a.representation k v = v}
    one_mem' := by simp
    mul_mem' := by
      intro k l hk hl
      change a.representation (k*l) v = v
      rw [map_mul,Module.End.mul_apply,hl,hk]
    inv_mem' := by
      intro k hk
      change a.representation k⁻¹ v = v
      calc
        _ = a.representation k⁻¹ (a.representation k v) := congrArg _ hk.symm
        _ = v := a.representation.inv_self_apply k v }
  let A := actorImage H (residual H1)
  let B := actorImage H (residual H2)
  have h1H : residual H1 ≤ H := (residual_le H1).trans
    (s.factors.first_le.trans s.factors.zero_le)
  have h2H : residual H2 ≤ H := (residual_le H2).trans
    (s.factors.second_le.trans s.factors.zero_le)
  have hBC : B ≤ C := by
    rintro k ⟨b,hb,rfl⟩
    change a.representation (q b) v = v
    rw [a.conjugation]
    have hc := (source_residual_factor_supports s).2.2.1 hu b hb
    apply congrArg Additive.ofMul
    apply congrArg (QuotientGroup.mk' (Z.subgroupOf U))
    apply Subtype.ext
    change (b:G)*u*(b:G)⁻¹ = u
    rw [hc,mul_inv_cancel_right]
  have hAC : ¬ A ≤ C := by
    intro hAC
    apply hun
    apply source_first_support_fixedFree s.ambient T s.empty s.maximal s.unique s.many
      s.module_card s.action s.abelian H s.outside a
      (by rw [s.factors.residual_card]; decide) H1 u hu
    intro k hk
    have hkq : q ⟨k,residual_le H hk⟩ ∈ A ⊔ B := by
      have hj : actorImage H (residual H) = A ⊔ B := by
        rw [←residual_factors_join a s.factors]
        unfold actorImage
        rw [subgroupOf_sup h1H h2H,Subgroup.map_sup]
        rfl
      rw [←hj]
      exact mem_map_of_mem _ hk
    have hf := (sup_le hAC hBC) hkq
    change a.representation (q ⟨k,residual_le H hk⟩) v = v at hf
    rw [a.conjugation] at hf
    have hc := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hf)
    change k*u*k⁻¹/u ∈ Z at hc
    have hh := Z.inv_mem hc
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,commutatorElement_def,mul_assoc] using hh
  have hn : A ≤ normalizer (B : Set (H ⧸ pCore 2 H)) :=
    actorImage_normalizes (residual H2) (residual H1) h2H
      (((residual_le H1).trans s.factors.first_le).trans
        (s.factors.normalizes_second.trans
          (normalizer_le_normalizer_characteristic_image H2 (pResidual 2 H2))))
  have hxq : q ⟨x,residual_le H hx⟩ ∈ (A ⊔ B) ⊓ C := by
    constructor
    · have hj : actorImage H (residual H) = A ⊔ B := by
        rw [←residual_factors_join a s.factors]
        unfold actorImage
        rw [subgroupOf_sup h1H h2H,Subgroup.map_sup]
        rfl
      rw [←hj]
      exact mem_map_of_mem _ hx
    · change a.representation (q ⟨x,residual_le H hx⟩) v = v
      rw [a.conjugation]
      apply congrArg Additive.ofMul
      apply QuotientGroup.eq_iff_div_mem.mpr
      change x*u*x⁻¹/u ∈ Z
      simpa only [commutatorElement_def,div_eq_mul_inv] using hfix
  have hxB := prime_first_stabilizer A B C (source_residual_first_actor_card s) hn hBC hAC hxq
  have hx2 : x ∈ H2 := by
    have hi : B ≤ actorImage H H2 := map_mono (subgroupOf_mono H (residual_le H2))
    have hc : q.ker ≤ H2.subgroupOf H := by
      rw [QuotientGroup.ker_mk']
      intro y hy
      exact s.factors.core_le_second (mem_map_of_mem H.subtype hy)
    have hh : (⟨x,residual_le H hx⟩ : H) ∈ ((H2.subgroupOf H).map q).comap q := hi hxB
    rwa [comap_map_eq_self hc] at hh
  refine ⟨⟨x,hx2⟩,?_,rfl⟩
  apply mem_pResidual_of_orderOf_coprime
  rw [←Subgroup.orderOf_coe (⟨x,hx2⟩ : H2),ho]
  decide

include s in
/-- A noncentral point in the first support has only the opposite quintic residual. -/
theorem source_residual_point_centralizer {B : Subgroup G}
    (hB : B ≤ firstSupport a H1) (hne : ¬ B ≤ centralInvolutions T) :
    closure {x : G | x ∈ residual H ⊓ centralizer (B : Set G) ∧ orderOf x = 5} =
      residual H2 := by
  classical
  obtain ⟨u,hu,hun⟩ := Set.not_subset.mp hne
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    apply source_residual_quintic_fixed_point s (hB hu) hun hx.1.1 hx.2
    have hc := hx.1.2 u hu
    have he : ⁅x,u⁆ = 1 := by
      change x*u*x⁻¹*u⁻¹ = 1
      rw [←hc]
      group
    rw [he]
    exact one_mem _
  · rw [←(residual_factors_generated a s.factors).2]
    apply Subgroup.closure_mono
    intro x hx
    refine ⟨⟨?_,?_⟩,hx.2⟩
    · exact (show residual H2 ≤ residual H from
        (residual_factors_join a s.factors) ▸ le_sup_right) hx.1
    · exact le_centralizer_iff.mp (hB.trans (source_residual_factor_supports s).2.2.1) hx.1

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

include s in
/-- The conjugated centralizer identity uses the original critical-pair element. -/
theorem source_residual_conjugate_point_closure
    (hclosure : residualClosure H Mc = residual H) :
    closure {x : G |
      x ∈ (residualClosure H Mc).map
        (MulAut.conj s.critical.endpoint.representative).toMonoidHom ⊓
        centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} =
      (residual H2).map (MulAut.conj s.critical.endpoint.representative).toMonoidHom := by
  classical
  let e := MulAut.conj s.critical.endpoint.representative
  let Z := centralInvolutions T
  have hnot : ¬ Z ≤ Z.map e.toMonoidHom := by
    intro hl
    have he : Z = Z.map e.toMonoidHom := eq_of_le_of_card_ge hl
      (by rw [card_map_of_injective e.injective])
    apply s.critical.outside
    exact (partner_eq_centralizer s).ge (normalizer_le_centralizer_of_card_two Z
      (plane_centralInvolutions_card T M s.maximal.1.2 s.module_card s.action)
        (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  obtain ⟨z,hz,hzn⟩ := Set.not_subset.mp hnot
  obtain ⟨u,hu,heu⟩ := s.critical.reverse_point_le hz
  change e u = z at heu
  have huZ : u ∉ Z := fun hh => hzn (heu ▸ mem_map_of_mem e.toMonoidHom hh)
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1.1
    have hyK : y ∈ residual H := hclosure ▸ hy
    have hy5 : orderOf y = 5 := (e.orderOf_eq y).symm.trans hx.2
    have hc : y*u = u*y := by
      apply e.injective
      have hh := (hx.1.2 z hz).symm
      change e y * z = z * e y at hh
      simpa only [map_mul,heu] using hh
    have hy2 := source_residual_quintic_fixed_point s hu huZ hyK hy5 (by
      have hh : ⁅y,u⁆ = 1 := by
        change y*u*y⁻¹*u⁻¹ = 1
        rw [hc]
        group
      rw [hh]
      exact one_mem _)
    exact mem_map_of_mem e.toMonoidHom hy2
  · rw [←(residual_factors_generated a s.factors).2,map_primeOrderClosure_equiv 5 _ e]
    apply Subgroup.closure_mono
    rintro x ⟨⟨y,hy,rfl⟩,ho⟩
    refine ⟨⟨mem_map_of_mem e.toMonoidHom ?_,?_⟩,ho⟩
    · rw [hclosure,←residual_factors_join a s.factors]
      exact mem_sup_right hy
    · intro z hz
      obtain ⟨u,hu,rfl⟩ := s.critical.reverse_point_le hz
      have hc := (source_residual_factor_supports s).2.2.1 hu y hy
      change e u * e y = e y * e u
      simpa only [map_mul] using (congrArg e hc).symm

variable (hclosure : residualClosure H Mc = residual H)
    (hpoint : closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧
      orderOf x = 5} = residualClosure H Mc)
    (hindex : (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2)

/-- Residual geometry with the conjugated centralizer and intersection core
proved from the source context. Its two remaining controls belong to the
same quintic-exclusion owner. -/
noncomputable def controlledResidualNormalizerGeometry :
    NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative :=
  residualNormalizerGeometry s hclosure hpoint
    (source_residual_conjugate_point_closure s hclosure) hindex
    (source_residual_intersection_core s hclosure hindex)

/-- The literal residual factors are retained by the improved constructor. -/
theorem controlledResidualNormalizerGeometry_factors :
    let d := controlledResidualNormalizerGeometry s hclosure hpoint hindex
    d.K1 = residual H1 ∧ d.K2 = residual H2 :=
  residualNormalizerGeometry_factors s hclosure hpoint
    (source_residual_conjugate_point_closure s hclosure) hindex
    (source_residual_intersection_core s hclosure hindex)

include s hclosure hpoint hindex in
/-- Apply the two proved controls to the actual C.2.3 second-normalizer setup. -/
theorem controlled_residual_secondNormalizer_setup :
    s.critical.endpoint.representative ∈ normalizer (residual H2 : Set G) ∧
      ¬normalizer (residual H2 : Set G) ≤ Mc ∧
      Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
        (normalizer (residual H2 : Set G)) (Mc.pCoreIn 2)
          (Mc ⊓ normalizer (residual H2 : Set G)) ∧
      ((T : Subgroup G) ⊓ normalizer (residual H2 : Set G)).relIndex T = 2 :=
  residual_secondNormalizer_setup s hclosure hpoint
    (source_residual_conjugate_point_closure s hclosure) hindex
    (source_residual_intersection_core s hclosure hindex)

include s hclosure hpoint hindex in
/-- Extract the genuine escaping component and exclude its normalized natural
row under the two remaining residual-geometry controls. Final source assembly
and discharge of these controls remain with qt-e-14615-quintic-exclusion. -/
theorem controlled_residual_component_comparison :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2)) ∧
    ∀ j : SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2),
      Mc.pCoreIn 2 ≤ normalizer (j.J : Set G) →
        ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) :=
  residual_component_comparison s hclosure hpoint
    (source_residual_conjugate_point_closure s hclosure) hindex
    (source_residual_intersection_core s hclosure hindex)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
