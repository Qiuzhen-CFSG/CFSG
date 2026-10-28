module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.Support

/-!
# Quintic point centralizers without the factor-join index

A quintic element in the whole residual fixing a noncentral point of one
support lies in the opposite residual. Apply this calculation to the exact
critical conjugator, retaining its reverse point containment. It identifies
the prime-order closure in the conjugated residual and, when the original
point-centralizer closure is known, proves that conjugator normalizes the
opposite residual and that its normalizer escapes Mc.

Source: Aschbacher--Smith 14.6.15, printed p.1034.
The ordinary point-centralizer closure is retained as an explicit premise.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

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

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs hp w

omit hp w [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)] in
private theorem original_residual_odd : Odd (Nat.card (pResidual 2 (J ⧸ pCore 2 J))) := by
  obtain ⟨p,hp,hE,_hr,_hne,_hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p (pResidual 2 (J ⧸ pCore 2 J))).exists_card_eq
  rw [hn]
  exact (show Odd p by rcases hp with rfl | rfl <;> decide).pow

/-- A quintic element fixing a noncentral first-support point belongs to
the opposite residual. All actors and quotient maps are the original ones. -/
theorem source_quintic_residual_fixed_point (i j : d.Index) (hij : i ≠ j) {u x : G}
    (hup : u ∈ firstSupport a (actorPreimage J (f.ambientFactor d i).actor))
    (hun : u ∉ centralInvolutions T) (hx : x ∈ residual J) (ho : orderOf x = 5)
    (hfix : ⁅x,u⁆ ∈ centralInvolutions T) :
    x ∈ residual (actorPreimage J (f.ambientFactor d j).actor) := by
  let H1 := actorPreimage J (f.ambientFactor d i).actor
  let H2 := actorPreimage J (f.ambientFactor d j).actor
  have hjoin : residual H1 ⊔ residual H2 = residual J :=
    source_quintic_residual_join_of_ne hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w i j hij
  have hsupport : firstSupport a H1 ≤ centralizer (residual H2 : Set G) :=
    source_quintic_support_centralizes_residual hG T hempty hM hu hmany hcard e hab
      J hJ a f d i j hij
  let U := conjugateSpanBy (localModule T M) J
  let Z := centralInvolutions T
  let q := QuotientGroup.mk' (pCore 2 J)
  have huU : u ∈ U := supportPreimage_le a _ hup
  let v := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,huU⟩)
  let C : Subgroup (J ⧸ pCore 2 J) := {
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
  let A := actorImage J (residual H1)
  let B := actorImage J (residual H2)
  have h1H : residual H1 ≤ J := (residual_le H1).trans
    (actorPreimage_le J _)
  have h2H : residual H2 ≤ J := (residual_le H2).trans
    (actorPreimage_le J _)
  have hBC : B ≤ C := by
    rintro k ⟨b,hb,rfl⟩
    change a.representation (q b) v = v
    rw [a.conjugation]
    have hc := hsupport hup b hb
    apply congrArg Additive.ofMul
    apply congrArg (QuotientGroup.mk' (Z.subgroupOf U))
    apply Subtype.ext
    change (b:G)*u*(b:G)⁻¹ = u
    rw [hc,mul_inv_cancel_right]
  have hAC : ¬ A ≤ C := by
    intro hAC
    apply hun
    apply source_first_support_fixedFree hG T hempty hM hu hmany hcard e hab J hJ.1 a
      (original_residual_odd hG T hempty hM hu hmany hcard e hab J hJ hs) H1 u hup
    intro k hk
    have hkq : q ⟨k,residual_le J hk⟩ ∈ A ⊔ B := by
      have hj : actorImage J (residual J) = A ⊔ B := by
        rw [←hjoin]
        unfold actorImage
        rw [subgroupOf_sup h1H h2H,Subgroup.map_sup]
        rfl
      rw [←hj]
      exact mem_map_of_mem _ hk
    have hf := (sup_le hAC hBC) hkq
    change a.representation (q ⟨k,residual_le J hk⟩) v = v at hf
    rw [a.conjugation] at hf
    have hc := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hf)
    change k*u*k⁻¹/u ∈ Z at hc
    have hh := Z.inv_mem hc
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,commutatorElement_def,mul_assoc] using hh
  have hn : A ≤ normalizer (B : Set (J ⧸ pCore 2 J)) :=
    actorImage_normalizes (residual H2) (residual H1) h2H
      ((embedded_pResidual_mono 2 (actorPreimage_le J _)).trans
        (source_quintic_residual_normalizes_factor hG T hempty hM hu hmany hcard e hab
          J hJ hs a f d π hp w j))
  have hxq : q ⟨x,residual_le J hx⟩ ∈ (A ⊔ B) ⊓ C := by
    constructor
    · have hj : actorImage J (residual J) = A ⊔ B := by
        rw [←hjoin]
        unfold actorImage
        rw [subgroupOf_sup h1H h2H,Subgroup.map_sup]
        rfl
      rw [←hj]
      exact mem_map_of_mem _ hx
    · change a.representation (q ⟨x,residual_le J hx⟩) v = v
      rw [a.conjugation]
      apply congrArg Additive.ofMul
      apply QuotientGroup.eq_iff_div_mem.mpr
      change x*u*x⁻¹/u ∈ Z
      simpa only [commutatorElement_def,div_eq_mul_inv] using hfix
  have hxB := prime_first_stabilizer A B C (source_quintic_residual_actor_card T J a f d π w i) hn hBC hAC hxq
  have hx2 : x ∈ H2 := by
    have hi : B ≤ (f.ambientFactor d j).actor := by
      rw [←actorImage_actorPreimage J (f.ambientFactor d j).actor]
      exact map_mono (subgroupOf_mono J (residual_le H2))
    exact ⟨⟨x,residual_le J hx⟩,hi hxB,rfl⟩
  refine ⟨⟨x,hx2⟩,?_,rfl⟩
  apply mem_pResidual_of_orderOf_coprime
  rw [←Subgroup.orderOf_coe (⟨x,hx2⟩ : H2),ho]
  decide

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J))

/-- The actual critical conjugator gives the opposite residual as the
quintic closure in the conjugated residual's ordinary point centralizer. -/
theorem source_quintic_conjugate_point_closure (i j : d.Index) (hij : i ≠ j)
    (c : Quintic.CriticalPair
      (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1)
        a Mc (actorPreimage J (f.ambientFactor d i).actor)) :
    closure {x : G | x ∈ (residual J).map (MulAut.conj c.endpoint.representative).toMonoidHom ⊓
      centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} =
      (residual (actorPreimage J (f.ambientFactor d j).actor)).map
        (MulAut.conj c.endpoint.representative).toMonoidHom := by
  let H1 := actorPreimage J (f.ambientFactor d i).actor
  let H2 := actorPreimage J (f.ambientFactor d j).actor
  have hsupport : firstSupport a H1 ≤ centralizer (residual H2 : Set G) :=
    source_quintic_support_centralizes_residual hG T hempty hM hu hmany hcard e hab
      J hJ a f d i j hij
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  classical
  let ec := MulAut.conj c.endpoint.representative
  let Z := centralInvolutions T
  have hnot : ¬ Z ≤ Z.map ec.toMonoidHom := by
    intro hl
    have he : Z = Z.map ec.toMonoidHom := eq_of_le_of_card_ge hl
      (by rw [card_map_of_injective ec.injective])
    apply c.outside
    exact hMc.ge (normalizer_le_centralizer_of_card_two Z
      (plane_centralInvolutions_card T M hM.1.2 hcard e)
        (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  obtain ⟨z,hz,hzn⟩ := Set.not_subset.mp hnot
  obtain ⟨u,hupt,heu⟩ := c.reverse_point_le hz
  change ec u = z at heu
  have huZ : u ∉ Z := fun hh => hzn (heu ▸ mem_map_of_mem ec.toMonoidHom hh)
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1.1
    have hyK : y ∈ residual J := hy
    have hy5 : orderOf y = 5 := (ec.orderOf_eq y).symm.trans hx.2
    have hc : y*u = u*y := by
      apply ec.injective
      have hh := (hx.1.2 z hz).symm
      change ec y * z = z * ec y at hh
      simpa only [map_mul,heu] using hh
    have hy2 := source_quintic_residual_fixed_point hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w i j hij hupt huZ hyK hy5 (by
      have hh : ⁅y,u⁆ = 1 := by
        change y*u*y⁻¹*u⁻¹ = 1
        rw [hc]
        group
      rw [hh]
      exact one_mem _)
    exact mem_map_of_mem ec.toMonoidHom hy2
  · rw [←source_quintic_residual_generated T J a f d π w j,map_primeOrderClosure_equiv 5 _ ec]
    apply Subgroup.closure_mono
    rintro x ⟨⟨y,hy,rfl⟩,ho⟩
    refine ⟨⟨mem_map_of_mem ec.toMonoidHom ?_,?_⟩,ho⟩
    · exact (embedded_pResidual_mono 2 (actorPreimage_le J _)) hy
    · intro z hz
      obtain ⟨u,hu,rfl⟩ := c.reverse_point_le hz
      have hc := hsupport hu y hy
      change ec u * ec y = ec y * ec u
      simpa only [map_mul] using (congrArg ec hc).symm

/-- The second-normalizer escape uses the literal critical conjugator.
The ordinary point-centralizer closure remains the source premise to prove. -/
theorem source_quintic_critical_normalizer_of_point_closure
    (i j : d.Index) (hij : i ≠ j)
    (c : Quintic.CriticalPair
      (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1)
        a Mc (actorPreimage J (f.ambientFactor d i).actor))
    (hpoint : closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} =
      residual J) :
    c.endpoint.representative ∈ normalizer
      (residual (actorPreimage J (f.ambientFactor d j).actor) : Set G) ∧
    ¬ normalizer (residual (actorPreimage J (f.ambientFactor d j).actor) : Set G) ≤ Mc := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJM : J ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
      J hJ.1.1 hJ.1.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups J from he ▸ Set.mem_singleton Mc).2
  have hg := mem_normalizer_of_primeOrder_centralizers 5 (centralInvolutions T)
    (residual J) (residual (actorPreimage J (f.ambientFactor d j).actor))
    (firstSupport a (actorPreimage J (f.ambientFactor d i).actor)) c.endpoint.representative
    (source_quintic_residual_generated T J a f d π w j)
    (((residual_le _).trans ((actorPreimage_le J _).trans hJM)).trans_eq hMc)
    c.point_le
    (source_quintic_support_centralizes_residual hG T hempty hM hu hmany hcard e hab
      J hJ a f d i j hij) hpoint
    (source_quintic_conjugate_point_closure hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w i j hij c)
  exact ⟨hg,fun hn => c.outside (hn hg)⟩

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
