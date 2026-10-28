module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableFullKernel
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity
public import Theory.Representation.NormalSimpleSeed.QuotientImage
public import Theory.GroupTheory.PResidual.AbelianQuotient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Thompson

/-!
# The solvable seed contradiction on the original central quotient

The checked full kernel comparison identifies the action on U/Z(U) with
the action on the elementary image of U in H/C_Z(U)(K). The original
natural seed V/V1 embeds in that image and its H-orbit generates it.
If dotted L1 is normal, the normal-image simple-seed theorem therefore
makes the L1-fixed subgroup of that image trivial.

The central LT seed is fixed by L1, so it lies in C_Z(U)(K). That subgroup
is H-normal; hence the entire orbit VH lies there, contradicting the
previously constructed order-four plane [VH,K]. This closes the solvable
paragraph of 14.3.25 conditional on its earlier marked action row.
For an actual S3 x S3 dotted group, its abelian two-residual and the
original Sylow normalization prove the required dotted L1 normality.
The final theorem discharges the seed premise in the literal Thompson
containment used in the Goldschmidt paragraph of 14.3.31.

The S3 x S3 identification and SolvableSeedRow are still explicit earlier
14.3.23--24 premises. Their construction, the nonsolvable marked rows,
the S6/G2(2) exclusions, and the Goldschmidt contradiction remain with
qt-d-hs-centerless-source. The completed action theorem assumes centerlessness
and is not used here. Final LocalStructure assembly remains with
qt-d-hs-local-structure. This module does not assert source centerlessness.

Source: Aschbacher--Smith, 14.3.23(2)(i), 14.3.25, and 14.3.31,
printed pp.1000--1003, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem seed_moved [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 (F.tilde V)]
    (hLV : L ≤ normalizer (V : Set G)) (D : F.NaturalSeedMarking L hLV) :
    ∃ k v, F.localSeedRepresentation L hLV k v ≠ v := by
  by_contra! hfix
  let v := D.coordinates.symm (![1,0] : Fin 2 → ZMod 2)
  obtain ⟨a,ha⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero
    (by decide : (![1,0] : Fin 2 → ZMod 2) ≠ 0)
    (by decide : (![0,1] : Fin 2 → ZMod 2) ≠ 0)
  obtain ⟨q,hq⟩ := D.quotientEquiv.surjective a
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  have he := D.equivariant k v
  rw [hfix,hq] at he
  simp only [v,LinearEquiv.apply_symm_apply] at he
  have hh := congrFun (he.trans ha) 0
  norm_num at hh

/-- The original central quotient has no L₁-fixed vector when dotted L₁ is normal. -/
theorem source_solvable_center_quotient_fixed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) :
    let q := QuotientGroup.mk' (solvableCenterFixed F g)
    ((F.U.subgroupOf F.H).map q) ⊓
      centralizer (((F.Li L 1).subgroupOf F.H).map q : Set (F.H ⧸ solvableCenterFixed F g)) = ⊥ := by
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let U := F.U.subgroupOf F.H
  let Uq := U.map q
  have hr := source_solvable_center_quotient_reduced d earlier hq chosen structural alternatives F hne g
  let := hr.normal
  let := hr.elementary
  let ρ := (NormalElementaryQuotient.originalAction Uq).comp q
  have hρ (a : F.H) (x : Additive Uq) :
      ((ρ a x).toMul : F.H ⧸ C) = q a * (x.toMul : F.H ⧸ C) * (q a)⁻¹ :=
    NormalElementaryQuotient.originalAction_apply Uq (q a) x
  let h := higherRankHypothesis d earlier hq chosen
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let σ := F.localSeedRepresentation L chosen.normalizes
  let k : F.Li L 1 →* F.H := inclusion ((F.Li_le L 1).trans inf_le_right)
  let p : F.G₁tilde →* (F.H ⧸ C) := QuotientGroup.map _ _ (MonoidHom.id F.H)
    (solvableCenterFixed_point F g)
  have hp (a : F.H) : p (F.tildeProjection a) = q a := rfl
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  have hVH : V ≤ F.H := hVU.trans F.U_le_H
  let f : F.tilde V →* Uq := (p.comp (F.tilde V).subtype).codRestrict Uq (by
    rintro ⟨x,a,ha,rfl⟩
    exact mem_map_of_mem q (hVU ha))
  let ι := f.toAdditive.toZModLinearMap 2
  have hi : Function.Injective ι := by
    apply (injective_iff_map_eq_zero ι).mpr
    intro x hx
    apply Additive.toMul.injective
    apply Subtype.ext
    obtain ⟨a,ha,he⟩ := x.toMul.property
    have hqa : q a = 1 := by
      have hh := congrArg (fun y : Additive Uq => (y.toMul : F.H ⧸ C)) hx
      change p (x.toMul : F.G₁tilde) = 1 at hh
      rw [←he] at hh
      exact hh
    have hC : a ∈ C := (QuotientGroup.eq_one_iff a).mp hqa
    have hpt : (a:G) ∈ F.Vi 1 :=
      (source_closure d earlier hq chosen structural alternatives F hne).2.2.le ⟨ha,hC.1⟩
    exact he.symm.trans ((QuotientGroup.eq_one_iff a).mpr hpt)
  have he (a : F.Li L 1) (x : Additive (F.tilde V)) :
      ι (σ a x) = ρ (k a) (ι x) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change p ((F.tildeAction (F.Li L 1) V _ _ a x.toMul : F.tilde V) : F.G₁tilde) = _
    rw [F.tildeAction_apply_coe,map_mul,map_mul,map_inv,hp]
    exact (NormalElementaryQuotient.originalAction_apply Uq (q (k a)) (ι x)).symm
  have hgen : ∀ R : Subrepresentation ρ, LinearMap.range ι ≤ R.toSubmodule → R = ⊤ := by
    intro R hR
    let A : Subgroup (F.H ⧸ C) := R.toSubmodule.toAddSubgroup.toSubgroup'.map Uq.subtype
    have hnA : F.H ≤ normalizer ((A.comap q).map F.H.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      intro a ha x hx
      obtain ⟨b,hb,rfl⟩ := hx
      obtain ⟨w,hw,hwe⟩ := hb
      refine ⟨(⟨a,ha⟩ : F.H) * b * (⟨a,ha⟩ : F.H)⁻¹,?_,rfl⟩
      refine ⟨(ρ ⟨a,ha⟩ (Additive.ofMul w)).toMul,R.apply_mem_toSubmodule ⟨a,ha⟩ hw,?_⟩
      change ((ρ ⟨a,ha⟩ (Additive.ofMul w)).toMul : F.H ⧸ C) = _
      rw [hρ]
      change q ⟨a,ha⟩ * Uq.subtype w * (q ⟨a,ha⟩)⁻¹ = _
      rw [hwe,map_mul,map_mul,map_inv]
    have hVA : V ≤ (A.comap q).map F.H.subtype := by
      intro v hv
      refine ⟨⟨v,hVH hv⟩,?_,rfl⟩
      exact ⟨f (F.tildeMap V hVH ⟨v,hv⟩), hR ⟨Additive.ofMul (F.tildeMap V hVH ⟨v,hv⟩),rfl⟩,rfl⟩
    have hUA : F.U ≤ (A.comap q).map F.H.subtype := conjugateSpanBy_le hVA hnA
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _
    obtain ⟨a,ha,he⟩ := x.toMul.property
    obtain ⟨b,hb,hba⟩ := hUA ha
    have hba' : b = a := Subtype.ext hba
    subst b
    obtain ⟨w,hw,hwe⟩ := hb
    have hwx : w = x.toMul := Subtype.ext (hwe.trans he)
    have hwx' : Additive.ofMul w = x := congrArg Additive.ofMul hwx
    exact hwx' ▸ hw
  let qhat := QuotientGroup.mk' F.uhatAction.ker
  have hker : qhat.ker ≤ ρ.ker := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    apply (NormalElementaryQuotient.originalAction_kernel Uq).ge
    exact (source_solvable_full_kernel d earlier hq chosen structural alternatives F hne hz g hgP hgH row).ge ha
  have hnormal : (qhat.comp k).range.Normal := by
    have heq : (qhat.comp k).range = dotImage F F.uhatAction (F.Li L 1) := by
      ext x
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨k a,a.property,rfl⟩
      · rintro ⟨a,ha,rfl⟩
        exact ⟨⟨a,ha⟩,rfl⟩
    rw [heq]
    exact hn
  have hf := fixed_eq_zero_of_normal_image_simple_seed ρ σ qhat k hker hnormal ι hi he
    ((irreducible_iff_isSimpleModule_asModule σ).mpr (D.seed_simple (by decide)))
    (seed_moved F chosen.normalizes D) hgen
  apply le_bot_iff.mp
  intro x hx
  let v : Additive Uq := Additive.ofMul ⟨x,hx.1⟩
  have hv : v = 0 := hf v (by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ (k a) v).toMul : F.H ⧸ C) = _
    rw [hρ]
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 (q (k a)) (mem_map_of_mem q a.property)))
  exact congrArg (fun y : Additive Uq => (y.toMul : F.H ⧸ C)) hv

/-- The solvable seed contradiction of 14.3.25 from its marked earlier row,
including the source normality clause for dotted L₁. -/
theorem source_seed_exclusion_of_solvable_row (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) :
    centralLTSeed F L = ⊥ := by
  by_contra hz
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  have hfix := source_solvable_center_quotient_fixed d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  have hseed : centralLTSeed F L ≤ C.map F.H.subtype := by
    intro z hz
    let zH : F.H := ⟨z,F.U_le_H hz.2⟩
    have hzq : q zH = 1 := hfix.le ⟨mem_map_of_mem q hz.2,by
      rintro _ ⟨a,ha,rfl⟩
      apply (map_mul q a zH).symm.trans
      apply Eq.trans _ (map_mul q zH a)
      apply congrArg q
      apply Subtype.ext
      obtain ⟨c,hc,he⟩ := hz.1
      have hcomm := congrArg Subtype.val (mem_center_iff.mp hc
        ⟨a,mem_sup_left ((F.Li_le L 1 ha).1)⟩)
      change (a:G) * z = z * (a:G)
      rw [←he]
      exact hcomm⟩
    exact ⟨zH,(QuotientGroup.eq_one_iff zH).mp hzq,rfl⟩
  have hnorm : F.H ≤ normalizer (C.map F.H.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha z hz
    obtain ⟨c,hc,rfl⟩ := hz
    exact ⟨(⟨a,ha⟩ : F.H) * c * (⟨a,ha⟩ : F.H)⁻¹,
      (inferInstance : C.Normal).conj_mem c hc ⟨a,ha⟩,rfl⟩
  have hspan : faithfulTestModule F L ≤ C.map F.H.subtype := conjugateSpanBy_le hseed hnorm
  have hWC : W ≤ C := by
    intro w hw
    obtain ⟨c,hc,he⟩ := hspan hw
    exact (Subtype.ext he : c = w) ▸ hc
  have hcomm : ⁅W,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hWC.trans inf_le_right)
  obtain ⟨heq,hcard,_⟩ := source_solvable_center_plane d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  rw [heq,hcomm,card_bot] at hcard
  omega

/-- The two-residual of the actual S₃ × S₃ quotient is abelian. Together
with the original Sylow normalization, this proves the marked L₁ normality. -/
theorem source_dot_Li_one_normal_of_symmetricThreePair (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    (dotImage F F.uhatAction (F.Li L 1)).Normal := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let N := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.uhatAction.ker
  obtain ⟨e⟩ := model
  have hcard : Nat.card (pResidual 2 (Hdot F F.uhatAction)) = 9 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) (K := pResidual 2 (Hdot F F.uhatAction)) e.injective,
      map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    exact SymmetricThreeProductResidual.residual_card
  let : IsMulCommutative (pResidual 2 (Hdot F F.uhatAction)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes structural)
      ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  have hLH : F.Li L 1 ≤ F.H := fun x hx => (F.Li_le L 1 hx).2
  have hp : IsPPerfect 2 N := by
    have hh : IsPPerfect 2 (F.Li L 1) := by
      rw [hres]
      exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
    exact hh.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  let S := (T.subtype (F.invariant 1)).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSN : (S : Subgroup (Hdot F F.uhatAction)) ≤ normalizer (N.map q : Set (Hdot F F.uhatAction)) := by
    apply le_trans (map_mono (f := q) ?_) (N.le_normalizer_map q)
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    exact (mem_normalizer_iff.mp (hTn ht)) (x : G)
  have hN : N.map q ≤ pResidual 2 (Hdot F F.uhatAction) :=
    le_pResidual_of_isPPerfect _ (hp.of_surjective (q.subgroupMap N) (q.subgroupMap_surjective N))
  have hC : pResidual 2 (Hdot F F.uhatAction) ≤ centralizer (N.map q : Set (Hdot F F.uhatAction)) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm
      (⟨y,hN hy⟩ : pResidual 2 (Hdot F F.uhatAction)) ⟨x,hx⟩)
  change (N.map q).Normal
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top S]
  exact sup_le (hC.trans (Subgroup.centralizer_le_normalizer _)) hSN

/-- The solvable marked source row excludes the central LT seed. No normality,
kernel-comparison, splitting or local-exclusion callback remains in this result. -/
theorem source_seed_exclusion_of_symmetricThreePair (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    centralLTSeed F L = ⊥ :=
  source_seed_exclusion_of_solvable_row d earlier hq chosen structural alternatives F hne
    g hgP hgH row (source_dot_Li_one_normal_of_symmetricThreePair d earlier hq chosen structural F model)

/-- Apply the solved solvable seed branch to the literal Thompson containment
used in the Goldschmidt paragraph of 14.3.31. -/
theorem source_symmetricThreePair_thompson_le_plane_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  source_contrary_thompson_le_plane_core d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_symmetricThreePair d earlier hq chosen structural alternatives F hne
      g hgP hgH row model) hI

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
