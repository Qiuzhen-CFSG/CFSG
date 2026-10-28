module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.PrimeMovement
public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow

/-!
# Excluding the moving component and recovering the ambient Sylow

The swapping involution fixes a diagonal copy of the component. Its join
with the actor stabilizer has trivial two-core and acts faithfully on the
involution's fixed space. At most one further dimension can be moved there,
so this diagonal action has cubic ratio at most two. The proved odd-prime
cubic barrier gives the contradiction.

The final application excludes the actual contrary ambient Sylow branch of
12.1.4. It retains the exact fixed-subgroup consequence owed by the original
MS argument; `qt-rank-two-ms93` supplies its source specialization and
`qt-d-double-natural-centralizers` retains final discharge. No universal MS
classification or dimension-four weak-closure premise is used.
Source: Aschbacher--Smith D.3.5--9 and 12.1.4,
printed pp.195--201,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The component stabilizer inside the centralizer of a swapping involution
contains a self-centralizing normal copy of the original component. -/
theorem swapped_diagonal_local_structure
    {Q : Type*} [Group Q] [Finite Q] (C B : Subgroup Q)
    (hC : IsComponent Q C) [IsSimpleGroup C]
    {a : Q} (hm : C.map (MulAut.conj a).toMonoidHom ≠ C) (ha : a ^ 2 = 1)
    (hBN : B ≤ normalizer (C : Set Q)) (hBa : B ≤ centralizer ({a} : Set Q))
    (hcent : centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) = ⊥) :
    let D := NormPair.normRange hC hm
    let H := D ⊔ B
    H ≤ centralizer ({a} : Set Q) ∧ (D.subgroupOf H).Normal ∧
      centralizer (D.subgroupOf H : Set H) = ⊥ ∧
      Nonempty (C ≃* D.subgroupOf H) ∧ pCore 2 H = ⊥ := by
  let D := NormPair.normRange hC hm
  let H := D ⊔ B
  have hDH : D ≤ H := le_sup_left
  have hDa : D ≤ centralizer ({a} : Set Q) := componentSwapNorm_range_le_centralizer hC hm ha
  have hHa : H ≤ centralizer ({a} : Set Q) := sup_le hDa hBa
  have hBD : B ≤ normalizer (D : Set Q) := fun b hb =>
    NormPair.normalizes_norm hC hm (mem_centralizer_singleton_iff.mp (hBa hb)) (hBN hb)
  let : (D.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hBD)
  have hCaC : C.map (MulAut.conj a).toMonoidHom ≤ centralizer (C : Set Q) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hC.map_conj a).commutator_eq_bot_of_ne hC hm)
  have hHN : H ≤ normalizer (C : Set Q) := sup_le
    ((NormPair.norm_le_pair hC hm).trans
      (sup_le C.le_normalizer (hCaC.trans (Subgroup.centralizer_le_normalizer _)))) hBN
  have hcD : centralizer (D.subgroupOf H : Set H) = ⊥ := by
    apply bot_unique
    intro b hb
    have hbD : (b : Q) ∈ centralizer (D : Set Q) := by
      intro d hd
      exact congrArg Subtype.val (hb ⟨d,hDH hd⟩ hd)
    have hba : Commute (b : Q) a := mem_centralizer_singleton_iff.mp (hHa b.property)
    have hbC := NormPair.centralizes_norm_normalizes_component hC hm hba (hHN b.property) hbD
    have hbCa : (b : Q) ∈ centralizer (C.map (MulAut.conj a).toMonoidHom : Set Q) := by
      rintro _ ⟨c,hc,rfl⟩
      have hbc : Commute (b : Q) c := (hbC c hc).symm
      exact ((hba.mul_right hbc).mul_right hba.inv_right).eq.symm
    have hh : (b : Q) ∈ centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) := by
      have hh : C ⊔ C.map (MulAut.conj a).toMonoidHom ≤ centralizer ({(b : Q)} : Set Q) :=
        sup_le (fun c hc => mem_centralizer_singleton_iff.mpr (hbC c hc))
          (fun c hc => mem_centralizer_singleton_iff.mpr (hbCa c hc))
      exact fun c hc => mem_centralizer_singleton_iff.mp (hh hc)
    exact Subtype.ext (mem_bot.mp (hcent ▸ hh))
  let e : C ≃* D.subgroupOf H :=
    (NormPair.normEquivOfSimple hC hm).trans (subgroupOfEquivOfLe hDH).symm
  let := hC.2
  let : IsQuasisimple (D.subgroupOf H) := IsQuasisimple.of_mulEquiv e
  have hD : IsComponent H (D.subgroupOf H) :=
    ⟨(inferInstance : (D.subgroupOf H).Normal).isSubnormal,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hcore : pCore 2 H = ⊥ := bot_unique
    ((le_centralizer_iff.mp (hD.le_centralizer_of_solvable_normal (pCore 2 H))).trans hcD.le)
  exact ⟨hHa,inferInstance,hcD,⟨e⟩,hcore⟩

/-- Restriction to a swapping involution's fixed space is faithful on a
commuting subgroup with trivial two-core. -/
theorem faithful_involution_fixed_action
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (H : Subgroup Q) {a : Q} (ha : a ^ 2 = 1)
    (hHa : H ≤ centralizer ({a} : Set Q)) (hcore : pCore 2 H = ⊥) :
    ∃ σ : Representation (ZMod 2) H (fixedSpace ρ (zpowers a)),
      Function.Injective σ ∧ ∀ (h : H) (v : fixedSpace ρ (zpowers a)),
        (σ h v : U) = ρ (h : Q) v := by
  let W := fixedSpace ρ (zpowers a)
  have hHW : H ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro h hh v hv
    rw [mem_fixedSpace_zpowers_iff] at hv ⊢
    have hc := (mem_centralizer_singleton_iff.mp (hHa hh)).symm
    rw [←Module.End.mul_apply,←map_mul,hc,map_mul,Module.End.mul_apply,hv]
  let σ := (invariantSubspace ρ H W hHW).toRepresentation
  let N := σ.ker.map H.subtype
  let : IsElementaryAbelian 2 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one ha
  have hp : IsPGroup 2 N := by
    apply isPGroup_of_commuting_fixes_fixedSpace ρ hf (zpowers a) N
      (IsElementaryAbelian.isPGroup 2 (zpowers a))
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      apply zpowers_le.mpr
      intro n hn
      exact mem_centralizer_singleton_iff.mp (hHa ((map_subtype_le σ.ker) hn))
    · rintro _ ⟨n,hn,rfl⟩
      refine ⟨mem_top _,?_⟩
      intro v hv
      exact congrArg Subtype.val (LinearMap.congr_fun hn (⟨v,hv⟩ : W))
  have hk : IsPGroup 2 σ.ker := hp.of_injective
    (H.subtype.subgroupMap σ.ker) (by
      intro x y hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N => (z : Q)) hh)
  have hkbot : σ.ker = ⊥ := bot_unique
    ((show σ.ker ≤ pCore 2 H from le_sSup ⟨inferInstance,hk⟩).trans hcore.le)
  exact ⟨σ,σ.ker_eq_bot_iff.mp hkbot,fun _ _ => rfl⟩

/-- The moving actor is impossible: its diagonal almost-simple section on
C_U(a) has cubic ratio at most two, contradicting the odd-prime barrier. -/
theorem no_small_moving_cubic_actor_pair
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q)
    (C C' : Subgroup Q) (hC : IsComponent Q C) [IsSimpleGroup C]
    (hcent : centralizer ((C ⊔ C' : Subgroup Q) : Set Q) = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmC : ClassicalGroup.IsPSL C 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    ¬ SmallMovingCubicActorPair ρ C C' := by
  intro hs
  obtain ⟨_,E,hE,_,hrB,hd,_,a,ha,ha2,han,hmap,hlo,_⟩ :=
    small_mover_prime_and_rank ρ hf C C' hC hs hp ho hmC hmod
  let B := E ⊓ normalizer (C : Set Q)
  let := hE.1.2.1.2
  let := hC.2
  have hm : C.map (MulAut.conj a).toMonoidHom ≠ C :=
    fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  have hpair : centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) = ⊥ := by
    rwa [hmap]
  have hBa : B ≤ centralizer ({a} : Set Q) := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm
      (⟨b,hb.1⟩ : E) ⟨a,ha⟩)
  have hasq : a ^ 2 = 1 := ha2 ▸ pow_orderOf_eq_one a
  obtain ⟨hHa,hnD,hcentD,⟨e⟩,hcore⟩ :=
    swapped_diagonal_local_structure C B hC hm hasq inf_le_right hBa hpair
  let D := NormPair.normRange hC hm
  let H := D ⊔ B
  let D₀ := D.subgroupOf H
  let B₀ := B.subgroupOf H
  have hBH : B ≤ H := le_sup_right
  let : D₀.Normal := hnD
  let : IsQuasisimple D₀ := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup D₀ := e.symm.isSimpleGroup
  let W := fixedSpace ρ (zpowers a)
  obtain ⟨σ,hσ,hact⟩ := faithful_involution_fixed_action ρ hf H hasq hHa hcore
  have hBn : B ≠ ⊥ := by
    intro hz
    change rank B = 2 at hrB
    rw [hz,Representation.BinaryOffender.rank_bot] at hrB
    omega
  have hB : IsElementaryTwo B := hE.1.2.1.of_le inf_le_left hBn
  let := hB.2
  have hB₀ : IsElementaryTwo B₀ := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hBH⟩
    intro hz
    exact hBn (by rw [←map_subgroupOf_eq_of_le hBH,show B.subgroupOf H = ⊥ from hz,Subgroup.map_bot])
  have hEW : fixedSpace ρ E ≤ W := fixedSpace_antitone ρ (zpowers_le.mpr ha)
  have hkeep : (fixedSpace ρ E).comap W.subtype ≤ fixedSpace σ B₀ := by
    intro v hv b
    apply Subtype.ext
    change (σ (b : H) v : U) = (v : U)
    rw [hact]
    exact hv ⟨((b : H) : Q),b.property.1⟩
  have hlow := Submodule.finrank_mono hkeep
  rw [(Submodule.comapSubtypeEquivOfLe hEW).finrank_eq] at hlow
  have hdimE := fixedCodim_add_finrank ρ E
  have hdima := fixedCodim_add_finrank ρ (zpowers a)
  have hdimB := fixedCodim_add_finrank σ B₀
  have hsmall : fixedCodim σ B₀ ≤ 1 := by
    change fixedCodim σ B₀ + Module.finrank (ZMod 2) (fixedSpace σ B₀) =
      Module.finrank (ZMod 2) W at hdimB
    change fixedCodim ρ (zpowers a) + Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) U at hdima
    change Module.finrank (ZMod 2) (fixedSpace ρ E) ≤
      Module.finrank (ZMod 2) (fixedSpace σ B₀) at hlow
    omega
  have hdisp (g : H) (v : W) :
      ((displacement σ g v : W) : U) = displacement ρ (g : Q) (v : U) := by
    change ((σ g v : W) : U) - v = ρ (g : Q) v - v
    rw [hact]
  have hcσ : IsCubic σ B₀ := by
    intro b hb c hc d hd v
    apply Subtype.ext
    simpa only [hdisp,Submodule.coe_zero] using
      hE.1.2.2.1 (b : Q) hb.1 (c : Q) hc.1 (d : Q) hd.1 (v : U)
  have hσc : cubicRatio σ ≤ 2 := (cubicRatio_le_nat_iff σ 2).mpr
    ⟨B₀,hB₀,hcσ,by have := hB₀.rank_pos; omega⟩
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hmC
  have hmD : ClassicalGroup.IsPSL D₀ 2 p :=
    ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans eF⟩⟩
  exact (not_lt_of_ge hσc) (normal_rank_one_cubic_barrier σ hσ (hsq.subgroup H)
    D₀ hcentD hp ho hmD hmod)

/-- The original quotient pair cannot support the common cubic actor.
The pair centralizer and SQTK hypotheses use the literal two-core quotient. -/
theorem no_local_quotient_common_cubic_actor
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) U)
    (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient (localJoin T L)))
    (C : Subgroup (XiQuotient (localJoin T L))) (t : localJoin T L)
    (hne : C ≠ C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom)
    (hnorm : (C ⊔ C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom).Normal)
    (hpair : C ⊔ C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom =
      ((localOrbit T L).subgroupOf (localJoin T L)).map (QuotientGroup.mk' (pCore 2 (localJoin T L))))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    ¬ CommonCubicActorPair ρ C
      (C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom) (XiQuotient L) := by
  intro hactor
  have hsmall := local_quotient_small_moving_actor ρ C t hne hnorm hpair hactor hp hm (by omega)
  obtain ⟨_,_,_,hCs⟩ := hactor
  let H := localJoin T L
  let q := QuotientGroup.mk' (pCore 2 H)
  let C' := C.map (MulAut.conj (q t)).toMonoidHom
  have h₁ := hCs C (by simp)
  have h₂ := hCs C' (by simp [C',q,H])
  let : IsSimpleGroup C := h₁.2.1.some.isSimpleGroup
  let : IsSimpleGroup C' := h₂.2.1.some.isSimpleGroup
  let := hnorm
  let S := ((T : Subgroup G).subgroupOf H).map q
  have hS : IsPGroup 2 S := (T.isPGroup'.comap_subtype).map q
  have hgen : (C ⊔ C') ⊔ S = ⊤ := by
    rw [hpair,←Subgroup.map_sup,←subgroupOf_sup
      (show localOrbit T L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot := isPGroup_quotient_of_sup_eq_top (C ⊔ C') S hS hgen
  have hcent := small_pair_centralizer_eq_bot C C' h₁.1 h₂.1 hne hquot
    (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hmC : ClassicalGroup.IsPSL C 2 p :=
    ⟨F,inferInstance,inferInstance,hF,⟨h₁.2.1.some.trans e⟩⟩
  exact no_small_moving_cubic_actor_pair ρ hf hsq C C' h₁.1 hcent hp ho hmC hmod hsmall


end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open Chapter3.Section02 Representation.BinaryOffender.Homogeneous
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The original marked point has its full ambient Sylow under the precise
fixed-subgroup consequence still owed by the source MS argument. -/
theorem doubleNatural_four_marked_pure_sylow_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      (¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
        omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥) →
      IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hfixed
  by_contra hf
  obtain ⟨P,A,K,F,hs,_,_,hodd,_,_,ρ,hρ,_,_,_,_,
      t,_,_,hneK,hnK,hpair,hactor⟩ :=
    D.doubleNatural_four_pure_common_cubic_actor_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf (hfixed hf)
  obtain ⟨_,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hs.toSwappedInput
  let : IsSimpleGroup (XiQuotient K) :=
    SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  have hJH : localJoin T K ≤ (P : Subgroup G) ⊔ (PureFourXi.residual T L ⊔ (T : Subgroup G)) :=
    sup_le (SwappedSylow.orbit_le_overgroup hs.toSwappedInput)
      (le_sup_right.trans hs.overgroup)
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (localJoin T K) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp (hs.sqtk.subgroup _)
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (XiQuotient (localJoin T K)) :=
    ⟨quotient_stronglyQuasithin hsqJ.stronglyQuasithin,hsqJ.isKGroup.quotient _⟩
  obtain ⟨p,hp',ho,hm,_,h24⟩ := hodd
  let := F.module_elementary
  exact PureFourXi.no_local_quotient_common_cubic_actor ρ hρ hsqQ _ t hneK hnK hpair hp' ho hm h24 hactor


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
