module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Quotients
public import Theory.SpecificGroups.AlternatingSix.SylowParabolicAction
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Recovery of the full quotient in the alternating-six branch

Pass the actual normal component through the ambient two-core quotient.
The original S₃ point parabolic has Sylow index three, so its intersection
with the component is an order-24 parabolic. The checked four-group action
calculation forces the whole conjugation image into the natural S₆.
The component and the Sylow subgroup generate, so the conjugation kernel
is a two-group and is trivial in the core-free quotient. The image contains
Inn(A₆), leaving precisely the actual A₆ and S₆ quotient models.

The source application retains the original subgroupOf and quotient maps
and uses same-G,T 12.2.2. It discharges the Dynkin-action step in original
14.7.49; the 14.7.11 exclusion of these full quotients remains separate.
Source: Aschbacher–Smith, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
variable {X : Type*} [Group X] [Finite X]

private theorem natural_inner_overgroup (R : Subgroup AutA6)
    (hi : AlternatingSix.ShadowLocal.inner ≤ R) (hn : R ≤ natural) : R = AlternatingSix.ShadowLocal.inner ∨ R = natural := by
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup AutA6) AlternatingSix.ShadowLocal.inner natural bot_le inner_le_natural
  rw [relIndex_bot_left,relIndex_bot_left,card_inner,card_natural] at hmul
  have htwo : AlternatingSix.ShadowLocal.inner.relIndex natural = 2 := by omega
  have hprod := relIndex_mul_relIndex AlternatingSix.ShadowLocal.inner R natural hi hn
  rw [htwo] at hprod
  rcases (Nat.dvd_prime Nat.prime_two).mp (dvd_of_mul_right_eq _ hprod) with h | h
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp h) hi)
  · have he : R.relIndex natural = 1 := by rw [h] at hprod; omega
    exact Or.inr (le_antisymm hn (relIndex_eq_one.mp he))

private theorem coreFree (hcore : pCore 2 X = ⊥)
    (N : Subgroup X) [N.Normal] (e : N ≃* A6)
    (S : Sylow 2 X) (hgen : N ⊔ (S : Subgroup X) = ⊤)
    (B : Subgroup X) (hSB : (S : Subgroup X) ≤ B)
    (hi : (S : Subgroup X).relIndex B = 3) :
    Nonempty (X ≃* A6) ∨ Nonempty (X ≃* Equiv.Perm (Fin 6)) := by
  let f := conjugationAction N e
  have hfN : f.comp N.subtype = (MulAut.conj : A6 →* AutA6).comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact conjugationAction_on_inner N e x
  have hkerN : (f.comp N.subtype).ker = ⊥ := by
    apply (MonoidHom.ker_eq_bot_iff _).mpr
    rw [hfN]
    exact inner_injective.comp e.injective
  have hk : IsPGroup 2 f.ker := f.kernel_isPGroup_of_normal_supplement N S S.isPGroup' hgen
    (by rw [hkerN]; exact IsPGroup.of_subsingleton 2 _)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique ((show f.ker ≤ pCore 2 X from le_sSup ⟨inferInstance,hk⟩).trans hcore.le)
  have hin : AlternatingSix.ShadowLocal.inner ≤ f.range := by
    rw [←conjugationAction_map_inner N e]
    exact map_le_range _ _
  have hn := AlternatingSix.SylowParabolicAction.parabolic_natural N e S B hSB hgen hi
  rcases natural_inner_overgroup f.range hin hn with hr | hr
  · exact Or.inl ⟨(MonoidHom.ofInjective hf).trans
      ((MulEquiv.subgroupCongr hr).trans innerEquiv.symm)⟩
  · exact Or.inr ⟨(MonoidHom.ofInjective hf).trans
      ((MulEquiv.subgroupCongr hr).trans
        GLS3.Chapter5.permSixMulEquivNaturalAlternatingAutomorphisms.symm)⟩

private theorem alternatingSix_normal_quotient (N : Subgroup X) [N.Normal]
    (e : (N ⧸ pCore 2 N) ≃* A6)
    (S : Sylow 2 X) (hgen : N ⊔ (S : Subgroup X) = ⊤)
    (B : Subgroup X) (hSB : (S : Subgroup X) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    Nonempty ((X ⧸ pCore 2 X) ≃* A6) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 6)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let C := N.map q
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let c : C ≃* A6 :=
    ((Normal.isSubnormal (inferInstance : N.Normal)).quotientCoreImageEquiv 2).symm.trans e
  have hgen' : C ⊔ (S' : Subgroup _) = ⊤ := by
    change N.map q ⊔ (S : Subgroup X).map q = ⊤
    rw [←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map,
      q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _)]
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcore : pCore 2 (X ⧸ pCore 2 X) = ⊥ := by
    apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 X))
    rw [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hqker,
      MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have hker : q.ker ≤ (S : Subgroup X) := hqker.le_sylow_of_normal S
  have hi : (S' : Subgroup _).relIndex (B.map q) = 3 := by
    change ((S : Subgroup X).map q).relIndex (B.map q) = 3
    rw [relIndex_map_map, sup_eq_left.mpr hker, sup_eq_left.mpr (hker.trans hSB)]
    exact SymmetricThreeTwoCore.sylow_index_three eB (S.subtype hSB)
  exact coreFree hcore C c S' hgen' (B.map q) (map_mono hSB) hi
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual original point parabolic excludes the nonnatural A₆
extensions: the full local quotient is A₆ or S₆. -/
theorem alternatingSix_full_quotient_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hn : (K.subgroupOf I).Normal)
    (hgen : I = K ⊔ (T : Subgroup G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6)) := by
  let := hn
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hBI : B ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  let e := subgroupOfEquivOfLe hKI
  let eN := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eK
  let b := subgroupOfEquivOfLe hBI
  let eB := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (pointQuotientEquiv_at h structural)
  apply alternatingSix_normal_quotient
    (K.subgroupOf I) eN (T.subtype (F.sylow_le_of_mem_Hz hI)) ?_ (B.subgroupOf I) ?_ eB
  · rw [Sylow.coe_subtype, ←subgroupOf_sup hKI (F.sylow_le_of_mem_Hz hI), ←hgen,
      subgroupOf_self]
  · exact subgroupOf_mono I le_sup_right

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
