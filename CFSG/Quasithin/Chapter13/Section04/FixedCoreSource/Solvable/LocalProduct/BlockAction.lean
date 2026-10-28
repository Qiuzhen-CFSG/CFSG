module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoreMovement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.PairQuotient
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SymmetricFour

/-!
# The terminal action contradiction in the A₆-block argument

Assume C_H(V_H) = O₂(H) for the actual H = C_G(z). If O₂,Z(L)
centralizes V_H, the marked C_L(z) action factors through its S₄ image.
The odd-prime rank bounds descend through this two-group kernel, and
A.1.26 kills the image of O₂(C_L(z)). Relative normality then makes
O₂(L₁) centralize V_H. In the ordinary A₆ row the checked nontrivial
commutator [[V,L₁],O₂(L₁)] consequently excludes [V,L₁] ≤ V_H.

This proves the final action contradiction in this kernel branch. The
block geometry must still establish the core-centralizer bound and the
moved-space containment under the centralizing Thompson alternative.
The larger-kernel branch and the remainder of 13.4.8–9 remain with
qt-d-1341-solvable-source; earlier-source discharge and final 13.4.1
assembly remain with qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.8, final paragraph of printed p.904.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory
open Chapter12.Section02 BinaryNaturalDual.VectorStabilizers Stellmacher
open Chapter14.Section03.FaithfulSource Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the two-core-kernel branch, the S₄ action and A.1.26 force the
 original residual two-core to centralize the actual centralizer module. -/
theorem firstCentralizerResidual_core_centralizes_orbit
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hLc : (centralCore L).map L.subtype ≤ centralizer (centralizerOmegaOrbit T z.val : Set G)) :
    (firstCentralizerResidual L z.val).pCoreIn 2 ≤
      centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  let H := centralizer ({z.val} : Set G)
  let C := L ⊓ H
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let t : C →* (H ⧸ centralizer (U : Set H)) := q.comp (inclusion inf_le_right)
  obtain ⟨f,hf,hk,_⟩ := component_centralizer_action D m z
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (m.coordinate z).toAdd =
        (m.coordinate z).toAdd := by
    intro h
    exact hzL ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) _).mp h))
  obtain ⟨e⟩ := BinaryPermutation.SixCoreResidualMovement.stabilizer_equiv _ hfix
  have hkt : f.ker ≤ t.ker := by
    rw [hk]
    intro c hc
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    apply Subtype.ext
    exact hLc (mem_map_of_mem L.subtype hc) v.val hv
  let d := f.liftOfSurjective hf ⟨t,hkt⟩
  have hd (c : C) : d (f c) = t c := MonoidHom.liftOfRightInverse_comp_apply ..
  have hsolvQ : Group.IsSolvable (H ⧸ centralizer (U : Set H)) := by
    let := hsolv
    infer_instance
  have hrank : ∀ (p : ℕ) [Fact p.Prime], Odd p →
      primeRank p (pCore p (H ⧸ centralizer (U : Set H))) ≤ 2 := by
    intro p _ hp
    apply (Theory.GroupTheory.primeRank_le_of_injective p (pCore p _).subtype Subtype.val_injective).trans
    rw [primeRank_congr p (QuotientGroup.quotientMulEquivOfEq hkernel)]
    apply (primeRank_quotient_le_of_isTwoGroup p hp _ pCore_isPGroup).trans
    exact (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      p Fact.out hp
  have hkill := ChapterA.RankActions.symmetricFour_twoCore_le_kernel
    hsolvQ hU.quotient_pCore_eq_bot hrank (d.comp e.symm.toMonoidHom)
  have hcS : pCore 2 (BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd) ≤
      d.ker := by
    intro s hs
    have he : e s ∈ pCore 2 (Equiv.Perm (Fin 4)) := by
      rw [← pCore_map_iso 2 e]
      exact mem_map_of_mem e.toMonoidHom hs
    have hh := hkill he
    simpa only [MonoidHom.mem_ker,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hh
  have hcC : pCore 2 C ≤ t.ker := by
    intro c hc
    have hfcore : (pCore 2 C).map f ≤
        pCore 2 (BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd) :=
      le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
    have hh := hcS (hfcore (mem_map_of_mem f hc))
    change d (f c) = 1 at hh
    rwa [hd] at hh
  intro b hb
  have hresN : C ≤ normalizer (firstCentralizerResidual L z.val : Set G) := by
    rw [firstCentralizerResidual_eq]
    exact C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))
  have hbC := pCoreIn_mono_of_normalizes (firstCentralizerResidual_le L z.val) hresN hb
  obtain ⟨c,hc,rfl⟩ := hbC
  have hh : (inclusion (inf_le_right : C ≤ H) c) ∈ centralizer (U : Set H) :=
    (QuotientGroup.eq_one_iff _).mp (hcC hc)
  intro v hv
  exact congrArg Subtype.val (hh ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)

/-- The literal moved three-space cannot lie in V_H under the core-centralizer
 conclusion used in the A₆-block argument. -/
theorem firstCentralizerResidual_moved_not_le_orbit
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hLc : L.pCoreIn 2 ≤ centralizer (centralizerOmegaOrbit T z.val : Set G)) :
    ¬ (⁅V,firstCentralizerResidual L z.val⁆ : Subgroup G) ≤ centralizerOmegaOrbit T z.val := by
  obtain ⟨e⟩ := ordinary
  have hc := centralCore_eq_twoCore_of_ordinary e
  have hcore : IsPGroup 2 (centralCore L) := hc ▸ pCore_isPGroup
  have hcentral := firstCentralizerResidual_core_centralizes_orbit h₀ D m z hz hzL
    hsolv hkernel (by simpa only [hc,pCoreIn] using hLc)
  intro hm
  apply firstCentralizerResidual_double_commutator_ne_bot D m hcore z hzL
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact hm.trans (le_centralizer_iff.mp hcentral)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
