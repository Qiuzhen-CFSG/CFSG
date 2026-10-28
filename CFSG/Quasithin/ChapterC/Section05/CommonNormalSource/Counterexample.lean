module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.MarkedPair
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OmegaSpan
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalOriginalControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AlternatingOriginalControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.G6ControlSource

/-!
# The original C.5.8 counterexample is impossible

The C.5.3 orbit, original C.5.4 markings, C.5.6 Sylow replacement and the
diagonal omega-center span now supply every input of the literal C.5.9–12
terminal. Each of the natural, A₃ and A₅ cases contradicts the original
noncommuting conjugate. Only genuine earlier classification implications
remain: the outside-block source, A.3.12, and normalized-cubic G.6.
No reduced configuration or desired normalizer conclusion is assumed.

Source: Aschbacher–Smith C.5.8–13, printed pp.160–163.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource
universe u
variable {G : Type u} [Group G] [Finite G] {H M K R T : Subgroup G}

omit [Finite G] in
private theorem H_ne_bot (d : OriginalHypotheses H M K R T) : H ≠ ⊥ := by
  intro he
  subst H
  exact d.unique.1.ne (Subsingleton.elim _ _)

omit [Finite G] in
private theorem commuting_blocks
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i j : Fin b.size) (hij : i ≠ j) :
    (b.block i).map H.subtype ≤ centralizer ((b.block j).map H.subtype : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute hij),Subgroup.map_bot]

theorem OriginalHypotheses.counterexample_false
    (d : OriginalHypotheses H M K R T) {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (outside : C128Outside 𝒦)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (hG6 : ChapterG.Section06.NormalizedCubicSourceInput.{u,u} 𝒦)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) : False := by
  have hHsqtk := CounterexampleCharacteristic.sqtk_of_mem_He hG H d.mem_He (H_ne_bot d)
  obtain ⟨b,hs,i,hhalf,x,hx,hxT,hxs,hnc⟩ :=
    d.exists_source_sylow_replacement outside hHsqtk P hP
  have hi := i.isLt
  let j : Fin b.size := ⟨1-i.val,by omega⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [j] at hv
    omega
  let Ki := (b.block i).map H.subtype
  let Kj := (b.block j).map H.subtype
  let T₁ := T ⊓ normalizer (ambientModule (b.block i) : Set G)
  have hu : RankOne.U Ki = ambientModule (b.block i) := (ambientModule_eq_literal _).symm
  have hH : H = (Ki ⊔ Kj) ⊔ (P : Subgroup G) := by
    rw [hP,d.pair_join b i j hij hs,d.residual_sup_sylow]
  have hT₁ : T₁ = (P : Subgroup G) ⊓ normalizer (RankOne.U Ki : Set G) := by rw [hP,hu]
  have hncU : ¬ (RankOne.U Ki).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (RankOne.U Ki : Set G) := hu.symm ▸ hnc
  have hcore : H.pCoreIn 2 ≤ centralizer (RankOne.U Ki : Set G) := hu.symm ▸ d.core_centralizes_module b i
  have hnk : T₁ ≤ normalizer (Ki : Set G) := d.module_stabilizer_le_block_normalizer b i
  have hU : RankOne.U Ki ≤ conjugateSpanBy (omegaOneCenterAmbient (P : Subgroup G)) H := by
    rw [hP,hu]
    exact d.module_le_omega_span b i
  obtain ⟨t,ht,hout,htK⟩ := d.pair_exchange b i j hij
  have hKL : Kj ≤ centralizer (Ki : Set G) := commuting_blocks d b j i (Ne.symm hij)
  have hpair : ∀ g ∈ (P : Subgroup G), Ki.conjBy g = Ki ∨ Ki.conjBy g = Kj := by
    rw [hP]
    exact d.pair_action b i j hij hs
  have ht' : t ∈ (P : Subgroup G) := hP.symm ▸ ht
  have hh : T₁.relIndex (P : Subgroup G) = 2 := hP.symm ▸ hhalf
  have hm := chiZero_equiv (equivMapOfInjective (b.block i) H.subtype H.subtype_injective) (b.type i).2
  rcases hm with ⟨n,hn⟩ | ha | ha
  · obtain ⟨F,F',_,_,⟨h⟩,⟨h'⟩⟩ := d.rankOne_paired_setups b i j (Or.inl ⟨n,hn⟩)
    exact NormalizerControl.natural_counterexample_false P hG hA312 H R Ki Kj T₁
      (hP.symm ▸ d.R_le) (hP.symm ▸ d.T_le.trans d.R_normal) h h' hn hKL hH d.mem_He
      hcore hT₁ hh hnk hU hpair t ht' hout htK x hxT (d.R_normal hx) hncU
  · obtain ⟨F,F',_,_,⟨h⟩,⟨h'⟩⟩ := d.rankOne_paired_setups b i j (Or.inr ha)
    exact NormalizerControl.alternating_three_counterexample_false_of_g6 P hG hG6 H R Ki Kj T₁
      (hP.symm ▸ d.R_le) (hP.symm ▸ d.T_le.trans d.R_normal) h ha h' hKL hH d.mem_He
      hcore hT₁ hh hnk hU hpair t ht' hout htK x hxT (d.R_normal hx) hncU
  · obtain ⟨⟨h⟩,⟨h'⟩⟩ := d.alternating_paired_setups b i j hij hs ha
    exact NormalizerControl.alternating_counterexample_false P hG hA312 H R Ki Kj T₁
      (hP.symm ▸ d.R_le) (hP.symm ▸ d.T_le.trans d.R_normal) h h' hH d.mem_He
      hcore hT₁ hh hnk hU hpair t ht' hout htK x hxT (d.R_normal hx) hncU

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
