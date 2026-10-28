module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.TerminalProducts
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CentralKernelElimination

/-!
# The full block centralizer fixes the conjugate total module

The genuine total mutual supplement leaves only a single Ui-commutator
when evaluated on Vi. Its membership in C(Ki) makes it trivial by the
fixed-vector lifting theorem. Both original blocks are treated using the
actual four-module cross commutators.

Source: Aschbacher–Smith, C.5.6(7), printed p.160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
variable {F F' : Type*} [Field F] [Field F']

theorem Setup.two_block_full_centralizer_centralizes
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : (∃ n, IsL2EvenBlock L n) →
      ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S R ⊓ L)
    (M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    R ⊓ centralizer (K ⊔ L : Subgroup G) ≤
      centralizer ((U K ⊔ U L : Subgroup G).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  let U₀ := U K ⊔ U L
  let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
  let V₁ := (U K).conjBy x⁻¹
  let V₂ := (U L).conjBy x⁻¹
  let P' := R ⊓ centralizer (V : Set G)
  let C := R ⊓ centralizer (K ⊔ L : Subgroup G)
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hcross := FourModuleOrbit.cross_commutators hi.toInputs
  have hV₁V : V₁ ≤ V := map_mono (show U K ≤ U₀ from le_sup_left)
  have hV₂V : V₂ ≤ V := map_mono (show U L ≤ U₀ from le_sup_right)
  have hPN : P' ≤ normalizer (U₀ : Set G) := by
    intro r hr
    have hh : r ∈ M ⊓ normalizer (FourModuleOrbit.modules (U K) (U L) x 2 : Set G) :=
      ⟨hTHM (hRTH hr.1),Subgroup.centralizer_le_normalizer _ (centralizer_le hV₁V hr.2)⟩
    have hn1 : r ∈ normalizer (U K : Set G) := ((hi.normalizers_eq 2 0) ▸ hh).2
    have hn2 : r ∈ normalizer (U L : Set G) := ((hi.normalizers_eq 2 1) ▸ hh).2
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp hn1,mem_normalizer_iff_map_conj_eq.mp hn2]
  have hCU : C ≤ R ⊓ centralizer (U₀ : Set G) := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (sup_le_sup (map_subtype_le _) (map_subtype_le _))))
  have hmut := h.two_block_mutual_centralizers h' hR hKL hSylow hSylow' M T_H hRTH hTHM
    x hx hxR hindex hpair ht hnc
  have hCP : C ≤ U₀ ⊔ P' := hCU.trans hmut.2
  have hc1 : C ≤ centralizer (V₁ : Set G) := h.centralizer_centralizes_of_supplement hxR
    (U L) P' C
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross.1))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross.2.2.1))
    (inf_le_right.trans (centralizer_le hV₁V)) hPN
    (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left))) hCP
  have hc2 : C ≤ centralizer (V₂ : Set G) := h'.centralizer_centralizes_of_supplement hxR
    (U K) P' C
    (commutator_eq_bot_iff_le_centralizer.mp hcross.1)
    (commutator_eq_bot_iff_le_centralizer.mp hcross.2.1)
    (inf_le_right.trans (centralizer_le hV₂V))
    (by simpa only [sup_comm] using hPN)
    (inf_le_right.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right)))
    (by simpa only [U₀,sup_comm] using hCP)
  change C ≤ centralizer (V : Set G)
  apply le_centralizer_iff.mpr
  change (U K ⊔ U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (C : Set G)
  rw [Subgroup.map_sup]
  exact sup_le (le_centralizer_iff.mp hc1) (le_centralizer_iff.mp hc2)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
