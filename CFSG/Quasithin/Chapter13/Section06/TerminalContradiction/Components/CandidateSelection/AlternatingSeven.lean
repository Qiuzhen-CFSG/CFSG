module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.AlternatingCoreGeneration
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.KnownSimple
public import CFSG.Quasithin.MainForward.SourceReduction
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Stellmacher.OmegaOneCenterMap

/-!
# Excluding the A₇ seed in source 13.6.27

A subgroup K of C_G(Ω₁(Z(T))) has KT in H(T): the nontrivial central
omega subgroup lies in O₂(KT). If K lies outside M, the original A₅
source setup gives n(KT) > 1 by 13.6.25. For a T-normalized K with
K/O₂(K) ≃ A₇, the actual quotient-action generation theorem gives
n(KT) ≤ 1, a contradiction.

The final theorem applies this to the literal centralizer component KZ
supplied by 5.2.3. Its ambient image contains the selected residual outside
M. The quotient is transported through that exact inclusion; only the
seed's T-normalization remains with the candidate-selection owner.

Source: Aschbacher–Smith, 13.6.27, printed p.934, using 13.6.25(2)
and E.1.14(3), p.214.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
open ChapterE
open SourceParameters
variable {G : Type*} [Group G] [Finite G]

private theorem centralOmega_nontrivial (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr (MainForward.sylow_ne_bot hG T)
  have hn := Subgroup.omega_center_ne_bot T.isPGroup'
  intro he
  apply hn
  apply Subgroup.map_injective (f := (T : Subgroup G).subtype) (T : Subgroup G).subtype_injective
  simpa only [Stellmacher.omegaOneCenterAmbient, Subgroup.map_bot] using he

/-- A subgroup of the actual central-omega centralizer has a local join with T. -/
theorem centralizer_join_mem_HOver
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (K : Subgroup G)
    (hKC : K ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hZ : Z ≠ ⊥ := centralOmega_nontrivial hG T
  have hZT : Z ≤ (T : Subgroup G) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hTC : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  have hc : Z ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
    let := Stellmacher.omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 Z)
      (hZT.trans le_sup_right) ((sup_le hKC hTC).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨?_, show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right⟩
  intro hzero
  exact hZ (bot_unique (hc.trans_eq hzero))

/-- Source 13.6.25 excludes an A₇ quotient for every T-normalized seed
outside M in C_G(Ω₁(Z(T))). -/
theorem not_alternatingSeven_of_A5_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (K : Subgroup G)
    (hKC : K ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) (hKM : ¬ K ≤ M) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  have hout : K ⊔ (T : Subgroup G) ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨centralizer_join_mem_HOver hG T K hKC, fun h => hKM (le_sup_left.trans h)⟩
  have hgt := (source_13_6_25_knownSimple hG s).2.1 _ hout
  exact (not_lt_of_ge (generationParameter_le_one_of_alternatingSeven_quotient K T hn e)) hgt

/-- Exclude A₇ for the literal centralizer component supplied by 5.2.3.
Its ambient image contains the original residual outside M. -/
theorem source523_seed_not_alternatingSeven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (H : Subgroup G)
    (hres : ¬ (pResidual 2 H).map H.subtype ≤ M)
    (KZ : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)))
    (hcontains : (pResidual 2 H).map H.subtype ≤ KZ.map
      (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype)
    (hn : (T : Subgroup G) ≤ normalizer (KZ.map
      (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype : Set G)) :
    ¬ Nonempty ((KZ ⧸ pCore 2 KZ) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  let C := centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let f := KZ.equivMapOfInjective C.subtype C.subtype_injective
  let eq := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  exact not_alternatingSeven_of_A5_setup hG s (KZ.map C.subtype)
    (map_subtype_le _) hn (fun h => hres (hcontains.trans h)) ⟨eq.symm.trans e⟩
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
