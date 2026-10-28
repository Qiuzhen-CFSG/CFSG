module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitAssembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.SourceData
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Source parabolic and rank assembly

The source theorem on markings supplies the weight-four flag, the actual
S₃ quotient of K₂T, the ordinary A₆ quotient of L, both local core bounds,
and U₂=[U₂,L₂]≤U_L. The new adapters construct every subgroup and orbit
premise needed by dimension doubling. Dimensions of the actual quotient
orbit give group ranks six and eight, using the repository's primeRank.
The natural branch retains the source's barred LT≃S₆ hypothesis.

The local marking construction supplies compatible coordinates for
I₂/O₂(I₂) and V/V₂, including the images of L₂ and O₂(G₁).
`source_parabolic_conclusions` discharges that premise of the retained
conditional assembly. Only the exact universal earlier 13.7.6(3) and
13.5.4 implications remain inputs, as authorized by this source development.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6(1)–(3),(6) and the ranks in (4),(5), printed p.948 (PDF p.965).
The Steinberg and permutation-module assertions belong to Quotients.
-/

public section
open Subgroup Module BinaryPermutation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.SourceAssembly
open TransvectionRecognition EarlierCore RankDoubling RankDoubling.SourceAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The elementary source seed and abelian V_H make U_H elementary abelian. -/
theorem elementary_UH_of_abelian_VH {H V V₃ : Subgroup G}
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)] (h₃ : V₃ ≤ V) :
    IsElementaryAbelian 2 (Source.UH H V₃) := by
  let : IsMulCommutative (conjugateSpanBy V H) := ‹IsMulCommutative (Source.VH H V)›
  let : IsElementaryAbelian 2 (Source.VH H V) := RankDoubling.elementary_conjugateSpan V H
  have hle : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono h₃ le_rfl
  refine {
    toIsMulCommutative := IsMulCommutative.of_setLike_mul_comm
      (fun _ hx _ hy => setLike_mul_comm (hle hx) (hle hy))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x.val (hle x.property)

private theorem binary_rank_eq_finrank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : primeRank 2 A = finrank (ZMod 2) (Additive A) := by
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)).trans
      (by rw [Nat.card_zmod])
  apply le_antisymm
  · exact IsElementaryAbelian.primeRank_le_of_card_le A hc.le
  · let : IsElementaryAbelian 2 (⊤ : Subgroup A) := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) x.val) }
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup A)
      ((Nat.card_congr Subgroup.topEquiv.toEquiv).trans hc)

variable {H V V₁ V₂ V₃ : Subgroup G}
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Transport the constructed flag to the actual orbit, double its dimension,
and recover the group rank. Only the local S₃ marking remains explicit. -/
theorem source_dimension_alternatives_of_local_marking
    {T : Sylow 2 G} {L K : Subgroup G}
    (s : NaturalSetup T L V V₁ V₂ V₃) (earlier : Earlier1354 T L V)
    (hTH : (T : Subgroup G) ≤ H) (hHZ : H ≤ normalizer (V₁ : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hmark : Marking.MarkedParabolic K V₂ T ρ)
    (m : CompatibleMarking H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂)
      (localData_of_naturalSetup s earlier hTH hHZ ρ hρ)) :
    (finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 4 ∧
      finrank (ZMod 2) (W H V V₂ V₃ s.seed_le) = 2 ∧
      finrank (ZMod 2) (Additive (Uhat H V V₂)) = 4 ∧
      primeRank 2 (Source.U2 H V V₂) = 6) ∨
    (finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 5 ∧
      finrank (ZMod 2) (W H V V₂ V₃ s.seed_le) = 3 ∧
      finrank (ZMod 2) (Additive (Uhat H V V₂)) = 6 ∧
      primeRank 2 (Source.U2 H V V₂) = 8) := by
  let d := localData_of_naturalSetup s earlier hTH hHZ ρ hρ
  have hi : V₂.relIndex V₃ = 2 := flag_index_two s.plane_le_seed
    (by decide : (4 : ℕ) ≠ 0) s.flag_orders.2.1 s.flag_orders.2.2
  have hQ := (source_dimension_doubling_of_source_data H V V₂ V₃ V₁
    (localI L V₁ V₂) (localResidual L V₂) d m (seed_core_commutator s hTH) hi).2
  have hU := source_rank_reduction_of_source_data H V V₂ V₃ V₁
    (localI L V₁ V₂) (localResidual L V₂) d m (seed_core_commutator s hTH) hi
    s.flag_orders.2.1
  rw [← binary_rank_eq_finrank] at hU
  rcases orbitMarking_of_markedParabolic K T ρ hρ hmark with hn | hn
  · obtain ⟨n⟩ := hn
    have hW := MarkedOrbit.natural_finrank (V := V) s.line_le_plane
      s.plane_le_seed s.seed_le n
    have hdim : finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 4 :=
      n.equiv.finrank_eq.trans (by simpa using finrank_natural_even (Fin 6) (by decide))
    exact Or.inl ⟨hdim, hW, by simpa only [hW] using hQ, by simpa only [hW] using hU⟩
  · obtain ⟨n⟩ := hn
    have hW := MarkedOrbit.cover_finrank (V := V) s.line_le_plane
      s.plane_le_seed s.seed_le n
    have hdim : finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 5 :=
      n.equiv.finrank_eq.trans (by simpa using finrank_core (Fin 6))
    exact Or.inr ⟨hdim, hW, by simpa only [hW] using hQ, by simpa only [hW] using hU⟩

/-- Conditional assembly of the geometric, core and rank conclusions of 13.8.6.
The marked K₂ action and all local identities are constructed from the original
source inputs. The remaining `localMarking` construction must be discharged
before this conditional theorem can certify the source result. -/
theorem source_parabolic_conclusions_of_local_marking
    (T : Sylow 2 G) (L M K : Subgroup G)
    (s : Marking.StandingFlag T L V V₁ V₂ V₃)
    (natural : Marking.StandingNatural L V (le_sup_left.trans s.normalizes_V))
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (localResidual L V₁) T
      (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (earlier1354 : Earlier1354 T L V)
    (hH : H ∈ Source.Hz (localResidual L V₁) T (normalizer (V₁ : Set G)) M)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (hmodel :
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
        ∀ (k : Source.starImage H K) u,
          E (ρ k u) = alternatingNaturalRepresentation (Fin 6) (eK k) (E u)) ∨
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6),
        ∀ (k : Source.starImage H K) u,
          E (ρ k u) = alternatingCoreRepresentation (Fin 6) (eK k) (E u)))
    (localMarking : ∀ (_s : NaturalSetup T L V V₁ V₂ V₃)
      (d : LocalData H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂)),
      Nonempty (CompatibleMarking H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂) d)) :
    Marking.MarkedParabolic K V₂ T ρ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizer (V₂ : Set G) ≤ normalizer (localResidual L V₂ : Set G) ∧
      ⁅Source.K2 H V₂, localResidual L V₂⁆ ≤
        (Source.K2 H V₂).pCoreIn 2 ⊓ (localResidual L V₂).pCoreIn 2 ∧
      Source.U2 H V V₂ = ⁅Source.U2 H V V₂, localResidual L V₂⁆ ∧
      Source.U2 H V V₂ ≤ Source.UL L H V₃ ∧
      finrank (ZMod 2) (Additive (Uhat H V V₂)) =
        2 * finrank (ZMod 2) (W H V V₂ V₃ s.seed_le) ∧
      (primeRank 2 (Source.Utilde H V₃ V₁) = 4 →
        Nonempty ((TransvectionQuotients.FiveSeed.toBar
          (L ⊔ (T : Subgroup G)) V s.normalizes_V).range ≃* Equiv.Perm (Fin 6)) →
        primeRank 2 (Source.U2 H V V₂) = 6) ∧
      (primeRank 2 (Source.Utilde H V₃ V₁) = 5 →
        primeRank 2 (Source.U2 H V V₂) = 8) := by
  obtain ⟨hL, _, _, hmark, _, _, hI, hres, _, _, _, _, hcore, hcomm, hUL⟩ :=
    Marking.source_marking_and_core T L V V₁ V₂ V₃ M H K s natural earlier1376
      earlier1354 hH hK hprod ρ hρ eK hmodel
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    change t ∈ (H : Set G)
    rw [hprod]
    exact ⟨1, K.one_mem, t, ht, one_mul t⟩
  let n := (s.componentSetup (Marking.standing_natural_earlier natural) hL).extend
  let d := localData_of_naturalSetup n earlier1354 hTH hH.2.1 ρ hρ
  obtain ⟨m⟩ := localMarking n d
  have hd := source_dimension_alternatives_of_local_marking n earlier1354 hTH hH.2.1 ρ hρ hmark m
  refine ⟨hmark, hL, local_normality _ _ _ _ hI hres.symm, hcore, hcomm, hUL, ?_, ?_, ?_⟩
  · exact (source_dimension_doubling_of_source_data H V V₂ V₃ V₁
      (localI L V₁ V₂) (localResidual L V₂) d m (seed_core_commutator n hTH)
      (flag_index_two s.plane_le_seed (by decide : (4 : ℕ) ≠ 0)
        s.orders.2.1 s.orders.2.2)).2
  · intro hdim _
    rw [binary_rank_eq_finrank] at hdim
    rcases hd with hd | hd
    · exact hd.2.2.2
    · omega
  · intro hdim
    rw [binary_rank_eq_finrank] at hdim
    rcases hd with hd | hd
    · omega
    · exact hd.2.2.2

/-- The geometric, core and rank conclusions of 13.8.6 from the original
source module hypotheses and the permitted earlier source implications.
The compatible local quotient and seed coordinates are constructed from
the natural setup and the proved earlier identities; no marking, orbit
dimension, dimension-doubling formula or numerical rank is assumed. -/
theorem source_parabolic_conclusions
    (T : Sylow 2 G) (L M K : Subgroup G)
    (s : Marking.StandingFlag T L V V₁ V₂ V₃)
    (natural : Marking.StandingNatural L V (le_sup_left.trans s.normalizes_V))
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (localResidual L V₁) T
      (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (earlier1354 : Earlier1354 T L V)
    (hH : H ∈ Source.Hz (localResidual L V₁) T (normalizer (V₁ : Set G)) M)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (hmodel :
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
        ∀ (k : Source.starImage H K) u,
          E (ρ k u) = alternatingNaturalRepresentation (Fin 6) (eK k) (E u)) ∨
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6),
        ∀ (k : Source.starImage H K) u,
          E (ρ k u) = alternatingCoreRepresentation (Fin 6) (eK k) (E u))) :
    Marking.MarkedParabolic K V₂ T ρ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizer (V₂ : Set G) ≤ normalizer (localResidual L V₂ : Set G) ∧
      ⁅Source.K2 H V₂, localResidual L V₂⁆ ≤
        (Source.K2 H V₂).pCoreIn 2 ⊓ (localResidual L V₂).pCoreIn 2 ∧
      Source.U2 H V V₂ = ⁅Source.U2 H V V₂, localResidual L V₂⁆ ∧
      Source.U2 H V V₂ ≤ Source.UL L H V₃ ∧
      finrank (ZMod 2) (Additive (Uhat H V V₂)) =
        2 * finrank (ZMod 2) (W H V V₂ V₃ s.seed_le) ∧
      (primeRank 2 (Source.Utilde H V₃ V₁) = 4 →
        Nonempty ((TransvectionQuotients.FiveSeed.toBar
          (L ⊔ (T : Subgroup G)) V s.normalizes_V).range ≃* Equiv.Perm (Fin 6)) →
        primeRank 2 (Source.U2 H V V₂) = 6) ∧
      (primeRank 2 (Source.Utilde H V₃ V₁) = 5 →
        primeRank 2 (Source.U2 H V V₂) = 8) := by
  exact source_parabolic_conclusions_of_local_marking T L M K s natural
    earlier1376 earlier1354 hH hK hprod ρ hρ eK hmodel
    (fun n d => LocalMarking.nonempty_compatibleMarking n d)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.SourceAssembly
