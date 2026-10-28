module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PairFrattini
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.PriorCaseReduction

/-!
# The two fixed-line centralizers are not of characteristic two

If one centralizer lay in He, the original Sylow-preserving reselection and
prior-case reduction would give another paired-cubic setup with the same
Thompson subgroup. Its central involution lies in that Thompson subgroup's
Frattini subgroup, contradicting the proved trivial intersection with the
selected group's center. The prior linear and A5 exclusions remain explicit
for the final Chapter 2 assembly; the paired-cubic exclusion is never used.

Source: Aschbacher–Smith, 2.4.31, printed p.547.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem frattini_transport
    (d e : MinimalBlockSetup M) (T : Sylow 2 G) (P : Subgroup G)
    (heS : (e.S : Subgroup e.H).map e.H.subtype = P)
    (hRT : sourceR d = elementaryAbelianMaxJ (T : Subgroup G))
    (hRP : sourceR d ≤ P) (hPT : P ≤ (T : Subgroup G))
    (z : G) (hzPhi : z ∈ (frattini (sourceR d)).map (sourceR d).subtype) :
    z ∈ (frattini (sourceR e)).map (sourceR e).subtype := by
  have hJTP : elementaryAbelianMaxJ (T : Subgroup G) ≤
      P := by
    rw [← hRT]
    exact hRP
  have hJ : elementaryAbelianMaxJ P =
      elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate_finite (T : Subgroup G)
      P hJTP hPT
  have hJR : sourceR e = sourceR d := by
    change elementaryAbelianMaxJ ((e.S : Subgroup e.H).map e.H.subtype) = _
    rw [heS]
    exact hJ.trans hRT.symm
  have hzPhi' : z ∈ (frattini (sourceR e)).map (sourceR e).subtype := by
    rw [hJR]
    exact hzPhi
  exact hzPhi'

private theorem centralizer_not_He_of_prior_cases
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hR : sourceR d ∈ beta M) (hRT : sourceR d = elementaryAbelianMaxJ T)
    (z : G) (hz : z ≠ 1) (hzPhi : z ∈ (frattini (sourceR d)).map (sourceR d).subtype)
    (hg : centralizer ({z} : Set G) ∈ gammaMax (Chapter1.He G) M)
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hRP : sourceR d ≤ (P : Subgroup _).map (centralizer ({z} : Set G)).subtype)
    (hPT : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype < (T : Subgroup G)) :
    centralizer ({z} : Set G) ∉ Chapter1.He G := by
  intro he
  have hzero : centralizer ({z} : Set G) ∈ gammaEvenZero (Chapter1.He G) M := ⟨Or.inr hg,he⟩
  have hPb : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype ∈ beta M :=
    beta_mono hR hRP (P.isPGroup'.map (centralizer ({z} : Set G)).subtype)
  have hfull : ((P : Subgroup _).map (centralizer ({z} : Set G)).subtype,
      centralizer ({z} : Set G)) ∈ localPairsIn (Chapter1.He G) M (centralizer ({z} : Set G)) :=
    ⟨⟨hPb,he,hg.1.1,map_subtype_le _,gamma_not_le hg.1⟩,le_rfl⟩
  have hzP := hRP ((map_subtype_le _) hzPhi)
  obtain ⟨e,heC,heS,hepair,hecubic,hze⟩ := exists_paired_cubic_setup_in_centralizer_of_prior_cases
    hG T hM hTM hu hdelta hcounter hlinear hfive z hzero P hfull hPT hzP
  have heT : (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) := heS ▸ hPT
  obtain ⟨c⟩ := e.paired_cubic_coordinates hG T hM hTM hu heT hepair hecubic
  have hzPhi' := frattini_transport d e T
    ((P : Subgroup _).map (centralizer ({z} : Set G)).subtype) heS hRT hRP hPT.le z hzPhi
  have hh : z ∈ (⊥ : Subgroup G) := c.frattini_inf_center_eq_bot ▸ ⟨hzPhi',hze⟩
  exact hz hh

 theorem SourceCentralizerGeometry.not_He_of_prior_cases
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) :
    centralizer ({g.z₁} : Set G) ∉ Chapter1.He G ∧
      centralizer ({g.z₂} : Set G) ∉ Chapter1.He G := by
  have hh := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  have hP₁ : (g.P₁ : Subgroup _).map (centralizer ({g.z₁} : Set G)).subtype < (T : Subgroup G) := by
    apply lt_of_le_of_ne (g.first_intersection ▸ inf_le_left)
    intro he
    have hidx := g.first_sylow_index
    rw [he,relIndex_self] at hidx
    omega
  have hP₂ : (g.P₂ : Subgroup _).map (centralizer ({g.z₂} : Set G)).subtype < (T : Subgroup G) := by
    apply lt_of_le_of_ne (g.second_intersection ▸ inf_le_left)
    intro he
    have hidx := g.second_sylow_index
    rw [he,relIndex_self] at hidx
    omega
  have hz₁ : g.z₁ ≠ 1 := by intro he; have hh := g.order_first; rw [he,orderOf_one] at hh; omega
  have hz₂ : g.z₂ ≠ 1 := by intro he; have hh := g.order_second; rw [he,orderOf_one] at hh; omega
  exact ⟨centralizer_not_He_of_prior_cases d hG T hM hTM hu hdelta hcounter hlinear hfive
    hh.2.2.2.2.2.1 hh.2.2.2.2.1 g.z₁ hz₁ g.involutions_mem_frattini.1 g.first_max g.P₁
    (g.first_span ▸ le_sup_left) hP₁,
    centralizer_not_He_of_prior_cases d hG T hM hTM hu hdelta hcounter hlinear hfive
    hh.2.2.2.2.2.1 hh.2.2.2.2.1 g.z₂ hz₂ g.involutions_mem_frattini.2 g.second_max g.P₂
    (g.second_span ▸ le_sup_left) hP₂⟩
end CFSG.Quasithin.Chapter2.DoubleA3
