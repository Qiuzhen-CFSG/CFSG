module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondDoubled
public import Theory.SpecificGroups.PSL3Two.NormalExtension.Parabolic
public import Theory.SpecificGroups.PSL3Two.Parabolics.TwoKernel

/-!
# The first parabolic inside the actual second join

The constructed doubled-natural component, its normality and the actual
S₃ first vertex identify the full quotient Y/O₂(Y) with L₃(2). The lifted
parabolic lattice makes the first vertex P maximal in Y. Since Y escapes
N_G(L), its intersection with N_G(L) is precisely P. Every nonzero point
of the original omega seed is fixed by P and moved by the component, so
its full centralizer in Y is P as well.

This identifies the literal first vertex needed for the Baumann argument.
Both joins, the full kernels, the same omega span and the original
Chapter12/13.3 premises are retained.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
variable {H : Type*} [Group H] [Finite H]

/-- A proper S₃ parabolic over the common Sylow is maximal in a normal
linear-three extension; the full two-core quotient is the actual L₃(2). -/
theorem linear_parabolic_coatom (S : Sylow 2 H) (K P : Subgroup H) [K.Normal]
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hgen : K ⊔ (S : Subgroup H) = ⊤)
    (hSP : (S : Subgroup H) ≤ P)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ ⊤) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.PSL) ∧ IsCoatom P := by
  obtain ⟨e⟩ := Matrix.PSL3Two.quotient_of_normal_component_and_symmetricThree_parabolic
    K (eK.trans Matrix.PSL3Two.equiv) S hgen P hSP eP
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨A,B,hA,hB,_,_,_,_,_,_,hall⟩ := Matrix.PSL3Two.two_kernel_parabolics S f hf hk
  refine ⟨⟨e⟩,?_⟩
  rcases hall P hSP with hs | ha | hb | ht
  · have hi := SymmetricThreeTwoCore.sylow_index_three eP (S.subtype hSP)
    change (S : Subgroup H).relIndex P = 3 at hi
    rw [←hs,relIndex_self] at hi
    omega
  · exact ha ▸ hA
  · exact hb ▸ hB
  · exact (hne ht).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original first vertex is the full centralizer of every nontrivial
seed point in the second join, and is its intersection with N_G(L). -/
theorem original_plane_second_point_parabolic
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
    Nonempty ((Y ⧸ pCore 2 Y) ≃* Matrix.PSL3Two.PSL) ∧
      IsCoatom (P.subgroupOf Y) ∧
      Y ⊓ normalizer (L : Set G) = P ∧
      ∀ z ∈ Z, z ≠ 1 → Y ⊓ centralizer ({z} : Set G) = P := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
  let U := conjugateSpanBy Z Y
  have hTP : (T : Subgroup G) ≤ P := sylow_le_firstFlagNormalizer
  have hPY : P ≤ Y := le_sup_left
  have hTY : (T : Subgroup G) ≤ Y := hTP.trans hPY
  let S := T.subtype hTY
  obtain ⟨_,⟨eP⟩,_,hPZ,_,_,_,hYout,_,_⟩ :=
    original_plane_second_amalgam h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,⟨q,e,he⟩,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩ :=
    exists_original_plane_second_doubled h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 modules fixed covered h13316
  let := hn
  let j := K.equivMapOfInjective Y.subtype Y.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map Y.subtype)) j (pCore_map_iso 2 j)
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    rw [←hr]
    exact pResidual_sup_sylow_eq_top S
  let a := subgroupOfEquivOfLe hPY
  have hPM : P ≤ normalizer (L : Set G) :=
    inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hneP : P.subgroupOf Y ≠ ⊤ := by
    intro hp
    apply hYout.2
    have hh := congrArg (map Y.subtype) hp
    rw [map_subgroupOf_eq_of_le hPY,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.ge.trans hPM
  obtain ⟨hq,hcoat⟩ := SecondGeneration.linear_parabolic_coatom S K (P.subgroupOf Y)
    (jq.trans q) hKS (fun _ ht => hTP ht)
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eP) hneP
  have maximal (B : Subgroup G) (hPB : P ≤ B) (hBY : B ≤ Y) (hneB : B ≠ Y) : B = P := by
    have hle : P.subgroupOf Y ≤ B.subgroupOf Y := comap_mono hPB
    by_contra hh
    have hlt : P.subgroupOf Y < B.subgroupOf Y := lt_of_le_of_ne hle (by
      intro heq
      have hm := congrArg (map Y.subtype) heq
      rw [map_subgroupOf_eq_of_le hPY,map_subgroupOf_eq_of_le hBY] at hm
      exact hh hm.symm)
    have heq := hcoat.2 _ hlt
    have hm := congrArg (map Y.subtype) heq
    rw [map_subgroupOf_eq_of_le hBY,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hneB hm
  refine ⟨hq,hcoat,maximal _ (le_inf hPY hPM) inf_le_left ?_,?_⟩
  · intro hh
    exact hYout.2 (hh.ge.trans inf_le_right)
  · intro z hz hz1
    apply maximal _ (le_inf hPY ?_) inf_le_left
    · intro hh
      have hzK : z ∈ centralizer (K.map Y.subtype : Set G) := by
        intro k hk
        exact mem_centralizer_singleton_iff.mp
          ((show Y ≤ centralizer ({z} : Set G) from hh ▸ inf_le_right)
            (map_subtype_le K hk))
      have hzbot : z ∈ (⊥ : Subgroup G) := hfix ▸
        (show z ∈ U ⊓ centralizer (K.map Y.subtype : Set G) from
          ⟨le_conjugateSpanBy Z Y hz,hzK⟩)
      exact hz1 hzbot
    · exact hPZ.trans (centralizer_le (Set.singleton_subset_iff.mpr hz))


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
