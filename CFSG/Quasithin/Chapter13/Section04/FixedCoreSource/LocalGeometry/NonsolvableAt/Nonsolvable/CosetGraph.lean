module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ComponentFullWeightComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ComponentSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.EscapingUniqueness
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.LinearReciprocal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.LinearSocleCases
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedReciprocity
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.OriginalProductWeight
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ProductMixed
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ProductReciprocity
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.Rank
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.WeightFourReciprocity
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryAugmentationAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CosetGraph
public import Theory.GroupAction.RankTwoCosetGeometry.ReciprocalSeeds
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ProductReciprocity

/-!
# The original two-type graph and the weight-two escape: structure at the original group

Form the coset graph of M=N_G(L) and X=H₀ inside their actual join, with
seeds V and U=⟨Ω₁Z(T)^X⟩. The augmentation marking identifies C_M(V)
with O₂(M). The fixed line lies in U, so C_X(U) lies in X∩M=B; the
original pair kernel then identifies it with O₂(X). Both kernels lie in
the literal O₂(B). Original maximal-local uniqueness kills every common
normal subgroup, proving that this coset graph is faithful.

The minimum over both vertex types gives reciprocal edge-core containments.
The proved 13.4.15 and 13.4.16 exclusions leave noncommuting V and Vᵍ.
Weight-four mutual normalization is impossible, so z has weight two. This
also supplies the rank-three bound and weight-two proper intersections,
selects the linear amalgam, and puts the original fixed line in the socle
of its 64-element omega module and in the original residual commutator.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/CosetGraph` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
open Representation.BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal original pair supplies a noncommuting conjugate of V with
both reciprocal containments in O₂(B), after the two reciprocal exclusions. -/
theorem original_pair_graph_noncommuting_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ B)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hout : ¬ P ⊔ B ≤ normalizer (L : Set G))
    (hXM : (P ⊔ B) ⊓ normalizer (L : Set G) = B)
    (hmixed : let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
      ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g → ⁅V,U.conjBy g⁆ = ⊥)
    (hsecond : let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
      ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g → ⁅U,U.conjBy g⁆ = ⊥) :
    ∃ g ∈ normalizer (L : Set G) ⊔ (P ⊔ B),
      V.conjBy g ≤ B.pCoreIn 2 ∧ V ≤ (B.pCoreIn 2).conjBy g ∧ ⁅V,V.conjBy g⁆ ≠ ⊥ := by
  let M := normalizer (L : Set G)
  let X := P ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hTX : (T : Subgroup G) ≤ X := hTP.trans le_sup_left
  have hZT : Z ≤ (T : Subgroup G) := fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hUX : U ≤ X := conjugateSpanBy_le_self (hZT.trans hTX)
  have hVM : V ≤ M := D.le_sylow.trans hTM
  have hnV : M ≤ normalizer (V : Set G) := normalizer_component_le_module_at h structural D m
  have hBM : B ≤ M := hXM.symm.le.trans inf_le_right
  have hMX : M ⊓ X = B := (inf_comm _ _).trans hXM
  have hCV : M ⊓ centralizer (V : Set G) = M.pCoreIn 2 := by
    obtain ⟨q,hq,_,_,hk⟩ := exists_core_product_permutation_at D m h structural eL
    have he := BinaryConjugationCoordinates.model_kernel (L ⊔ (T : Subgroup G)) V
      (sup_le D.normalizes ((structural L h).2.2 V D).1)
      (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
      q m.coordinate hq
    rw [hk] at he
    have hm := congrArg (map (L ⊔ (T : Subgroup G)).subtype) he
    rw [subgroupOf_map_subtype,inf_comm] at hm
    change normalizer (L : Set G) ⊓ centralizer (V : Set G) =
      (normalizer (L : Set G)).pCoreIn 2
    rw [hM]
    exact hm.symm
  have hQMB : M.pCoreIn 2 ≤ B :=
    (pCoreIn_le_sylow M (T.subtype hTM)).trans (by
      rw [T.coe_subtype,map_subgroupOf_eq_of_le hTM]
      exact hTB)
  have hQMR : M.pCoreIn 2 ≤ B.pCoreIn 2 :=
    (le_inf hQMB le_rfl).trans (inf_pCoreIn_le_of_le 2 hBM)
  have hFU : V ⊓ centralizer (L : Set G) ≤ U := by
    apply le_trans ?_ (le_conjugateSpanBy Z X)
    intro x hx
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    have hc := normalizer_component_le_fixed_centralizer_at h structural D m
    let := D.elementary
    exact ⟨D.le_sylow hx.1,elemPow_eq_one_of_isElementaryAbelian x hx.1,
      fun t ht => (hc (hTM ht) x hx).symm⟩
  obtain ⟨hr,_,hBk,_⟩ := Amalgam.original_pair_action_kernel h₀ D m hTP hTB eP eB hne hiP hiB
  have hCU : X ⊓ centralizer (U : Set G) = X.pCoreIn 2 := by
    apply le_antisymm
    · rw [←hBk]
      exact le_inf
        ((le_inf inf_le_left ((inf_le_right.trans (centralizer_le hFU)).trans
          (fixed_centralizer_eq_normalizer_at h structural D m).le)).trans hXM.le)
        inf_le_right
    · exact le_inf (X.pCoreIn_le 2) (hBk.symm.le.trans inf_le_right)
  have hQXR : X.pCoreIn 2 ≤ B.pCoreIn 2 :=
    (le_inf (hBk.symm.le.trans inf_le_left) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (show B ≤ X from le_sup_right))
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hr.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom (subgroupOfEquivOfLe hUX).symm.injective
  let := D.elementary
  have hcommon (A : Subgroup G) (hAM : A ≤ M)
      (hn : M ⊔ X ≤ normalizer (A : Set G)) : A = ⊥ := by
    by_contra ha
    have hnM := D.normal_subgroup_normalizer_le h.toHypothesis1221
      (hAM.trans hM.le) ha (hM.symm.le.trans (le_sup_left.trans hn))
    exact hout ((le_sup_right.trans hn).trans hnM)
  obtain ⟨g,hg,hg₁,hg₂,hgc⟩ := Subgroup.CosetGeometry.RankTwo.exists_first_reciprocal_noncommuting_seeds
    M X V U hVM hUX hnV (le_normalizer_conjugateSpanBy Z X)
    (commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer)
    (commutator_eq_bot_iff_le_centralizer.mpr U.le_centralizer) D.ne_bot
    (by rw [hMX,hCV]; exact hQMR) (by rw [hMX,hCU]; exact hQXR) hcommon
    (by simpa only [hMX] using hmixed) (by simpa only [hMX] using hsecond)
  exact ⟨g,hg,by simpa only [hMX] using hg₁,by simpa only [hMX] using hg₂,hgc⟩

/-- Construct the actual graph pair and establish 13.4.17(1),(5),(6), with
the linear socle alternative needed for (3). No graph or endpoint witness
is assumed; the final centralizer transporter and natural component remain. -/
theorem escaping_original_graph_pair_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (hpair1347 : PairAmalgamSource1347 T)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    m.weight z = 2 ∧ 3 ≤ ChapterE.globalR V ∧
    (∀ g : G, g ∉ normalizer (L : Set G) → ∀ v : V, v ≠ 1 →
      v.val ∈ V.conjBy g → m.weight v = 2) ∧
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (¬ K ≤ normalizer (L : Set G)) ∧
      (Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) ∧
      ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
        Module.finrank (ZMod 2) W = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
        ∃ P : Subgroup G,
          P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
          P ⋖ centralizer ({z.val} : Set G) ∧
          Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
          let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
          let X := P ⊔ B
          let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
          Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
          X ∈ Chapter1.HOver G (T : Set G) ∧
          X ⊓ normalizer (L : Set G) = B ∧
          X ⊓ centralizer ({z.val} : Set G) = P ∧
          (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
            ⁅V,U.conjBy g⁆ = ⊥) ∧
          Solvable.LinearAmalgamConclusion T X ∧
          (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
            ⁅U,U.conjBy g⁆ = ⊥) ∧
          ∃ he : IsElementaryAbelian 2 U, let := he
            let ρ := elementaryRepresentation (p := 2)
              (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy
                (omegaOneCenterAmbient (T : Subgroup G)) X)))
            Nat.card U = 64 ∧
            V ⊓ centralizer (L : Set G) ≤
              ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 P).map P.subtype⁆ ∧
            binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U) ≤
              (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule ∧
          ∃ g ∈ normalizer (L : Set G) ⊔ X,
            g ∉ normalizer (L : Set G) ∧
            V.conjBy g ≤ B.pCoreIn 2 ∧ V ≤ (B.pCoreIn 2).conjBy g ∧
              ⁅V,V.conjBy g⁆ ≠ ⊥ ∧ ⁅V,V.conjBy g⁆ ≤ V ⊓ V.conjBy g := by
  have hzL : z.val ∉ centralizer (L : Set G) := by
    intro hz
    exact hzout (fixed_generator_centralizer_at h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  have hnonsolv := hnonsolvable z hzT hzL hzout
  have hunique := (escaping_seed_uniqueness_and_rank_at hl h₀ h structural modules D m h1332
    fixed five covered h13316 hindex hM h1347 hpair1347 h1338 hnonsolvable
    z hz1 hzT hzout).2.2.1
  obtain ⟨K,hK,hfK,_,hHN,_,hKM,_⟩ := exists_escaping_component_at h₀ h structural m
    h1332 h1338 hzT (fun he => hz1 (Subtype.ext he)) hzout hnonsolv
  have model := selected_component_ordinary_or_linear_at hl h₀ h structural D m h1332
    fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK
  have hgeom : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨_,_,hL,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry_at
        hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact ⟨hL,hZ.le.trans inf_le_left⟩
    · obtain ⟨_,_,_,hL,_,_,hZ,_⟩ := ordinary_six_component_geometry_at
        h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact ⟨hL,hZ.le.trans inf_le_left⟩
  obtain ⟨⟨eL⟩,hZV⟩ := hgeom
  obtain ⟨W,hW,hTW,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,hfixed,hcentral⟩ :=
    small_component_original_pair_at hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK model
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hTW
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hout : ¬ X ≤ normalizer (L : Set G) := fun hx => hP.1.2 (le_sup_left.trans hx)
  have hBlocal : B ∈ Chapter1.HOver G (T : Set G) := by
    have hVB : V ≤ B.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
        (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module_at h structural D m))
    refine ⟨?_,hTB⟩
    intro he
    have hv : V = ⊥ := bot_unique (he ▸ hVB)
    have hc := m.card_module
    rw [hv,card_bot] at hc
    omega
  have hcentral' :
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂) := by
    dsimp only
    intro hx
    obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral X hx.1 le_sup_left le_sup_right
    exact ⟨h₁,h₂,Or.inl hr⟩
  have hfixedB : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G) := by
    rw [←Amalgam.omega_fixed_twoResidual B hTB]
    exact hfixed
  have hc := h1347 W hW hTW P hP.1.1 hBlocal ⟨eP⟩ ⟨eB⟩ hne
    (Solvable.original_second_flag_residual_eq_inner D m W hTW)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB hcentral'
  obtain ⟨hXM,hXH,_⟩ := hcentral X hlocal.1 le_sup_left le_sup_right
  have hrecip :
      (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
        ⁅V,U.conjBy g⁆ = ⊥) ∧
      ((⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
          ((pResidual 2 P).map P.subtype).pCoreIn 2 ∧
        m.weight z = 4 ∧ ⁅U,B.pCoreIn 2⁆ ≤ V ⊓ centralizer (L : Set G) ∧
        (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
          ⁅U,U.conjBy g⁆ = ⊥)) ∨
        (Solvable.LinearAmalgamConclusion T X ∧
          (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
            ⁅U,U.conjBy g⁆ = ⊥))) := by
    rcases hc.2 with hc | hc
    · refine ⟨original_product_pair_mixed_commute_at h₀ D m h structural hindex P B
        hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc hBM hfixedB hfusion,Or.inl ⟨hc,?_,?_,?_⟩⟩
      · exact original_product_weight_four_at h structural D m W hW hTW P hP z hzL hPH.le hc
      · rw [←hfixedB]
        exact original_product_radical_movement_at h₀ D m h structural hindex P B
          hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc
      · exact original_product_pair_reciprocal_commute_at h₀ D m h structural hindex P B
          hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc hBM hfixedB hfusion
          z hz1 hzT hzout hunique
          (original_product_weight_four_at h structural D m W hW hTW P hP z hzL hPH.le hc)
    · refine ⟨?_,Or.inr ⟨hc,?_⟩⟩
      · exact original_linear_pair_mixed_commute_at hl h₀ h structural modules D m
          hP.1.1.2 hTB eP eB hne hout hindex hiP hiB (hcentral' hlocal).2.2
          h1332 fixed five covered h13316 h1338 hc eL hM hZV W hW hTW rfl
          hfusion z hzT hzL hPH.le hnonsolv
      · obtain ⟨_,_,_,hr⟩ := original_linear_pair_module_nonFF_at h₀ h structural D m
          hP.1.1.2 hTB eP eB hne hout hindex hiP hiB (hcentral' hlocal).2.2 h1332 hc
        intro g h₁ h₂
        have hR : B.pCoreIn 2 ≤ X := (pCoreIn_le 2 B).trans le_sup_right
        exact hr g (h₁.trans hR) (h₂.trans (map_mono hR))

  have hsecond : ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
      ⁅U,U.conjBy g⁆ = ⊥ := hrecip.2.elim (fun hp => hp.2.2.2) (fun hl => hl.2)
  obtain ⟨g,hg,hg₁,hg₂,hgc⟩ := original_pair_graph_noncommuting_at h₀ h structural D m eL hM
    P B hP.1.1.2 hTB eP eB hne hiP hiB hout hXM hrecip.1 hsecond
  have hw2 : m.weight z = 2 := by
    rcases m.nonfixed_weight z hzL with hh | hh
    · exact hh
    · exact (hgc (original_weight_four_mutual_conjugates_commute_at h structural D m
        z hz1 hzT hzout hunique hfusion hh g
        (hg₁.trans ((pCoreIn_le 2 B).trans hBM))
        (hg₂.trans (map_mono ((pCoreIn_le 2 B).trans hBM))))).elim
  have hlin : Solvable.LinearAmalgamConclusion T X := by
    rcases hrecip.2 with hp | hl
    · have hh := hp.2.1
      omega
    · exact hl.1
  obtain ⟨he,hcard,hcases⟩ := original_linear_weight_socle_alternatives_at h₀ D m h1332
    hP.1.1.2 hTB eP eB hne hiP hiB h structural hM hZV W hW hTW rfl
    z hzT hzL hPH.le hP.1.2 hindex (hcentral' hlocal).2.2 hlin
  have hmiddle := hcases.resolve_left (fun hp => by have hh := hp.1; omega)
  have hpoint := hmiddle.resolve_right (fun hp => by have hh := hp.1; omega)
  have hinter : ∀ a : G, a ∉ normalizer (L : Set G) → ∀ v : V, v ≠ 1 →
      v.val ∈ V.conjBy a → m.weight v = 2 := by
    intro a ha v hv hvA
    exact (m.conjugate_intersection_weight_of_unique_escape_at h structural z hz1 hzT hzout
      hunique hfusion a ha v hv hvA).trans hw2
  have hn := normalizer_component_le_module_at h structural D m
  have hgout : g ∉ normalizer (L : Set G) := by
    intro hgM
    have he : V.conjBy g = V := mem_normalizer_iff_map_conj_eq.mp (hn hgM)
    let := D.elementary
    apply hgc
    rw [he]
    exact commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer
  have hnorm₁ : V.conjBy g ≤ normalizer (V : Set G) :=
    (hg₁.trans ((pCoreIn_le 2 B).trans hBM)).trans hn
  have hnorm₂ : V ≤ normalizer (V.conjBy g : Set G) :=
    (hg₂.trans (map_mono (((pCoreIn_le 2 B).trans hBM).trans hn))).trans (le_normalizer_map _)
  exact ⟨hw2,m.three_le_globalR_of_unique_escape_at h structural z hz1 hzT hzout hunique,
    hinter,K,hK,hfK,hHN,hKM,model,W,hW,hTW,P,hP,hPH,⟨eP⟩,⟨eB⟩,hlocal,hXM,hXH,
    hrecip.1,hlin,hsecond,he,hcard,hpoint.2.1,hpoint.2.2,g,hg,hgout,hg₁,hg₂,hgc,
    le_inf (le_normalizer_iff_commutator_le_left.mp hnorm₁)
      (le_normalizer_iff_commutator_le_right.mp hnorm₂)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
