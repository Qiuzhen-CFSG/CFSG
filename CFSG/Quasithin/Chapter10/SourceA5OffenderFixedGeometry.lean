module
public import CFSG.Quasithin.Chapter10.SourceA5ConjugateIntersection
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureFixedSpace
public import Theory.GroupTheory.Commutator.ExchangedFactor

/-!
# Source weak-closure displacement geometry for the original A5 factor

A common element of an outside conjugate moved factor has a centralizer that
normalizes the moved factor. The proved outside-M intersection theorem then
forces the relevant normalizing subgroup to centralize the common fixed-space
factor. If the displacement subgroup is nontrivial, the whole original full
module is forced into the conjugate maximal local group. The module-A lower
bound from the source fixed-space calculation can therefore be used without
assuming the fixed-space identity separately.

The genuine earlier source inputs remain explicit: separate-factor
centralization, element-centralizer containment, component-normalizer
containment, and the corank offender. The source module kernel equality is
not inferred from pair decomposition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 10.2.12, printed pp.754–755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem moved_pair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {m : G} (hm : m ∈ D.maximalLocal) :
    (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  have hmaps (a : G) (ha : a ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj a).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ha)
  rw [map_commutator,hmaps m hm,map_commutator,
    hmaps t ((le_normalizer_componentOrbit L T) ht)]
  rcases source_nonnormal_maximal_pair D hn ht htn m hm with he|he
  · exact Or.inl (congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) he)
  · exact Or.inr (congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) he)

theorem source_nonnormal_conjugate_point_centralizer_normalizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    {g b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    centralizer ({b} : Set G) ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom ⊓
      normalizer (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  obtain ⟨w,hw,rfl⟩ := hb
  have hwn : w ∉ centralizer (L : Set G) := by
    intro hc
    apply hbn
    rintro z ⟨l,hl,rfl⟩
    simpa only [←map_mul,MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (hc l hl)
  have hwne : w ≠ 1 := fun he => hwn (he ▸ one_mem _)
  have hwu : w ∉ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom :=
    fun hh => hwn (hcross hh)
  have hc := centralizer_le_normalizer_of_conj_pair D.maximalLocal ⁅D.fullModule,L⁆
    ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (fun m hm => moved_pair D hn ht htn hm) hw hwu (hcent w hw hwne)
  change centralizer ({(MulAut.conj g) w} : Set G) ≤ _
  rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) w]
  exact le_inf (map_mono (hc.trans inf_le_left))
    ((map_mono (hc.trans inf_le_right)).trans
      ((⁅D.fullModule,L⁆ : Subgroup G).le_normalizer_map (MulAut.conj g).toMonoidHom))

theorem source_a5_offender_normalizer_fixed_space
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g b : G} (hg : g ∉ D.maximalLocal)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
        normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let X := W ⊓ centralizer ({b} : Set G)
  let B := P ⊓ D.maximalLocal ⊓ normalizer (W : Set G)
  have hXN : X ≤ normalizer (P : Set G) := inf_le_right.trans
    ((source_nonnormal_conjugate_point_centralizer_normalizes D hn ht htn hcross hcent
      hb hbn).trans inf_le_right)
  have hBW : B ≤ normalizer (W : Set G) := inf_le_right
  have hcomm : ⁅B,X⁆ ≤ W ⊓ P := le_inf
    ((commutator_mono le_rfl (show X ≤ W from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp hBW))
    ((commutator_mono (show B ≤ P from inf_le_left.trans inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hXN))
  have he : ⁅B,X⁆ = ⊥ := eq_bot_iff.mpr
    (hcomm.trans_eq (source_a5_moved_inf_conjugate_eq_bot D e hn t ht hcross hcent hNL hg))
  exact le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp he)

theorem source_a5_offender_fixed_space_of_normalizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal)
    (hAN : (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal : Subgroup G) : Set G) := by
  simpa only [inf_of_le_left hAN] using
    source_a5_offender_normalizer_fixed_space D e hn ht htn hcross hcent hNL hg hb hbn

theorem source_a5_offender_moduleA_lower_of_normalizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (g : G) (hg : g ∉ D.maximalLocal) {k : ℕ} (hk : k ≤ 2)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
    let _ := source_full_moved_elementary D
    A ≤ normalizer (W : Set G) → ¬ A ≤ centralizer (W : Set G) →
    ((4-k : ℕ) : ℕ∞) ≤ moduleA
      ((automizerRepresentation W).comp (inducedAutomizer W D.maximalLocal).subtype) := by
  dsimp only
  intro hAN hactive
  apply source_a5_offender_local_moduleA_lower D e g hk hsmall hAN hactive
  intro b hb hbn
  exact source_a5_offender_fixed_space_of_normalizes D e hn ht htn hcross hcent hNL hg
    hAN hb.1 hbn

theorem source_nonnormal_offender_displacement_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    {g b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ ≤
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.fullModule := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let X := W ⊓ centralizer ({b} : Set G)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hXN : X ≤ normalizer (P : Set G) := inf_le_right.trans
    ((source_nonnormal_conjugate_point_centralizer_normalizes D hn ht htn hcross hcent
      hb hbn).trans inf_le_right)
  have hAV : A ≤ normalizer (D.fullModule : Set G) :=
    inf_le_right.trans D.maximalLocal_normalizes_fullModule
  exact le_inf
    ((commutator_mono (show A ≤ P from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hXN))
    ((commutator_mono le_rfl (show X ≤ D.fullModule from inf_le_left.trans hWV)).trans
      (le_normalizer_iff_commutator_le_right.mp hAV))

theorem source_nonnormal_nontrivial_displacement_module_le_conjugate
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    {g b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G))
    (hQ : ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ ≠ ⊥) :
    D.fullModule ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
  let Q := ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
    ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆
  let : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hQ
  obtain ⟨q,hq⟩ := exists_ne (1 : Q)
  have hqne : (q : G) ≠ 1 := fun he => hq (Subtype.ext he)
  have hinc := source_nonnormal_offender_displacement_le D hn ht htn hcross hcent hb hbn
    q.property
  have hC : centralizer ({(q : G)} : Set G) ≤
      D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
    obtain ⟨w,hw,hew⟩ := hinc.1
    have hwne : w ≠ 1 := by
      intro he
      apply hqne
      rw [←hew,he,map_one]
    rw [←hew]
    change centralizer ({(MulAut.conj g) w} : Set G) ≤ _
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) w]
    exact map_mono (hcent w hw hwne)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  apply le_trans ?_ hC
  intro v hv
  exact mem_centralizer_singleton_iff.mpr (D.fullModule.le_centralizer hv q hinc.2).symm

theorem source_nonnormal_fullModule_eq_moved_pair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    D.fullModule = ⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  obtain ⟨s,_,_,_,hV,hpair⟩ := source_nonnormal_fullModule_pair D hn
  have hne : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≠ ⁅D.fullModule,L⁆ := by
    intro he
    have hc : ⁅D.fullModule,L⁆ ≤ centralizer (L : Set G) := he ▸ hcross
    let := Chapter1.mem_L_isPerfect D.maximal.1
    exact source_full_moved_ne_bot D (commutator_eq_bot_of_iterated_eq_bot D.fullModule L
      (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have he := (hpair t ((le_normalizer_componentOrbit L T) ht)).resolve_left hne
  exact hV.trans (congrArg (fun U : Subgroup G => ⁅D.fullModule,L⁆ ⊔ U) he.symm)

theorem source_nonnormal_moved_swap_generation
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    {A : Subgroup G} (hAM : A ≤ D.maximalLocal)
    {a : G} (ha : a ∈ A) (han : a ∉ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    D.fullModule = ⁅A,⁅D.fullModule,L⁆⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  have he := (moved_pair D hn ht htn (hAM ha)).resolve_left
    (fun hh => han (mem_normalizer_iff_map_conj_eq.mpr hh))
  exact eq_commutator_sup_of_conjugate_factor_le A D.fullModule ⁅D.fullModule,L⁆
    ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (source_nonnormal_fullModule_eq_moved_pair D hn ht hcross).symm
    (hAM.trans D.maximalLocal_normalizes_fullModule) ha he.le

end CFSG.Quasithin.Chapter10
