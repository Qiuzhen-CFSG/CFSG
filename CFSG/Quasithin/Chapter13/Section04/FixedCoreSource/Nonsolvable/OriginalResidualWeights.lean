module
public import Theory.Representation.BinaryPermutation.SynthemeCoreCommutator
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductCoreWeight
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Original residual commutators detect the two core weights

For the original five-dimensional augmentation core, a nonidentity vector
of V ∩ Ω₁Z(T) belongs to [V ∩ Ω₁Z(T),L₂] exactly when it has weight four.
The proof lifts the Klein four subgroup of the literal tetrahedral residual
through a Sylow intersection. Its fixed words are constant on opposite
edges; the residual displacements are precisely the even plane on those
three pairs. Relabeling preserves weight and retains the original quotient.

Both recognized component rows supply Ω₁Z(T) ≤ V, giving the source test
with the full Z. In the five-dimensional component row, seed splitting
also gives Z ≤ V_K, independently of the product/linear H₀ alternative.
The existing outside-parabolic uniqueness identifies the actual component
plane. Applying the same weight test proves that C_V(L) ≤ [Z,O²(P)] is
exactly weight four for its generator in V_K; failure is exactly weight two.

For the natural component rows, the original fixed line lies in [Z,O²(P)]
exactly when it lies in V_K. The natural model bounds its Sylow fixed space
by one line. The P-orbit of that line has no P-fixed vector, since otherwise
P would lie in C_G(C_V(L)) = N_G(L). Sylow averaging and P = O²(P)T then
put the line in the literal seed commutator.

These are the two weight/commutator equivalences in the first paragraph
of the proof of 13.4.14. The six-dimensional H₀ module/socle alternatives,
both escaping-weight uniqueness, remaining reciprocal exclusions and graph
assembly remain separate. Earlier Chapter12/13.3 and the independent natural
LargeDistanceInput retain their existing producers and final discharge.
Source: Aschbacher–Smith 13.4.14, printed p.911; H.5 is used subsequently.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem sylow_intersection (S : Sylow 2 G) (J : Subgroup G)
    (hSJ : (S : Subgroup G) ≤ normalizer (J : Set G)) :
    ∃ P : Sylow 2 J, (P : Subgroup J) = (S : Subgroup G).subgroupOf J := by
  let X := J ⊔ (S : Subgroup G)
  have hJX : J ≤ X := le_sup_left
  let _ : (J.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJX).mpr (sup_le J.le_normalizer hSJ)
  obtain ⟨P,hP⟩ := (S.subtype (show (S : Subgroup G) ≤ X from le_sup_right)).exists_subgroupOf_eq_of_normal (J.subgroupOf X)
  let e := subgroupOfEquivOfLe hJX
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,hJX x.property⟩,x.property⟩,hx,rfl⟩

private theorem marked_residual_weight_iff
    (D : ChosenModule T L V) (m : CoreMarking D)
    (K : Subgroup G) (hKL : K ≤ L)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (f : K →* A) (hf : Function.Surjective f)
    (hmark : ∀ k : K, (m.quotient (QuotientGroup.mk' (centralCore L)
      (inclusion hKL k))).val = synthemeHom (f k))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    z.val ∈ ⁅V ⊓ omegaOneCenterAmbient (T : Subgroup G), K⁆ ↔ m.weight z = 4 := by
  let Z := V ⊓ omegaOneCenterAmbient (T : Subgroup G)
  let N := ((SynthemeCoreChief.oppositePlane.toSubgroup).comap m.coordinate.toMonoidHom).map V.subtype
  let act (k : K) (w : V) : V := V.normalizerMonoidHom ⟨k.val,D.normalizes (hKL k.property)⟩ w
  have hact (k : K) (w : V) : (m.coordinate (act k w)).toAdd =
      coreRepresentation (Fin 6) (synthemeHom (f k)) (m.coordinate w).toAdd := by
    rw [←hmark k]
    exact m.equivariant (inclusion hKL k) w
  obtain ⟨S,hS⟩ := sylow_intersection T K hTK
  have hklein : klein ≤ ((T : Subgroup G).subgroupOf K).map f := by
    rw [←klein_core,←hS]
    exact pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hf)
  have hfixed (w : V) (hw : w.val ∈ omegaOneCenterAmbient (T : Subgroup G)) :
      ∀ a : A, a ∈ klein → coreRepresentation (Fin 6) (synthemeHom a) (m.coordinate w).toAdd =
        (m.coordinate w).toAdd := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := hklein ha
    rw [←hact]
    congr 2
    apply Subtype.ext
    change k.val * w.val * k.val⁻¹ = w.val
    exact mul_inv_eq_iff_eq_mul.mpr (((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 k.val hk)
  have hN (w : V) : w.val ∈ N ↔ (m.coordinate w).toAdd ∈ SynthemeCoreChief.oppositePlane :=
    mem_map_iff_mem V.subtype_injective
  have hcomm : ⁅Z,K⁆ ≤ N := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk w hw
    let v : V := ⟨w,hw.1⟩
    have hc : (act ⟨k,hk⟩ v * v⁻¹).val = ⁅k,w⁆ := rfl
    rw [←hc,hN]
    rw [map_mul,map_inv]
    simp only [toAdd_mul, toAdd_inv, ←sub_eq_add_neg]
    rw [hact]
    exact SynthemeCoreChief.klein_fixed_displacement _ (hfixed v hw.2) (f ⟨k,hk⟩)
  constructor
  · intro hz
    have hm := SynthemeCoreChief.oppositePlane_weight (m.coordinate z).toAdd ((hN z).mp (hcomm hz))
    rcases hm with he | he
    · exact False.elim (hz1 (m.coordinate.injective (he.trans m.coordinate.map_one.symm)))
    · exact he
  · intro hw
    obtain ⟨a,b,hab⟩ := SynthemeCoreChief.weight_four_displacement_sum
      (m.coordinate z).toAdd (hfixed z hzT) hw
    obtain ⟨k,hk⟩ := hf a
    obtain ⟨j,hj⟩ := hf b
    have he : (act k z * z⁻¹) * (act j z * z⁻¹) = z := by
      apply m.coordinate.injective
      apply Multiplicative.toAdd.injective
      simp only [map_mul,map_inv]
      simp only [toAdd_mul, toAdd_inv, ←sub_eq_add_neg]
      rw [hact,hact,hk,hj]
      exact hab
    rw [←he,commutator_comm]
    exact mul_mem (commutator_mem_commutator k.property ⟨z.property,hzT⟩)
      (commutator_mem_commutator j.property ⟨z.property,hzT⟩)

/-- The original plane residual detects weight four on every nonidentity
Sylow-central vector of the five-dimensional core. -/
theorem original_second_flag_weight_iff
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    z.val ∈ ⁅V ⊓ omegaOneCenterAmbient (T : Subgroup G), (pResidual 2 B).map B.subtype⁆ ↔
      m.weight z = 4 := by
  let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTJ := m.sylow_normalizes_inner_plane W hT
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hT
  obtain ⟨f,hf,hmark⟩ := Solvable.second_parabolic_residual_action D (m.relabel g) J inf_le_left
    (m.aligned_inner_plane_image W g hg)
  have he := marked_residual_weight_iff D (m.relabel g) _ ((map_subtype_le _).trans inf_le_left)
    (hTJ.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J)))
    f hf hmark z hzT hz1
  have hweight : (m.relabel g).weight z = m.weight z := by
    change wordWeight (representation (Fin 6) g.val⁻¹ (m.coordinate z).toAdd.val) = _
    rw [wordWeight_permute]
    rfl
  rw [hweight] at he
  dsimp only
  rw [Solvable.second_flag_normalizer_eq D _ hT,Solvable.second_parabolic_full_residual J hTJ]
  exact he

/-- When the whole omega-center lies in the original core, this is the
literal equivalence z∈[Z,L₂] iff z has weight four used in 13.4.14. -/
theorem original_omega_residual_weight_iff
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    z.val ∈ ⁅omegaOneCenterAmbient (T : Subgroup G), (pResidual 2 B).map B.subtype⁆ ↔
      m.weight z = 4 := by
  simpa only [inf_eq_right.mpr hZV] using
    original_second_flag_weight_iff D m W hW hT z hzT hz1

open Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- Both recognized component rows supply full omega containment, so the
weight test applies to the literal original L₂ and every central vector. -/
theorem small_component_original_weight_detection
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)))
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    ∀ v : V, v.val ∈ omegaOneCenterAmbient (T : Subgroup G) → v ≠ 1 →
      (v.val ∈ ⁅omegaOneCenterAmbient (T : Subgroup G), (pResidual 2 B).map B.subtype⁆ ↔
        m.weight v = 4) := by
  have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨_,_,_,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry
        hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact hZ.le.trans inf_le_left
    · obtain ⟨_,_,_,_,_,_,hZ,_⟩ := ordinary_six_component_geometry
        h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact hZ.le.trans inf_le_left
  exact fun v hv hv1 => original_omega_residual_weight_iff D m hZV W hW hT v hv hv1

/-- In the actual five-dimensional component row the full seed lies in
both cores. Construct the original and component planes and obtain both
literal weight/commutator tests, independently of the H₀ alternative. -/
theorem ordinary_six_original_reciprocal_weight_detection
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := ⁅conjugateSpanBy Z K,K⁆
    ∃ DK : ChosenModule T K U, ∃ mK : CoreMarking DK, ∃ hd : m.constant.val ∈ U,
      ∃ W WK : Submodule (ZMod 2) (natural (Fin 6)),
        Module.finrank (ZMod 2) W = 2 ∧ Module.finrank (ZMod 2) WK = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
        (T : Subgroup G) ≤ normalizer (mK.naturalPreimage WK : Set G) ∧
        ∃ P : Subgroup G,
          P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
          P ⋖ centralizer ({z.val} : Set G) ∧
          P = (K ⊔ (T : Subgroup G)) ⊓ normalizer (mK.naturalPreimage WK : Set G) ∧
          let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
          Z ≤ U ∧
          (∀ v : V, v.val ∈ Z → v ≠ 1 →
            (v.val ∈ ⁅Z,(pResidual 2 B).map B.subtype⁆ ↔ m.weight v = 4)) ∧
          (V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 P).map P.subtype⁆ ↔
            mK.weight ⟨m.constant.val,hd⟩ = 4) ∧
          (¬ V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 P).map P.subtype⁆ ↔
            mK.weight ⟨m.constant.val,hd⟩ = 2) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,hfixK,_,_,hZ,_⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hzU : z.val ∈ U := (hfixK.symm ▸ mem_zpowers z.val).1
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (Solvable.original_sylow_le_centralizer hzT).trans hHN
  have hZU : Z ≤ U := by
    have hh := le_conjugateSpanBy Z K
    rw [component_seed_split h₀ hzT hz1 hK.1 hTK,
      component_full_fixed_line h structural z.val hz1 hzT hindex K hK.1 hKM] at hh
    exact hh.trans (sup_le le_rfl (zpowers_le.mpr hzU))
  have hdT : m.constant.val ∈ Z := (m.constant_mem_central_four h structural).2
  have hd : m.constant.val ∈ U := hZU hdT
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨W,hW,hT,P,hP,hPH,_,_,_,_,_,_,_,_,_,_⟩ := ordinary_six_original_pair
    h₀ h structural modules D m h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK eK
  have hH := (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed
    hindex hM z hzT hzL hK hHN hKM hfK eK).1
  obtain ⟨P₀,_,_,_,_,_,_,_,_,_,_,_,_,hunique₀⟩ :=
    ordinary_six_full_centralizer_parabolic h₀ h structural modules D m h1332 fixed
      hindex hM z hzT hzL hK hHN hKM hfK eK
  have hPP : P = P₀ := hunique₀ P hP hPH.le
  have hunique : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Q ≤ centralizer ({z.val} : Set G) → Q = P := by
    intro Q hQ hQH
    exact (hunique₀ Q hQ hQH).trans hPP.symm
  obtain ⟨WK,hWK,hTKW,hPK⟩ := component_core_plane_parabolic
    h hK12 structural D m DK mK hKM hd z.val hzT hz1 hH P hPH hunique
  have hweight := original_omega_residual_weight_iff DK mK hZU WK hWK hTKW
    ⟨m.constant.val,hd⟩ hdT (fun he => m.constant_ne_one (Subtype.ext (congrArg (fun a : U => a.val) he)))
  dsimp only at hweight
  rw [←hPK] at hweight
  have hline : V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 P).map P.subtype⁆ ↔
      m.constant.val ∈ ⁅Z,(pResidual 2 P).map P.subtype⁆ := by
    constructor
    · intro he
      exact he ⟨m.constant.property,m.constant_fixed⟩
    · intro he v hv
      rcases (m.fixed_iff ⟨v,hv.1⟩).mp hv.2 with hx | hx
      · have hx' : v = 1 := congrArg Subtype.val hx
        rw [hx']
        exact one_mem _
      · have hx' : v = m.constant.val := congrArg Subtype.val hx
        exact hx'.symm ▸ he
  have hnK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hc
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩ (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc k hk)
  have hw := mK.nonfixed_weight ⟨m.constant.val,hd⟩ hnK
  refine ⟨DK,mK,hd,W,WK,hW,hWK,hT,hTKW,P,hP,hPH,hPK,hZU,?_,hline.trans hweight,?_⟩
  · exact fun v hv hv1 => original_omega_residual_weight_iff D m
      (hZ.le.trans inf_le_left) W hW hT v hv hv1
  · rw [hline,hweight]
    omega

private theorem fixed_line_le_residual_of_natural_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (P U : Subgroup G) [IsElementaryAbelian 2 U]
    (hTP : (T : Subgroup G) ≤ P) (hPM : ¬ P ≤ normalizer (L : Set G))
    (hPU : P ≤ normalizer (U : Set G))
    (hbound : Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2)
    (hFU : V ⊓ centralizer (L : Set G) ≤ U) :
    V ⊓ centralizer (L : Set G) ≤
      ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 P).map P.subtype⁆ := by
  let F := V ⊓ centralizer (L : Set G)
  let Y := conjugateSpanBy F P
  have hFZ : F ≤ omegaOneCenterAmbient (T : Subgroup G) :=
    Solvable.fixed_le_original_omegaCenter h structural D m
  have hFT : F ≤ centralizer (T : Set G) := fun _ hx =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hFZ hx)).2.2
  have hFfix : F = U ⊓ centralizer (T : Set G) :=
    eq_of_le_of_card_ge (le_inf hFU hFT) (by rw [m.card_fixed]; exact hbound)
  have hYU : Y ≤ U := conjugateSpanBy_le hFU hPU
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYU
  have hzero : Y ⊓ centralizer (P : Set G) = ⊥ := by
    apply bot_unique
    intro a ha
    by_contra hn
    have ha1 : a ≠ 1 := fun he => hn (he ▸ one_mem _)
    have haF : a ∈ F := hFfix.symm ▸ ⟨hYU ha.1,centralizer_le hTP ha.2⟩
    have hPC : P ≤ centralizer ({a} : Set G) :=
      fun p hp => mem_centralizer_singleton_iff.mpr (ha.2 p hp)
    exact hPM (hPC.trans (fixed_generator_centralizer h structural D m haF ha1).le)
  have hsplit := conjugateSpan_split_of_sylow_fixed (T.subtype hTP)
    (show F ≤ centralizer (((T.subtype hTP : Sylow 2 P) : Subgroup P).map P.subtype : Set G) by
      rw [T.coe_subtype,map_subgroupOf_eq_of_le hTP]; exact hFT)
  change Y = ⁅Y,P⁆ ⊔ (Y ⊓ centralizer (P : Set G)) at hsplit
  rw [hzero,sup_bot_eq] at hsplit
  have hFP : F ≤ P := hFZ.trans ((fun _ hx =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) : omegaOneCenterAmbient (T : Subgroup G) ≤
      (T : Subgroup G)) |>.trans hTP
  have hYP : Y ≤ P := conjugateSpanBy_le_self hFP
  have hc := normalClosure_commutator_eq_of_centralizing_supplement
    (F.subgroupOf P) (pResidual 2 P) (T.subtype hTP : Subgroup P)
    (pResidual_sup_sylow_eq_top (T.subtype hTP))
    (show F.subgroupOf P ≤ centralizer (T.subtype hTP : Set P) from
      fun a ha t ht => Subtype.ext (hFT ha t.val ht))
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy F P hFP] at hc
  have hm := congrArg (map P.subtype) hc
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hYP,
    map_subgroupOf_eq_of_le hFP,←MonoidHom.range_eq_map,range_subtype] at hm
  exact (le_conjugateSpanBy F P).trans
    ((hsplit.trans hm).le.trans (commutator_mono hFZ le_rfl))

/-- In either actual natural component row, membership of the original
fixed line in V_K is equivalent to membership in [Z,O²(P)]. The module
bound and all residual and normalization premises are discharged here. -/
theorem small_component_natural_residual_fixed_iff
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) = ⊥)
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPH : P ≤ centralizer ({z.val} : Set G)) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := ⁅conjugateSpanBy Z K,K⁆
    (V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 P).map P.subtype⁆ ↔
      V ⊓ centralizer (L : Set G) ≤ U) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (Solvable.original_sylow_le_centralizer hzT).trans hHN
  obtain ⟨DK,⟨mark⟩⟩ : ∃ DK : ChosenModule T K U, Nonempty (ComponentModuleAt DK z.val) := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨DK,mark,_⟩ := linear_component_geometry hl h₀ h structural modules D m h1332
        fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact ⟨DK,mark⟩
    · obtain ⟨DK,mark,_⟩ := ordinary_six_component_geometry h₀ h structural modules D m h1332
        fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact ⟨DK,mark⟩
  have hbound : Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
    cases mark with
    | linearThree q e he =>
      exact Representation.BinaryOffender.sylow_fixed_card_le_of_conjugation_marking
        T K U DK.sylow_normalizes_component DK.normalizes BinaryLinearThree.W
        (q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
        (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he 2
        BinaryLinearThree.card_sylow_natural_fixed_le_two
    | naturalSix q e he =>
      exact Representation.BinaryOffender.sylow_fixed_card_le_of_conjugation_marking
        T K U DK.sylow_normalizes_component DK.normalizes
        (alternatingNaturalRepresentation (Fin 6))
        (q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
        (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he 2
        six_natural_sylow_fixed_card_le_two
    | coreSix mK _ =>
      have hc := mK.card_fixed
      rw [hfixed,card_bot] at hc
      omega
  have hH : centralizer ({z.val} : Set G) = H := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · exact (linear_full_centralizer hl h₀ h structural modules D m h1332 fixed hindex
        hM z hzT hzL hK.1 hHN hKM hfK eK).1
    · exact (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed hindex
        hM z hzT hzL hK hHN hKM hfK eK).1
  have hPH' : P ≤ H := hPH.trans_eq hH
  have hUP : P ≤ normalizer (U : Set G) := hPH'.trans
    (le_normalizer_of_normal_subgroupOf (DK.le_sylow.trans le_sup_right)
      (hK := (component_moved_reduced h₀ hzT hz1 hK.1 hTK).normal))
  have hRK : (pResidual 2 P).map P.subtype ≤ K := by
    have hKH : K ≤ H := le_sup_left
    have hTH : (T : Subgroup G) ≤ H := le_sup_right
    let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le K.le_normalizer hTK)
    have hsup : K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hTH,
        ←MonoidHom.range_eq_map,range_subtype]
    have hr := embedded_pResidual_le_of_normal_sup_pGroup
      (K.subgroupOf H) ((T : Subgroup G).subgroupOf H) (P.subgroupOf H)
      T.isPGroup'.comap_subtype (by rw [hsup]; exact le_top)
    have hm := map_mono (f := H.subtype) hr
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPH',map_subgroupOf_eq_of_le hKH] at hm
    exact hm
  let := DK.elementary
  exact ⟨fun hc => hc.trans (commutator_mono (le_conjugateSpanBy Z K) hRK),
    fixed_line_le_residual_of_natural_bound h structural D m P U hP.1.1.2 hP.1.2 hUP hbound⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
