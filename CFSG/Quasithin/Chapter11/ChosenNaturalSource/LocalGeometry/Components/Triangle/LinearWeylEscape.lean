module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearRecognition
public import Theory.SpecificGroups.SymplecticFour.FullTorusNormalizer
public import Theory.AtlasPort.LinearGroups.G2.ParabolicApartment
public import Theory.AtlasPort.LinearGroups.G2.ParabolicLocalOrder

/-!
# Weyl normalizer escape in the original linear triangle

At field four the full split torus is Sylow three in each Sp₄ or G₂
parabolic. Sylow conjugacy inside the parabolic puts any cubic subgroup
in that torus. The symplectic form matrix, respectively the longest
G₂ Weyl word, inverts the torus and lies outside both standard parabolics.
Conjugating back gives escape for the original subgroup. The proved local
placement theorems identify both actual parabolic residuals, and coprime
normalizer lifting carries escape through the literal two-core quotient.

The consumer uses the original linear common-Q triangle and the two-model
recognition. It proves I ∩ N_G(X₂) is not contained in L₂X and transfers
this to the original X₁ using X₁ = X₂. No reselected natural action,
maximal-faithful placement or additional model premise is assumed.

The source equality I ∩ M = L₂X, the subsequent centralizer/module
argument, common-normal existence, exclusion of the original SL₃(4),
both final orientations and full 11.1.1--3 remain with
qt-d-1222-natural-relative-components. Earlier-source inputs retain their
producers and final discharge by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith 11.1.2, printed p.763. The G₂ torus and Weyl
coordinates use the existing licensed ATLAS port, with attribution in
Theory/AtlasPort/LinearGroups/G2/ParabolicApartment.lean and LICENSES/ATLAS.txt.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
public noncomputable section

private theorem escape_of_torus_inverter
    {G : Type*} [Group G] [Finite G] (P T A : Subgroup G)
    (_hT : T ≤ P) (hA : IsPGroup 3 A) (hAP : A ≤ P)
    (hindex : ¬ 3 ∣ (T.subgroupOf P).index)
    (w : G) (hw : w ∉ P) (hinv : ∀ t ∈ T, w*t*w⁻¹ = t⁻¹) :
    ¬ normalizer (A : Set G) ≤ P := by
  obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index
    (T.subgroupOf P) (A.subgroupOf P) hindex hA.comap_subtype
  let a := MulAut.conj (g : G)
  have hconj : A.map a.toMonoidHom ≤ T := by
    rintro _ ⟨x,hx,rfl⟩
    exact hg ⟨⟨x,hAP hx⟩,hx,rfl⟩
  have hwN : w ∈ normalizer (A.map a.toMonoidHom : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change w*x*w⁻¹ ∈ _
      rw [hinv x (hconj hx)]
      exact (A.map a.toMonoidHom).inv_mem hx
    · intro x hx
      refine ⟨x⁻¹,(A.map a.toMonoidHom).inv_mem hx,?_⟩
      change w*x⁻¹*w⁻¹=x
      rw [hinv _ (T.inv_mem (hconj hx)),inv_inv]
  intro hn
  apply hw
  rw [←map_equiv_normalizer_eq] at hwN
  obtain ⟨x,hx,hxe⟩ := hwN
  rw [←hxe]
  exact P.mul_mem (P.mul_mem g.property (hn hx)) (P.inv_mem g.property)

private theorem local_normalizer_ne_top
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) : normalizer (B : Set G) ≠ ⊤ := by
  intro he
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B (normalizer_eq_top_iff.mp he) with h | h
  · rw [h] at hB
    exact hB.ne_bot (by simp)
  · exact hproper h

private theorem escape_conjugate
    {G : Type*} [Group G] [Finite G] (B A : Subgroup G) (g : G)
    (h : ¬ normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ≤
      normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)) :
    ¬ normalizer (A : Set G) ≤ normalizer (B : Set G) := by
  intro hn
  apply h
  rw [←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
  exact map_mono hn

namespace Sp4Weyl
open Theory.SpecificGroups.SymplecticFour
open FullTorusNormalizer
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem torus_card (hF : Nat.card F = 4) : Nat.card (torus (F := F)) = 9 := by
  let f := (borel (F := F)).subtype.comp EvenBorelTorus.torusSection
  have hf : Function.Injective f := by
    intro a b h
    have he := congrArg (fun x : borel (F := F) => borelCharacters x)
      ((borel (F := F)).subtype_injective h)
    simpa only [EvenBorelTorus.characters_torusSection] using he
  change Nat.card f.range = 9
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_prod,Nat.card_units,hF]

private theorem torus_index (hF : Nat.card F = 4) (P : Subgroup (Sp F))
    (ht : torus ≤ P) : ¬ 3 ∣ ((torus (F := F)).subgroupOf P).index := by
  have hc := (torus (F := F)).card_mul_index
  rw [torus_card hF,card_sp,hF] at hc
  have hi : (torus (F := F)).index = 108800 := by omega
  intro hd
  have h := hd.trans (relIndex_dvd_index_of_le ht)
  rw [hi] at h
  norm_num at h

private theorem point_escape (hF : Nat.card F = 4) (A : Subgroup (Sp F))
    (hA : IsPGroup 3 A) (hAP : A ≤ pointParabolic) :
    ¬ normalizer (A : Set (Sp F)) ≤ pointParabolic := by
  apply escape_of_torus_inverter pointParabolic torus A
    (torus_le_borel.trans inf_le_left) hA hAP
    (torus_index hF _ (torus_le_borel.trans inf_le_left))
    (SymplecticGroup.symJ (Fin 2) F) _ symJ_conj_torus
  intro hw
  have he := ((mem_pointParabolic_iff _).mp hw).2 0
  simp [SymplecticGroup.symJ,Matrix.J,Matrix.fromBlocks] at he

private theorem plane_escape (hF : Nat.card F = 4) (A : Subgroup (Sp F))
    (hA : IsPGroup 3 A) (hAP : A ≤ planeParabolic) :
    ¬ normalizer (A : Set (Sp F)) ≤ planeParabolic := by
  apply escape_of_torus_inverter planeParabolic torus A
    (torus_le_borel.trans inf_le_right) hA hAP
    (torus_index hF _ (torus_le_borel.trans inf_le_right))
    (SymplecticGroup.symJ (Fin 2) F) _ symJ_conj_torus
  intro hw
  have he := (mem_planeParabolic_iff _).mp hw 0 0
  simp [SymplecticGroup.symJ,Matrix.J,Matrix.fromBlocks] at he

/-- Every cubic subgroup in the normalizer of a proper local component
of Sp₄(4) has a normalizer escaping that parabolic. -/
theorem local_escape (hF : Nat.card F = 4) [CharP F 2]
    (S : Sylow 2 (Sp F)) (B A : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hA : IsPGroup 3 A) (hAB : A ≤ normalizer (B : Set (Sp F))) :
    ¬ normalizer (A : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) := by
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    (n := 2) hF (by decide) S B hB hproper
  have h := (map_mono (f := (MulAut.conj g).toMonoidHom) hAB).trans
    (le_normalizer_map _)
  apply escape_conjugate B A g
  rcases hg with hg | hg
  · rw [hg,DiagramAutomorphisms.pointLocal_normalizer (n := 2) hF (by decide)] at h ⊢
    exact point_escape hF _ (hA.map _) h
  · rw [hg,DiagramAutomorphisms.planeLocal_normalizer (n := 2) hF (by decide)] at h ⊢
    exact plane_escape hF _ (hA.map _) h

end Sp4Weyl

namespace G2Weyl
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.ParabolicApartment Atlas.SplitOctonion
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem torus_inverse (t : Model F) (ht : t ∈ splitTorus) :
    longest*t*longest⁻¹=t⁻¹ := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ht
  rw [longest_inv]
  exact (longest_torus a b).trans (torusHom.map_inv (a,b))

private theorem short_escape (hF : Nat.card F = 4) (A : Subgroup (Model F))
    (hA : IsPGroup 3 A) (hAP : A ≤ parabolic₁) :
    ¬ normalizer (A : Set (Model F)) ≤ parabolic₁ := by
  have ht : splitTorus (K := F) ≤ parabolic₁ := le_sup_right.trans borel_le_parabolic₁
  have hc := ((splitTorus (K := F)).subgroupOf parabolic₁).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe ht).toEquiv,card_splitTorus,
    ParabolicCells.short_card,card_borel,hF] at hc
  have hi : ¬ 3 ∣ ((splitTorus (K := F)).subgroupOf parabolic₁).index := by
    have he : ((splitTorus (K := F)).subgroupOf parabolic₁).index = 20480 := by omega
    rw [he]; decide
  apply escape_of_torus_inverter parabolic₁ splitTorus A ht hA hAP hi longest _ torus_inverse
  intro hw
  have he := (parabolic₁_le_shortPlaneStabilizer hw).1 _
    (basis_mem_shortPlane 0 (by decide)) 7 (by decide)
  rw [longest_apply] at he
  simp [basisVector] at he

private theorem long_escape (hF : Nat.card F = 4) (A : Subgroup (Model F))
    (hA : IsPGroup 3 A) (hAP : A ≤ parabolic₂) :
    ¬ normalizer (A : Set (Model F)) ≤ parabolic₂ := by
  have ht : splitTorus (K := F) ≤ parabolic₂ := le_sup_right.trans borel_le_parabolic₂
  have hc := ((splitTorus (K := F)).subgroupOf parabolic₂).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe ht).toEquiv,card_splitTorus,
    card_parabolic,hF] at hc
  have hi : ¬ 3 ∣ ((splitTorus (K := F)).subgroupOf parabolic₂).index := by
    have he : ((splitTorus (K := F)).subgroupOf parabolic₂).index = 20480 := by omega
    rw [he]; decide
  apply escape_of_torus_inverter parabolic₂ splitTorus A ht hA hAP hi longest _ torus_inverse
  intro hw
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp (parabolic_le_pointStabilizer hw)
  have he := congrFun ha 7
  rw [longest_apply] at he
  simp [basisVector] at he

/-- The longest Weyl element gives the same escape for both actual
G₂(4) parabolics and every cubic subgroup they contain. -/
theorem local_escape (hF : Nat.card F = 4) [CharP F 2]
    (S : Sylow 2 (Model F)) (B A : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hA : IsPGroup 3 A) (hAB : A ≤ normalizer (B : Set (Model F))) :
    ¬ normalizer (A : Set (Model F)) ≤ normalizer (B : Set (Model F)) := by
  have hlarge : 2 < Nat.card F := by omega
  let := Atlas.G2.isSimple hlarge
  have hn := local_normalizer_ne_top S B hB hproper
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement
    hlarge S B hB hproper
  let a := MulAut.conj g
  have hne : normalizer (B.map a.toMonoidHom : Set (Model F)) ≠ ⊤ := by
    rw [←map_equiv_normalizer_eq]
    intro ht
    apply hn
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  have h := (map_mono (f := a.toMonoidHom) hAB).trans (le_normalizer_map _)
  apply escape_conjugate B A g
  rcases hg with hg | hg
  · change B.map a.toMonoidHom = local₁ at hg
    have he : normalizer (local₁ (F := F) : Set (Model F)) = parabolic₁ :=
      le_antisymm ((isCoatom_iff_ge_of_le.mp HigherFieldResiduals.parabolic₁_isCoatom).2 _
        (hg ▸ hne) parabolic₁_normalizes_local₁) parabolic₁_normalizes_local₁
    rw [hg,he] at h ⊢
    exact short_escape hF _ (hA.map _) h
  · change B.map a.toMonoidHom = local₂ at hg
    have he : normalizer (local₂ (F := F) : Set (Model F)) = parabolic₂ :=
      le_antisymm ((isCoatom_iff_ge_of_le.mp HigherFieldResiduals.parabolic₂_isCoatom).2 _
        (hg ▸ hne) parabolic₂_le_normalizer_local₂) parabolic₂_le_normalizer_local₂
    rw [hg,he] at h ⊢
    exact long_escape hF _ (hA.map _) h

end G2Weyl

private theorem escape_through_local_two_kernel
    {G M : Type*} [Group G] [Finite G] [Group M] [Finite M]
    (T : Sylow 2 G) {B I J E : Subgroup G}
    (hB : B ∈ localCComponents T) (hI : I ∈ localCComponents T)
    (hBI : B < I) (hJI : J ≤ I)
    (hJN : J ≤ normalizer (B : Set G)) (hEJ : E ≤ J) (hE : IsPGroup 3 E)
    (q : I →* M) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (escape : ∀ (S : Sylow 2 M) (C A : Subgroup M),
      C ∈ localCComponents S → C ≠ ⊤ → IsPGroup 3 A →
      A ≤ normalizer (C : Set M) → ¬ normalizer (A : Set M) ≤ normalizer (C : Set M)) :
    ¬ I ⊓ normalizer (E : Set G) ≤ J := by
  obtain ⟨P,hP,hBP⟩ := ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_in_local_overgroup
    T hB hI hBI.le
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using
      hI.subgroupOf_of_le (show I ≤ I from le_rfl) (show I ≤ I ⊔ T from le_sup_left)
  have hproper : (B.subgroupOf I).map q ≠ ⊤ := by
    intro he
    have he' : (B.subgroupOf I).map q = (⊤ : Subgroup I).map q := by
      rw [he,map_top_of_surjective q hq]
    have ht := local_cComponent_eq_of_map_eq hBP htop le_top q
      (hk.le_sylow_of_normal P) he'
    exact hBI.not_ge (subgroupOf_eq_top.mp ht)
  have hJN' : J.subgroupOf I ≤ normalizer (B.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hBI.le]
    exact comap_mono hJN
  have hJq := (map_mono (f := q) hJN').trans (le_normalizer_map q)
  have hEq : (E.subgroupOf I).map q ≤ (J.subgroupOf I).map q :=
    map_mono (comap_mono hEJ)
  have hn := escape (P.mapSurjective hq) ((B.subgroupOf I).map q) ((E.subgroupOf I).map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hBP q) hproper
    (hE.comap_subtype.map q) (hEq.trans hJq)
  have he := normalizer_not_le_of_two_kernel q hq hk (J.subgroupOf I) (E.subgroupOf I)
    (p := 3) (by decide) hE.comap_subtype (fun h => hn (h.trans hJq))
  intro h
  apply he
  rw [←subgroupOf_normalizer_eq (hEJ.trans hJI)]
  intro x hx
  exact h ⟨x.property,hx⟩

/-- Escape from the original local supplement lifts through the literal
two-core quotient. No compatible choice of a new Cartan or action is assumed. -/
theorem local_two_core_cubic_normalizer_escape
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {B I J E : Subgroup G}
    (hB : B ∈ localCComponents T) (hI : I ∈ localCComponents T)
    (hBI : B < I) (hJI : J ≤ I)
    (hJN : J ≤ normalizer (B : Set G)) (hEJ : E ≤ J) (hE : IsPGroup 3 E)
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨ ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4) :
    ¬ I ⊓ normalizer (E : Set G) ≤ J := by
  rcases hm with hm | hm
  all_goals
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (show Nat.card F = 2^2 by simpa using hF)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 q.ker := by
      rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
      exact pCore_isPGroup
    apply escape_through_local_two_kernel T hB hI hBI hJI hJN hEJ hE q hq hk
  · exact Sp4Weyl.local_escape hF
  · exact G2Weyl.local_escape hF

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original common-Q linear triangle supplies a Weyl normalizer escape
for both equal cubic kernels, outside the literal L₂X. -/
theorem linear_triangle_cubic_normalizer_escape_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    (¬ I ⊓ normalizer ((X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) : Set G) ≤ f.Li 1 ⊔ X) ∧
      (¬ I ⊓ normalizer ((X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) : Set G) ≤ f.Li 1 ⊔ X) := by
  intro I
  obtain ⟨_,hIL,_,hXI,_,_,_,hmodels⟩ := linear_triangle_join_two_models_of_common_normal
    D S m f hd hfix hX hK hLK hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  obtain ⟨_,hc,_,hnX⟩ := linear_triangle_proper_residuals D S m f hd hX hK hLK hK₀ hK₀K hk hp
  have hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 1⟩⟩
  have hu : f.IsInnerUnique := by
    intro i U hU hT
    exact (SL3.flag_inner_unique D S m i U hU hT).trans
      (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  have hXC : X ≤ normalizer (f.Li 1 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
    exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hp3 : IsPGroup 3 (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) :=
    IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hescape := local_two_core_cubic_normalizer_escape T
    (flag_mem_local_of_model D S f 1 hm).1 hIL.1 hc
    (sup_le (show f.Li 1 ≤ I from le_sup_right) hXI)
    (sup_le (f.Li 1).le_normalizer hXC)
    (inf_le_left.trans (show X ≤ f.Li 1 ⊔ X from le_sup_right)) hp3 hmodels
  refine ⟨hescape,?_⟩
  simpa only [linear_four_cartan_kernels_eq D S m hd f hX] using hescape

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
