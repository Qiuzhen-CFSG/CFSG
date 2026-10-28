module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality
public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Rank-one upper components in the original A₆ chain

The Bender carriers have solvable proper full-Sylow overgroups, so any
contained local component is the whole upper component. Perfect central
covers inherit this argument. For odd PSL₂ over a prime or its square,
the actual lower image in IT/O₂(IT) retains its A₆ two-core quotient.
Dickson's prime-field obstruction and the proved quadratic-field embedding
theorem therefore exclude every proper enlargement.

These are unconditional branches of the 13.3.2 maximality argument, using
A.3.12(1,8), printed pp.47–48, and 13.1.2(5), p.866. The final consumer
uses the unchanged NaturalSetup and does not assume a global model list.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality
open CFSG.Quasithin CFSG.Quasithin.Chapter1
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem local_eq_of_bender_quotient {T L I : Subgroup G}
    (hL : L ∈ Chapter1.L G T) (hI : I ∈ Chapter1.L G T) (hLI : L ≤ I)
    (hm : ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)) : L = I :=
  Chapter13.Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups hI hL hLI
    (bender_solvable_proper_sylow_overgroup hm)

theorem local_eq_of_central_bender_quotient {T L I : Subgroup G}
    (hL : L ∈ Chapter1.L G T) (hI : I ∈ Chapter1.L G T) (hLI : L ≤ I)
    (hm : ClassificationModels.IsBenderModel
      ((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I))) : L = I := by
  let : Group.IsPerfect I := Chapter1.mem_L_isPerfect hI
  apply Chapter13.Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups hI hL hLI
  exact SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (by simp)
    (bender_solvable_proper_sylow_overgroup hm)

omit [Finite G] in
private theorem local_eq_of_images_eq (T : Sylow 2 G) {L I : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    (he : (L.subgroupOf (I ⊔ (T : Subgroup G))).map
        (QuotientGroup.mk' (pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G))) =
      radicalLocalImage (T : Subgroup G) I) : L = I := by
  let J := I ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 J)
  have hLJ : L ≤ J := hLI.trans le_sup_left
  have hpre : I.subgroupOf J ≤ L.subgroupOf J ⊔ pCore 2 J := by
    have hh := map_le_iff_le_comap.mp he.ge
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using hh
  have hcore : pCore 2 J ≤ (T : Subgroup G).subgroupOf J := by
    simpa only [Sylow.coe_subtype] using
      pCore_isPGroup.le_sylow_of_normal (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
  have hIJ : I ≤ L ⊔ (T : Subgroup G) := by
    intro x hx
    have hm := hpre (show (⟨x, (show I ≤ J from le_sup_left) hx⟩ : J) ∈ I.subgroupOf J from hx)
    have hh : L.subgroupOf J ⊔ pCore 2 J ≤ (L ⊔ (T : Subgroup G)).subgroupOf J :=
      sup_le (comap_mono le_sup_left) (hcore.trans (comap_mono le_sup_right))
    exact hh hm
  have hj : I ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G) :=
    le_antisymm (sup_le hIJ le_sup_right) (sup_le_sup_right hLI _)
  have hi : (I.subgroupOf (L ⊔ (T : Subgroup G))).IsCComponent := hj ▸ hI.1
  have hh := hL.1.eq_of_le hi (comap_mono hLI)
  simpa only [map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le hIJ] using
    congrArg (map (L ⊔ (T : Subgroup G)).subtype) hh

private noncomputable def imageCoreEquiv (J : Subgroup G) (L : Subgroup G) (hLJ : L ≤ J) :
    (L ⧸ pCore 2 L) ≃*
      (((L.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) ⧸
        pCore 2 ((L.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)))) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.subgroupMap (L.subgroupOf J)
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  exact (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLJ).symm
      (pCore_map_iso 2 (subgroupOfEquivOfLe hLJ).symm)).trans
    (f.pCoreQuotientEquiv (q.subgroupMap_surjective _) hk)

private theorem quadratic_image_models (T : Sylow 2 G) {L I : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (p ^ 2)) :
    L = I ∨ (3 < p ∧ ClassicalGroup.IsPSL
      ((L.subgroupOf (I ⊔ (T : Subgroup G))).map
        (QuotientGroup.mk' (pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)))) 2 p) := by
  let J := I ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := (L.subgroupOf J).map q
  let P := (I.subgroupOf J).map q
  have hLJ : L ≤ J := hLI.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hLlocal : L.subgroupOf J ∈ Chapter1.L J (S : Subgroup J) := by
    simpa only [S, Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf (show (T : Subgroup G) ≤ J from le_sup_right) hLJ).mp
        (show L ∈ Chapter1.LIn J (T : Subgroup G) from ⟨hLJ, hL⟩)
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hB : B ∈ ChapterA.Section03.localCComponents (Sq : Subgroup _) := by
    simpa only [Sq, B, Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hLlocal
  let := pCore_isNilpotent (p := 2) (G := J)
  have hP : P.IsCComponent := hI.1.map_quotient (pCore 2 J)
  have hmP : ClassicalGroup.IsPSL P 2 (p ^ 2) :=
    hm.of_mulEquiv (radicalLocalQuotientEquiv hI).symm
  by_cases he : B = P
  · exact .inl (local_eq_of_images_eq T hL hI hLI he)
  · exact .inr (proper_quadraticPSL2_models Sq hB hP
      (map_mono (comap_mono hLI)) he hp ho hmP)

/-- A prime-field PSL₂ upper quotient cannot contain the original A₆ section. -/
theorem local_eq_of_prime_psl_quotient {L I : Subgroup G} (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 p) : L = I := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨F, _, _, hF, ⟨eI⟩⟩ := hm
  let := pCore_isNilpotent (p := 2) (G := I)
  let m : Group.SolvableKernelModel I (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) := {
    kernel := pCore 2 I
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := eI }
  let U := L.subgroupOf I
  let f : U →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp
      (subgroupOfEquivOfLe hLI).toMonoidHom)
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (subgroupOfEquivOfLe hLI).surjective)
  obtain ⟨W, g, hg⟩ := m.simple_section (Group.IsPerfect.not_isSolvable _) U f hf
  exact (prime_psl_no_six_section ho hlarge hF W g hg).elim

/-- The quadratic odd-field branch of A.3.12 forces equality of the original
local components. Both quotient images use IT/O₂(IT). -/
theorem local_eq_of_quadratic_psl_quotient (T : Sylow 2 G) {L I : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (p ^ 2)) : L = I := by
  rcases quadratic_image_models T hL hI hLI hp ho hm with he | ⟨hlarge, hmB⟩
  · exact he
  · let : Fact p.Prime := ⟨hp⟩
    let J := I ⊔ (T : Subgroup G)
    let B := (L.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
    let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6) :=
      (imageCoreEquiv J L (hLI.trans le_sup_left)).symm.trans e
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hmB
    let f : (⊤ : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) →*
        alternatingGroup (Fin 6) :=
      eB.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 B)).comp
        (a.symm.toMonoidHom.comp topEquiv.toMonoidHom))
    have hf : Function.Surjective f := eB.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (a.symm.surjective.comp topEquiv.surjective))
    exact (prime_psl_no_six_section ho hlarge hF ⊤ f hf).elim

/-- All odd PSL₂ rows in the actual Theorem C catalogue, including p²=9. -/
theorem local_eq_of_odd_psl_quotient (T : Sylow 2 G) {L I : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {p a : ℕ} (hp : p.Prime) (ho : Odd p) (ha : a = 1 ∨ a = 2)
    (hsimple : 4 ≤ p ^ a)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (p ^ a)) : L = I := by
  rcases ha with rfl | rfl
  · simp only [pow_one] at hm hsimple
    exact local_eq_of_prime_psl_quotient hLI e hp ho (by omega) hm
  · exact local_eq_of_quadratic_psl_quotient T hL hI hLI e hp ho hm

open Section08.SourceCompletion

/-- Original A₆ consumer: every Bender, central Bender, or odd PSL₂ upper
quotient already gives maximality along this actual local-component chain. -/
theorem NaturalSetup.local_eq_of_rankOne_quotient
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ I : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    (hm : ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) ∨
      ClassificationModels.IsBenderModel ((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ∨
      ∃ p a : ℕ, p.Prime ∧ Odd p ∧ (a = 1 ∨ a = 2) ∧ 4 ≤ p ^ a ∧
        ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (p ^ a)) : L = I := by
  have hL := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    d.counterexample.local_component).1
  rcases hm with hm | hm | ⟨p, a, hp, ho, ha, hs, hm⟩
  · exact local_eq_of_bender_quotient hL hI hLI hm
  · exact local_eq_of_central_bender_quotient hL hI hLI hm
  · exact local_eq_of_odd_psl_quotient T hL hI hLI e hp ho ha hs hm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality

