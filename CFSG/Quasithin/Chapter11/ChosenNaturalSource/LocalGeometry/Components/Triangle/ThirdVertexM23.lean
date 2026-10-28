module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexComparisonSp4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveOddModels
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion

/-!
# The marked M₂₃ comparison at the third vertex

A full Sylow normalizing an A₅ two-core section forces its two-core to be
nontrivial: otherwise its faithful action on A₅ contradicts the Sylow order.
The native M₂₃ elementary-normalizer calculation then puts its normalizer
inside the fixed heptad or triple stabilizer. The heptad quotient is the
actual A₇; its normalized A₅ fixes two letters, so it cannot admit the
order-nine Cartan. Both original marked locals consequently lie in the
same proper triple stabilizer and cannot generate M₂₃.

The final comparison carries both local sections, the full Sylow and the
same Cartan through the literal two-core projection of I = K₀ ∨ L₂. Its
consumer is ThirdVertexRecognitionSp4. The common-normal existence,
source SL₃(4) exclusion, maximal-faithful placement and both orientations
remain with qt-d-1222-natural-relative-components; earlier flag and Cartan
inputs retain their existing producers and final discharge by
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith A.3.14(7) and 11.1.2, printed pp.49,762--764.
The imported native heptad and triple calculations retain their source
attribution; no extra Mathieu catalogue is assumed here.
-/

open scoped Pointwise
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open FiveLocalFF.SolvableQuotients M23Geometry
public noncomputable section

private theorem m23_core_nontrivial (S : Sylow 2 M23) (B : Subgroup M23)
    (hn : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : pCore 2 B ≠ ⊥ := by
  intro hc
  let e : B ≃* alternatingGroup (Fin 5) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans eB
  apply AlternatingFive.not_sixteen_dvd_of_no_involution S B e hn ?_
    (by rw [m23_order]; decide)
  intro t ht ht2
  have hb : B ≤ centralizer ({t} : Set M23) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (ht b hb)
  have h5 : 5 ∣ Nat.card B := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hd := h5.trans (card_dvd_of_le hb)
  rw [card_centralizer_eq_of_isConj t involutionRepresentative
    (involutions_isConj t involutionRepresentative ht2 involutionRepresentative_order),
    involutionRepresentative_centralizer_card] at hd
  norm_num at hd

private theorem normalizer_preserves_fixed
    {A Ω : Type*} [Group A] [MulAction A Ω] (B : Subgroup A)
    {g : A} (hg : g ∈ normalizer (B : Set A)) {x : Ω}
    (hx : x ∈ MulAction.fixedPoints B Ω) :
    g • x ∈ MulAction.fixedPoints B Ω := by
  intro b
  have h := hx ⟨g⁻¹ * b.val * g,(mem_normalizer_iff''.mp hg b.val).mp b.property⟩
  simpa only [mul_smul,inv_smul_smul,smul_inv_smul,Subgroup.smul_def] using
    congrArg (fun y => g • y) h

private theorem seven_no_nine_normalizer (S : Sylow 2 (alternatingGroup (Fin 7)))
    (B X : Subgroup (alternatingGroup (Fin 7)))
    (hn : (S : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (B : Set _))
    (eB : B ≃* alternatingGroup (Fin 5))
    (hx : X ≤ normalizer (B : Set _)) (hc : Nat.card X = 9) : False := by
  classical
  let F := MulAction.fixedPoints B (Fin 7)
  have hF : Nat.card F = 2 := by
    simpa only [Nat.card_coe_set_eq] using
      Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B eB S hn
  have hp (g : X) (x : Fin 7) : g.val.val x ∈ F ↔ x ∈ F := by
    constructor
    · intro h
      have hh := normalizer_preserves_fixed B (hx (X.inv_mem g.property)) h
      change (g.val)⁻¹ • (g.val • x) ∈ MulAction.fixedPoints B (Fin 7) at hh
      simpa only [inv_smul_smul] using hh
    · exact normalizer_preserves_fixed B (hx g.property)
  let a : X →* Equiv.Perm F := {
    toFun g := g.val.val.subtypePerm (hp g)
    map_one' := by ext x; rfl
    map_mul' := by intros; ext x; rfl }
  have h2 : Nat.card a.range ∣ 2 := by
    have hh := a.range.card_subgroup_dvd_card
    rwa [Nat.card_perm,hF,show Nat.factorial 2 = 2 from rfl] at hh
  have h9 : Nat.card a.range ∣ 9 := by
    rw [←hc,←index_ker]
    exact a.ker.index_dvd_card
  have ha : a.range = ⊥ := card_eq_one.mp (Nat.dvd_one.mp (Nat.dvd_gcd h2 h9))
  have hfix (g : X) (x : F) : g.val.val x.val = x.val := by
    have he : a g = 1 := mem_bot.mp (ha ▸ (show a g ∈ a.range from ⟨g,rfl⟩))
    exact congrArg Subtype.val (DFunLike.congr_fun he x)
  obtain ⟨i,j,hij,hijF⟩ := Set.ncard_eq_two.mp
    (Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B eB S hn)
  let P := fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))
  have hXP : X ≤ P := by
    intro g hg x
    exact hfix ⟨g,hg⟩ ⟨x.val,by change x.val ∈ MulAction.fixedPoints B (Fin 7); rw [hijF]; exact x.property⟩
  have hPc : Nat.card P = 60 := by
    let e := Atlas.Families.Alternating.stabilizerComplementEquiv ({i,j} : Finset (Fin 7))
    have hset : (({i,j} : Finset (Fin 7)) : Set (Fin 7)) = {i,j} := by ext x; simp
    have hc : Nat.card (↑(({i,j} : Finset (Fin 7))ᶜ)) = 5 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl]
      simp [hij]
    let : Nontrivial (↑(({i,j} : Finset (Fin 7))ᶜ)) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        simpa only [←Nat.card_eq_fintype_card,hc] using (by decide : 1 < 5))
    change Nat.card (fixingSubgroup _ _) = 60
    rw [←hset,Nat.card_congr e.toEquiv,nat_card_alternatingGroup,hc]
    norm_num
  have hd := card_dvd_of_le hXP
  rw [hc,hPc] at hd
  norm_num at hd


private theorem card_nine_image_of_two_kernel {A H : Type*} [Group A] [Finite A] [Group H]
    (q : A →* H) (hk : IsPGroup 2 q.ker) (X : Subgroup A) (hX : Nat.card X = 9) :
    Nat.card (X.map q) = 9 := by
  let f := q.subgroupMap X
  have hker : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨n,hn⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime 9 (Nat.card f.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have he := f.ker.card_mul_index
  rw [index_eq_card,Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective X)).toEquiv,hX] at he
  exact Nat.dvd_antisymm (hX ▸ X.card_map_dvd q)
    (hcop.dvd_of_dvd_mul_left (he.symm ▸ dvd_refl 9))

private theorem heptad_not_nine_normalizer (S : Sylow 2 M23)
    (B X : Subgroup M23)
    (hn : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hx : X ≤ normalizer (B : Set M23)) (hc : Nat.card X = 9)
    {F : Finset (Fin 23)} (hF : F ∈ m23Blocks)
    (hS : (S : Subgroup M23) ≤ MulAction.stabilizer M23 F)
    (hB : B ≤ MulAction.stabilizer M23 F) (hX : X ≤ MulAction.stabilizer M23 F) : False := by
  let H := MulAction.stabilizer M23 F
  obtain ⟨_,_,q,hq,hk⟩ := heptad_stabilizer_local_structure hF (MulEquiv.refl H)
  let P := S.subtype hS
  let D := B.subgroupOf H
  let Y := X.subgroupOf H
  let b := subgroupOfEquivOfLe hB
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hd : IsPGroup 2 (q.subgroupMap D).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eD := alternatingGroup.SevenFiveSection.imageFiveEquiv q D hd (bq.trans eB)
  have hnD : (P : Subgroup H) ≤ normalizer (D : Set H) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hB]
    exact comap_mono hn
  have hxD : Y ≤ normalizer (D : Set H) := by
    rw [←subgroupOf_normalizer_eq hB]
    exact comap_mono hx
  exact seven_no_nine_normalizer (P.mapSurjective hq) (D.map q) (Y.map q)
    ((map_mono hnD).trans (le_normalizer_map q)) eD
    ((map_mono hxD).trans (le_normalizer_map q))
    (card_nine_image_of_two_kernel q hk Y
      ((Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv).trans hc))

private theorem aligned_m23_marked_five_le_triple (B X : Subgroup M23)
    (hn : FusionCertificate.subgroup ≤ normalizer (B : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hx : X ≤ normalizer (B : Set M23)) (hc : Nat.card X = 9) :
    B ≤ MulAction.stabilizer M23 SylowTwoLocals.Coverage.fixedTriple := by
  let N := normalizer (B.pCoreIn 2 : Set M23)
  have hN : IsTwoLocal N := by
    refine ⟨B.pCoreIn 2,?_,pCore_isPGroup.map B.subtype,rfl⟩
    intro he
    exact m23_core_nontrivial FusionCertificate.sylow B hn eB
      ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hBN : B ≤ N := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hSN : FusionCertificate.subgroup ≤ N := hn.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hXN : X ≤ N := hx.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨M,hNM,hM⟩ := Finite.exists_le_maximal hN
  obtain ⟨R,hR,_,he,hMR⟩ := exists_normal_elementary_normalizer_of_sylow_le
    FusionCertificate.sylow hM (hSN.trans hNM)
  let A := R.map (FusionCertificate.sylow : Subgroup M23).subtype
  have hAS : A ≤ FusionCertificate.subgroup := map_subtype_le R
  have hAN : FusionCertificate.subgroup ≤ normalizer (A : Set M23) := hMR ▸ hSN.trans hNM
  have hA : A ≠ ⊥ := fun h => hR ((map_eq_bot_iff_of_injective R
    (FusionCertificate.sylow : Subgroup M23).subtype_injective).mp h)
  let := he
  have hEA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  rcases SylowTwoLocals.Coverage.normal_elementary_normalizer_coverage A hAS hAN hA hEA
    with hh | ht
  · have hMF : M ≤ MulAction.stabilizer M23 FourNormalizers.fixedSet := hMR ▸ hh
    exact (heptad_not_nine_normalizer FusionCertificate.sylow B X hn eB hx hc
      FourNormalizers.fixedSet_mem ((hSN.trans hNM).trans hMF)
      ((hBN.trans hNM).trans hMF) ((hXN.trans hNM).trans hMF)).elim
  · exact (hBN.trans hNM).trans (hMR ▸ ht)


/-- At one full Sylow, both original A₅ sections normalized by an order-nine
subgroup lie in the same proper triple stabilizer, so cannot generate M₂₃. -/
theorem m23_not_generated_by_marked_five_pair (S : Sylow 2 M23)
    (B C X : Subgroup M23)
    (hnB : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (hnC : (S : Subgroup M23) ≤ normalizer (C : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hxB : X ≤ normalizer (B : Set M23)) (hxC : X ≤ normalizer (C : Set M23))
    (hc : Nat.card X = 9) : B ⊔ C ≠ ⊤ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 S FusionCertificate.sylow
  let a := MulAut.conj g
  let f := a.toMonoidHom
  have hs : (S : Subgroup M23).map f = FusionCertificate.subgroup :=
    congrArg Sylow.toSubgroup hg
  have step (D : Subgroup M23)
      (hnD : (S : Subgroup M23) ≤ normalizer (D : Set M23))
      (eD : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 5))
      (hxD : X ≤ normalizer (D : Set M23)) :
      D.map f ≤ MulAction.stabilizer M23 SylowTwoLocals.Coverage.fixedTriple := by
    let d := a.subgroupMap D
    let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    exact aligned_m23_marked_five_le_triple (D.map f) (X.map f)
      (hs ▸ (map_mono hnD).trans (le_normalizer_map f)) (dq.symm.trans eD)
      ((map_mono hxD).trans (le_normalizer_map f))
      ((card_map_of_injective a.injective).trans hc)
  intro hgen
  have htop : (⊤ : Subgroup M23) ≤
      MulAction.stabilizer M23 SylowTwoLocals.Coverage.fixedTriple := by
    rw [←map_top_of_surjective f a.surjective,←hgen,Subgroup.map_sup]
    exact sup_le (step B hnB eB hxB) (step C hnC eC hxC)
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq M23 (0 : Fin 23) (1 : Fin 23)
  have hh := Finset.smul_mem_smul_finset (a := t)
    (show (0 : Fin 23) ∈ SylowTwoLocals.Coverage.fixedTriple by decide)
  rw [show t • SylowTwoLocals.Coverage.fixedTriple = SylowTwoLocals.Coverage.fixedTriple
    from htop (mem_top t),ht] at hh
  exact (by decide : (1 : Fin 23) ∉ SylowTwoLocals.Coverage.fixedTriple) hh

/-- Both marked residuals and their common order-nine Cartan survive the
literal two-core projection of their join; the quotient is not M₂₃. -/
theorem local_join_not_m23_of_marked_cartan
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C I X : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hI : I ∈ localCComponents T) (hBI : B ≤ I) (hCI : C ≤ I)
    (hnB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hnC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hgen : B ⊔ C = I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (hXI : X ≤ I) (hxB : X ≤ normalizer (B : Set G))
    (hxC : X ≤ normalizer (C : Set G)) (hc : Nat.card X = 9) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* M23) := by
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI
  have hCS : C.subgroupOf I ∈ localCComponents S := hS.symm ▸ local_restrict hC hCI
  rintro ⟨e⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have step (D : Subgroup G) (hD : D ≤ I)
      (hDS : D.subgroupOf I ∈ localCComponents S)
      (hnD : (T : Subgroup G) ≤ normalizer (D : Set G))
      (hxD : X ≤ normalizer (D : Set G))
      (hmD : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 4) :
      (S : Subgroup I).map q ≤ normalizer ((D.subgroupOf I).map q : Set M23) ∧
      (X.subgroupOf I).map q ≤ normalizer ((D.subgroupOf I).map q : Set M23) ∧
      Nonempty ((((D.subgroupOf I).map q) ⧸ pCore 2 ((D.subgroupOf I).map q)) ≃*
        alternatingGroup (Fin 5)) := by
    have hn : (S : Subgroup I) ≤ normalizer (D.subgroupOf I : Set I) := by
      rw [hS,←subgroupOf_normalizer_eq hD]
      exact comap_mono hnD
    have hx : X.subgroupOf I ≤ normalizer (D.subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq hD]
      exact comap_mono hxD
    refine ⟨(map_mono hn).trans (le_normalizer_map q),
      (map_mono hx).trans (le_normalizer_map q),?_⟩
    obtain ⟨F,_,_,hF,⟨ef⟩⟩ := hmD
    obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    let d := subgroupOfEquivOfLe hD
    let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    exact section_map q (D.subgroupOf I) hDS (dq.trans (ef.trans ea))
  obtain ⟨hb,hxb,⟨eb⟩⟩ := step B hBI hBS hnB hxB hmB
  obtain ⟨hc',hxc,⟨ec⟩⟩ := step C hCI hCS hnC hxC hmC
  apply m23_not_generated_by_marked_five_pair (S.mapSurjective hq)
    ((B.subgroupOf I).map q) ((C.subgroupOf I).map q) ((X.subgroupOf I).map q)
    hb hc' eb ec hxb hxc
    (card_nine_image_of_two_kernel q hk (X.subgroupOf I)
      ((Nat.card_congr (subgroupOfEquivOfLe hXI).toEquiv).trans hc))
  rw [←Subgroup.map_sup,←subgroupOf_sup hBI hCI,hgen,subgroupOf_self,map_top_of_surjective q hq]

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
