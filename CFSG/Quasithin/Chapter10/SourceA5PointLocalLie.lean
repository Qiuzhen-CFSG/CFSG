module
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalEmbedding
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimpleDispatch
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree

/-!
# Original point markings in the rank-two Lie families

The prescribed full point Sylow restricts to the original containing component
I and maps through I/Z(I). Transporting this exact Sylow and the image of L to
the actual Lie model supplies the hypotheses of the existing A₅ local-placement
theorems. They force the field to have four elements. In the symplectic and G₂
rows, composing the original model equivalence with the proved conjugation
retains the literal subgroup marking needed by the quasisimple dispatcher.
The resulting consumers give the original point-component alternative.

Catalogue wrappers retain the actual central quotient, including arbitrary
perfect central covers. The binary derived G₂ endpoint has no A₅ section;
the binary projective-derived symplectic endpoint and PSL₃(2) are smaller than
the source lower bound 960. No embedding marking is supplied as a hypothesis.

Source: Aschbacher–Smith A.3.12/A.3.14 and 10.2.9, printed pp.750–752.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
open Theory.SpecificGroups.SymplecticFour
universe u w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem local_model_transport {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (eH : H ≃* K) (S : Sylow 2 H) (B : Subgroup H)
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    let A := B.map eH.toMonoidHom
    A ∈ localCComponents (S.mapSurjective (f := eH.toMonoidHom) eH.surjective) ∧ A ≠ ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5)) := by
  let : Group.IsSolvable eH.toMonoidHom.ker := by
    rw [eH.toMonoidHom.ker_eq_bot eH.injective]
    infer_instance
  let a := eH.subgroupMap B
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hl eH.toMonoidHom, ?_,
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eB⟩⟩
  intro ht
  apply hp
  apply map_injective (f := eH.toMonoidHom) eH.injective
  rw [map_top_of_surjective _ eH.surjective]
  exact ht

include D in
/-- The G₂ point row obtains its field and marking from the original local data. -/
theorem source_a5_point_g2_quasisimple_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {F : Type w} [Field F] [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
    (eI : (I ⧸ center I) ≃* Atlas.G2.Model F) :
    Nat.card F = 4 ∧ SourceA5PointQuasisimpleMarking.{u,w} L I := by
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let A := B.map eI.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hlA,hpA,⟨eA⟩⟩ := local_model_transport eI R B hl hp eB
  obtain ⟨hF,g,hg⟩ := SourceEmbeddings.FiveLocalFF.G2.five_section_placement hq
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hlA hpA eA
  refine ⟨hF,.g2 hF (eI.trans (MulAut.conj g)) ?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
  simpa only [A,B,q,map_map, he, MonoidHom.comp_assoc] using hg

include D in
/-- The symplectic point row obtains its field and marking from the original local data. -/
theorem source_a5_point_symplectic_quasisimple_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hnF : 1 < n)
    (eI : (I ⧸ center I) ≃* Sp F) :
    Nat.card F = 4 ∧ SourceA5PointQuasisimpleMarking.{u,w} L I := by
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let A := B.map eI.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hlA,hpA,⟨eA⟩⟩ := local_model_transport eI R B hl hp eB
  obtain ⟨h4,g,hg⟩ := SourceEmbeddings.FiveLocalFF.symplectic_five_section_placement hF hnF
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hlA hpA eA
  refine ⟨h4,.symplectic h4 (eI.trans (MulAut.conj g)) ?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
  simpa only [A,B,q,map_map, he, MonoidHom.comp_assoc] using hg

include D in
/-- The proved G₂ marking feeds the original point alternative. -/
theorem source_a5_point_g2_local_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (t : G)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    {F : Type w} [Field F] [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
    (eI : (I ⧸ center I) ≃* Atlas.G2.Model F) :
    SourceA5PointComponentAlternative D e t I :=
  source_a5_point_alternative_of_quasisimple_marking D e t I hLI.le hv hNI hcross
    (source_a5_point_g2_quasisimple_marking D e hn (hcross hv) hv0 hs hLI hIX hI hq eI).2

include D in
/-- The proved symplectic marking feeds the original point alternative. -/
theorem source_a5_point_symplectic_local_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (t : G)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hnF : 1 < n)
    (eI : (I ⧸ center I) ≃* Sp F) :
    SourceA5PointComponentAlternative D e t I :=
  source_a5_point_alternative_of_quasisimple_marking D e t I hLI.le hv hNI hcross
    (source_a5_point_symplectic_quasisimple_marking D e hn (hcross hv) hv0 hs hLI hIX hI hF hnF eI).2

/-- The binary derived G₂ endpoint cannot contain the original A₅ section. -/
theorem source_a5_not_g2_binary_containing_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I)
    {F : Type w} [Field F] [Finite F] (hF : Nat.card F = 2)
    (eI : (I ⧸ center I) ≃* commutator (Atlas.G2.Model F)) : False := by
  let B := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  let a := eI.subgroupMap B
  let eB := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (source_a5_containing_center_image_quotient e hLI)
  exact SourceEmbeddings.FiveLocalFF.G2.binary_derived_excluded hF
    (B.map eI.toMonoidHom) eB

include D in
/-- The catalogue G₂ carrier forces the field-four row and supplies its marking. -/
theorem source_a5_point_g2_model_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hnF : 2 ≤ n) (hmodel : ClassificationModels.IsG2At (I ⧸ center I) (2 ^ n)) :
    n = 2 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨h4,hm⟩ := source_a5_point_g2_quasisimple_marking D e hn hvL hv0 hs hLI hIX hI hq eI
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) ?_,hm⟩
  simpa only [← hF] using h4

include D in
/-- The projective symplectic carrier supplies the actual symplectic marking. -/
theorem source_a5_point_symplectic_model_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hnF : 2 ≤ n) (hmodel : ClassicalGroup.IsPSp (I ⧸ center I) 2 (2 ^ n)) :
    n = 2 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨h4,hm⟩ := source_a5_point_symplectic_quasisimple_marking D e hn hvL hv0 hs hLI hIX hI
    hF (by omega) (eI.trans (EvenProjective.equiv (F := F)).symm)
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) ?_,hm⟩
  simpa only [← hF] using h4

include D in
/-- The original A₅ image and its core-center bound require at least 960 elements. -/
theorem source_a5_containing_center_quotient_card_ge
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) : 960 ≤ Nat.card (I ⧸ center I) := by
  let B := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  have hc : 16 ≤ Nat.card (pCore 2 B) :=
    (source_a5_marked_core_center_card D e hLI (MulEquiv.refl B)).trans
      (card_le_card_group (center (pCore 2 B)))
  have hb : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr (source_a5_containing_center_image_quotient e hLI).toEquiv]
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hB : 960 ≤ Nat.card B := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),hb]
    omega
  exact hB.trans (card_le_card_group B)

include D in
/-- The binary projective-derived symplectic catalogue endpoint is too small. -/
theorem source_a5_not_symplectic_binary_containing_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I)
    (eI : (I ⧸ center I) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False := by
  have hc := source_a5_containing_center_quotient_card_ge D e hLI
  rw [Nat.card_congr (eI.trans Binary.projectiveDerivedEquivAlternatingSix).toEquiv] at hc
  rw [nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

include D in
/-- The original linear-three point row has field four, including exclusion of q = 2. -/
theorem source_a5_point_linear_three_quasisimple_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hnF : 1 ≤ n)
    (eI : (I ⧸ center I) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    Nat.card F = 4 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  have hn2 : 1 < n := by
    by_contra! h
    have he : n = 1 := by omega
    have hc := source_a5_containing_center_quotient_card_ge D e hLI.le
    rw [Nat.card_congr eI.toEquiv,Matrix.PSL3.LinearThree.card_projective F,hF,he] at hc
    norm_num at hc
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let A := B.map eI.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hlA,hpA,⟨eA⟩⟩ := local_model_transport eI R B hl hp eB
  obtain ⟨h4,_⟩ := SourceEmbeddings.FiveLocalFF.linear_three_five_section_placement hF hn2
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hlA hpA eA
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,h4,Matrix.PSL3Four.card_F])
  exact ⟨h4,.linear (eI.trans (Atlas.fieldEquivPSL 3 a))⟩

include D in
/-- The catalogue linear-three carrier discharges its marking input. -/
theorem source_a5_point_linear_three_model_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hnF : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL (I ⧸ center I) 3 (2 ^ n)) :
    n = 2 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨h4,hm⟩ := source_a5_point_linear_three_quasisimple_marking D e hn hvL hv0 hs hLI hIX hI
    hF hnF eI
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) ?_,hm⟩
  simpa only [← hF] using h4

include D in
/-- The proved linear-three placement feeds the original point alternative. -/
theorem source_a5_point_linear_three_local_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (t : G)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hnF : 1 ≤ n)
    (eI : (I ⧸ center I) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    SourceA5PointComponentAlternative D e t I :=
  source_a5_point_alternative_of_quasisimple_marking D e t I hLI.le hv hNI hcross
    (source_a5_point_linear_three_quasisimple_marking D e hn (hcross hv) hv0 hs hLI hIX hI hF hnF eI).2

end CFSG.Quasithin.Chapter10
