module
public import Theory.GroupTheory.PerfectNormalizerLift
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximality
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallModels


/-!
# Matching the fields in split and Ree relative-component embeddings

Restrict the original full Sylow to the containing C-component K, and map
through the literal K/O₂(K) model. The smaller component's core quotient
survives this two-group kernel. Properness survives because equality of the
two-core images forces equality of the original local components.

The proved parabolic-placement theorems identify the smaller image with a
root residual in PSL₃, Sp₄, G₂, or Ree. Its rank-one quotient determines the
field: the two-adic valuation of |PSL₂(2ⁿ)| is n. In SL₃ the central projection
has a two-group restricted kernel because the smaller core quotient is
centerless. In Ree the Suzuki residual is excluded by divisibility by three,
leaving exactly the coefficient field of degree 2m+1.

The applications retain both flag normalizers and arbitrary nontrivial
U ≤ V₁ with the original N_T(U) Sylow hypothesis. These prove the split
nonbinary and Ree branches, not an exhaustive carrier catalogue. The
Refinement.SplitOrRee consumer uses them without an embedding-list premise.
The preceding flag quotient and pointwise-action premises belong to
qt-d-1222-natural-flag-cartan; their final discharge remains with
qt-d-1222-natural-local-geometry. The relative-components owner retains
triality, the remaining carrier branches, and full 11.1.1--11.1.3 assembly.

Source: Aschbacher--Smith A.3.12(2) and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004. The imported root-model calculations
retain their source attribution and literal field conventions.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Restrict to the containing component and transport the smaller local
component through its literal two-core quotient. Properness and the original
rank-one quotient survive; the top C-component condition is inherited. -/
theorem model_local_image
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n : ℕ} (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    {A : Type*} [Group A] [Finite A] (e : (K ⧸ pCore 2 K) ≃* A) :
    ∃ (S : Sylow 2 A) (C : Subgroup A), C ∈ localCComponents S ∧ C ≠ ⊤ ∧
      ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2 ^ n) ∧ (⊤ : Subgroup A).IsCComponent := by
  obtain ⟨R,_,hR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK.le hK.subnormal
  let D := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 K := by
    ext x
    change e (q x) = 1 ↔ x ∈ pCore 2 K
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let := pCore_isNilpotent (p := 2) (G := K)
  let : Group.IsSolvable f.ker := hk ▸ (inferInstance : Group.IsSolvable (pCore 2 K))
  let S := R.mapSurjective hf
  let C := D.map f
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.subgroupOf le_rfl
  have hproper : C ≠ ⊤ := by
    intro he
    have heq : D.map q = (⊤ : Subgroup K).map q := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [map_map, map_map, map_top_of_surjective f hf]
      exact he
    have heD := MovedMaximality.eq_of_twoCore_images_eq R hR ht le_top heq
    exact hBK.ne (le_antisymm hBK.le (subgroupOf_eq_top.mp heD))
  have hker : IsPGroup 2 (f.subgroupMap D).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let d := subgroupOfEquivOfLe hBK.le
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let a := (f.subgroupMap D).quotientPCoreEquivOfSurjective (f.subgroupMap_surjective D) hker
  refine ⟨S,C,localCComponents_map_of_solvable_ker hR f,hproper,
    hsmall.of_mulEquiv (a.symm.trans dq),?_⟩
  have hh := (ht.map_quotient (pCore 2 K)).map_equiv e
  simpa only [map_top_of_surjective (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _),
    map_top_of_surjective e.toMonoidHom e.surjective] using hh

private theorem binary_parameter_eq {A : Type*} [Group A]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : ClassicalGroup.IsPSL A 2 (2 ^ n))
    (h' : ClassicalGroup.IsPSL A 2 (2 ^ m)) : n = m :=
  (binary_two_valuation hn h).symm.trans (binary_two_valuation hm h')

private theorem binary_parameter_of_sl2 {A : Type*} {F : Type} [Group A] [Field F] [Finite F]
    [CharP F 2] {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : ClassicalGroup.IsPSL A 2 (2 ^ n)) (hF : Nat.card F = 2 ^ m)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F) : n = m :=
  binary_parameter_eq hn hm h
    ⟨F,inferInstance,inferInstance,hF,⟨e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F)⟩⟩

private theorem linear_parameter {F : Type} [Field F] [Finite F] [CharP F 2]
    {n m : ℕ} (hn : 0 < n) (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n)) : n = m := by
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.linear_three_local_placement hF hm S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp
  · apply binary_parameter_of_sl2 hn (by omega) hsmall hF
    apply aq.trans
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F
  · apply binary_parameter_of_sl2 hn (by omega) hsmall hF
    apply aq.trans
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F

private theorem symplectic_parameter {F : Type} [Field F] [Finite F] [CharP F 2]
    {n m : ℕ} (hn : 0 < n) (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n)) : n = m := by
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.symplectic_local_placement hF hm S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp
  · apply binary_parameter_of_sl2 hn (by omega) hsmall hF
    apply aq.trans
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hm
  · apply binary_parameter_of_sl2 hn (by omega) hsmall hF
    apply aq.trans
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hm

private theorem g2_parameter {F : Type} [Field F] [Finite F] [CharP F 2]
    {n m : ℕ} (hn : 0 < n) (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n)) : n = m := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hm
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.G2.local_placement hq S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp
  · apply binary_parameter_of_sl2 hn (by omega) hsmall hF
    apply aq.trans
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
      Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL
  · apply binary_parameter_of_sl2 hn (by omega) hsmall hF
    apply aq.trans
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
      Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL

private theorem ree_parameter {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (S : Sylow 2 (ReeF4.Model m)) (B : Subgroup (ReeF4.Model m))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (htop : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent) : n = 2 * m + 1 := by
  obtain ⟨g,s,he⟩ := SourceEmbeddings.ReeLocal.local_placement hm htop S B hB hproper
  let a := ((MulAut.conj g).subgroupMap B).trans (MulEquiv.subgroupCongr he)
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  cases s with
  | linear =>
    exact binary_parameter_eq hn (by omega) hsmall
      ⟨ReeF4.CoefficientField m,inferInstance,inferInstance,ReeF4.field_card m,
        ⟨aq.trans (ReeF4.Parabolics.linearLocalQuotientEquiv m)⟩⟩
  | suzuki =>
    exact (binary_not_suzuki hsmall m (by omega)
      ⟨aq.trans (ReeF4.Parabolics.suzukiLocalQuotientEquiv m)⟩).elim

private theorem special_linear_parameter {F : Type} [Field F] [Finite F] [CharP F 2]
    {n m : ℕ} (hn : 0 < n) (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n)) : n = m := by
  let f := Matrix.PSL3.projection F
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect B := by
    let := hB.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup SL(3,F)) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hker : f.ker ≤ center SL(3,F) := (Matrix.PSL3.projection_ker F).le
  have hp : B.map f ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    apply le_of_map_le_of_perfect f hker ⊤ B
    rw [ht]
    exact le_top
  have hk : IsPGroup 2 (f.subgroupMap B).ker := by
    apply pCore_isPGroup.to_le
    intro b hb
    have hc : (b : SL(3,F)) ∈ center SL(3,F) := hker (congrArg Subtype.val hb)
    have hbc : b ∈ center B := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (mem_center_iff.mp hc a)
    let q := QuotientGroup.mk' (pCore 2 B)
    have hz : q b ∈ center (B ⧸ pCore 2 B) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) a
      rw [← map_mul,← map_mul,mem_center_iff.mp hbc a]
    rw [binary_center_eq_bot hsmall,mem_bot] at hz
    exact (QuotientGroup.eq_one_iff b).mp hz
  let a := (f.subgroupMap B).quotientPCoreEquivOfSurjective (f.subgroupMap_surjective B) hk
  exact linear_parameter hn hm hF
    (S.mapSurjective (Matrix.PSL3.projection_surjective F)) (B.map f)
    (localCComponents_map_of_solvable_ker hB f) hp (hsmall.of_mulEquiv a.symm)

/-- A proper linear, symplectic or G₂ containing component has the same binary field. -/
theorem proper_untwisted_parameters
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n m : ℕ} (hn : 0 < n) (hm : 1 < m)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ m) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ m) ∨
      Source.IsSp (K ⧸ pCore 2 K) 2 (2 ^ m) ∨
      ClassificationModels.IsG2At (K ⧸ pCore 2 K) (2 ^ m)) : n = m := by
  rcases hmodel with h | h | h | h
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨R,C,hl,hp,hs,_⟩ := model_local_image P hB hK hBK hsmall e
    exact special_linear_parameter hn hm hF R C hl hp hs
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨R,C,hl,hp,hs,_⟩ := model_local_image P hB hK hBK hsmall e
    exact linear_parameter hn hm hF R C hl hp hs
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨R,C,hl,hp,hs,_⟩ := model_local_image P hB hK hBK hsmall e
    exact symplectic_parameter hn hm hF R C hl hp hs
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨R,C,hl,hp,hs,_⟩ := model_local_image P hB hK hBK hsmall e
    exact g2_parameter hn hm hF R C hl hp hs

/-- In a Ree containing component, the PSL₂ section uses the linear parabolic
and its exact coefficient-field degree. The Suzuki parabolic is impossible. -/
theorem proper_ree_parameters
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : LocalModels.IsReeF4At (K ⧸ pCore 2 K) m) : n = 2 * m + 1 := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  obtain ⟨R,C,hl,hp,hs,htop⟩ := model_local_image P hB hK hBK hsmall (e.trans d.modelEquiv)
  exact ree_parameter hn hm R C hl hp hs htop
/-- Actual carrier models for the split rank-two and Ree branches, before
matching their independent field parameter with the original flag. -/
@[expose] def SplitOrReeCarrier (A : Type*) [Group A] : Prop :=
  (∃ m, 1 < m ∧ (Source.IsSL A 3 (2 ^ m) ∨ ClassicalGroup.IsPSL A 3 (2 ^ m) ∨
    Source.IsSp A 2 (2 ^ m) ∨ ClassificationModels.IsG2At A (2 ^ m))) ∨
    ∃ m, 1 ≤ m ∧ LocalModels.IsReeF4At A m

/-- The split and Ree branches of 11.1.1: the original smaller quotient
forces the field relation, without assuming an embedding alternative. -/
theorem component_alternative_of_split_or_ree
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) : ComponentAlternative B K n := by
  by_cases he : B = K
  · exact .equal he
  have hlt := lt_of_le_of_ne hBK he
  rcases hmodel with ⟨m,hm,hmodel⟩ | ⟨m,hm,hmodel⟩
  · have he := proper_untwisted_parameters P hB hK hlt (by omega) hm hsmall hmodel
    subst m
    rcases hmodel with h | h | h | h
    · exact .lie (.sl3 h)
    · exact .lie (.psl3 h)
    · exact .lie (.sp4 h)
    · exact .lie (.g2 h)
  · exact .lie (.ree m hm (proper_ree_parameters P hB hK hlt (by omega) hm hsmall hmodel) hmodel)

/-- Apply the parameter comparison in the literal relative group H, retaining
its full Sylow and the actual two-core quotients. -/
theorem relative_equal_or_lie_of_split_or_ree
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) : B = K ∨ LieOvergroup (K ⧸ pCore 2 K) n := by
  by_cases he : B = K
  · exact .inl he
  obtain ⟨P₀,hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH,hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  have hlt : B.subgroupOf H < K.subgroupOf H := by
    refine lt_of_le_of_ne (comap_mono hBK) ?_
    intro hh
    apply he
    simpa only [map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hK.1] using
      congrArg (map H.subtype) hh
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  rcases hmodel with ⟨m,hm,hmodel⟩ | ⟨m,hm,hmodel⟩
  · have ht : Source.IsSL (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) 3 (2 ^ m) ∨
        ClassicalGroup.IsPSL (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) 3 (2 ^ m) ∨
        Source.IsSp (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) 2 (2 ^ m) ∨
        ClassificationModels.IsG2At (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) (2 ^ m) := by
      rcases hmodel with h | h | h | h
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
        exact .inl ⟨F,inferInstance,inferInstance,hF,⟨kq.trans a⟩⟩
      · exact .inr (.inl (h.of_mulEquiv kq))
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
        exact .inr (.inr (.inl ⟨F,inferInstance,inferInstance,hF,⟨kq.trans a⟩⟩))
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
        exact .inr (.inr (.inr ⟨F,inferInstance,inferInstance,hF,⟨kq.trans a⟩⟩))
    have hnm := proper_untwisted_parameters P₀ hlocal hK.2 hlt (by omega) hm
      (hsmall.of_mulEquiv bq) ht
    subst m
    rcases hmodel with h | h | h | h
    · exact .inr (.sl3 h)
    · exact .inr (.psl3 h)
    · exact .inr (.sp4 h)
    · exact .inr (.g2 h)
  · have ht : LocalModels.IsReeF4At (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) m := by
      obtain ⟨d,⟨a⟩⟩ := hmodel
      exact ⟨d,⟨kq.trans a⟩⟩
    exact .inr (.ree m hm (proper_ree_parameters P₀ hlocal hK.2 hlt (by omega) hm
      (hsmall.of_mulEquiv bq) ht) hmodel)

/-- The source alternative with the same original relative subgroups. -/
theorem relative_component_alternative_of_split_or_ree
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) : ComponentAlternative B K n := by
  exact (relative_equal_or_lie_of_split_or_ree hP hB hK hBK hn hsmall hmodel).elim
    ComponentAlternative.equal ComponentAlternative.lie

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual source application to both original flag normalizers. -/
theorem flag_component_alternative_of_split_or_ree (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩
  exact relative_component_alternative_of_split_or_ree hs (flag_mem_local_of_model D S f i hm)
    hK hLK S.nonbinary hm hmodel

/-- The same source branch for arbitrary nontrivial U ≤ V₁ and its literal
normalizer, retaining the N_T(U) Sylow condition and the full point preimage. -/
theorem subspace_component_alternative_of_split_or_ree
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_component_alternative_of_split_or_ree hSyl hlocalP hK hLK
    S.nonbinary hm hmodel

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
