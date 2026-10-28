module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoFourPlacement
public import Theory.GroupTheory.FixedElementaryTransport

/-!
# Recognizing the J₄ proper pair in the genuine triple M₂₂ cover

The first involution-centralizer quotient is used through its actual
central projection. A full-Sylow-normalized local image descends to the
native triple M₂₂ cover, where the complete original point catalogue and
properness force the image to be the whole cover. The intrinsic two-core
quotient is transported back to the original point component, yielding the
literal `mathieuCoverJanko` proper pair.

This is the remaining-cover step of A.3.12 and 11.4.2, Aschbacher–Smith,
printed pp. 776–777. The later inner-radical, omega-center and Hall/Cartan
endgame remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem first_point_cover_image
    (P : Sylow 2 Janko4.InvolutionCentralizers.First.centralizer)
    (B : Subgroup Janko4.InvolutionCentralizers.First.centralizer)
    (hB : B ∈ localCComponents P)
    (hn : (P : Subgroup Janko4.InvolutionCentralizers.First.centralizer) ≤ normalizer (B : Set Janko4.InvolutionCentralizers.First.centralizer)) :
    ∃ (S : Sylow 2 Sporadic.Mathieu.M22TripleCover)
      (C : Subgroup Sporadic.Mathieu.M22TripleCover),
      C ∈ localCComponents S ∧ (S : Subgroup Sporadic.Mathieu.M22TripleCover) ≤ normalizer (C : Set Sporadic.Mathieu.M22TripleCover) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (C ⧸ pCore 2 C)) := by
  open Janko4.InvolutionCentralizers.First in
  open QuotientExtension in
  have ht : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf_of_le le_rfl le_sup_left
  let : Group.IsPerfect (⊤ : Subgroup B) := ht.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := B)).toMonoidHom) (topEquiv (G := B)).surjective
  have hBH : B ≤ H := by
    intro x hx
    rw [←centralizerOuterCharacter_ker]
    let g := centralizerOuterCharacter.comp B.subtype
    let : Group.IsPerfect g.range := Group.IsPerfect.range g
    have he : g.rangeRestrict ⟨x,hx⟩ = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val he
  obtain ⟨R,hR,hrlocal⟩ := exists_local_sylow_restriction P hB hBH
    (inferInstance : H.Normal).isSubnormal
  have hn' : (R : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    intro s hs
    have hsp : (s : centralizer) ∈ (P : Subgroup centralizer) := by
      change s ∈ (P : Subgroup centralizer).subgroupOf H
      rwa [←hR]
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hsp) (x : centralizer)
  let g := coverProjection
  have hp : IsPGroup 2 g.ker := by
    rw [coverProjection_ker]
    exact (pCore_isPGroup (p := 2) (G := centralizer)).comap_subtype
  let : Group.IsSolvable g.ker := by
    let := hp.isNilpotent
    infer_instance
  have hk : IsPGroup 2 (g.subgroupMap (B.subgroupOf H)).ker := by
    rw [ker_subgroupMap]
    exact hp.comap_subtype
  let d := subgroupOfEquivOfLe hBH
  let a := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
    ((g.subgroupMap (B.subgroupOf H)).pCoreQuotientEquiv (g.subgroupMap_surjective _) hk)
  exact ⟨R.mapSurjective coverProjection_surjective,(B.subgroupOf H).map g,
    localCComponents_map_of_solvable_ker hrlocal g,
    (map_mono hn').trans ((B.subgroupOf H).le_normalizer_map g),⟨a⟩⟩

private theorem cover_core_eq_bot : pCore 2 Sporadic.Mathieu.M22TripleCover = ⊥ := by
  have hd := card_dvd_of_le (IsQuasisimple.pCore_le_center 2 (G := Sporadic.Mathieu.M22TripleCover))
  rw [Sporadic.Mathieu.M22TripleCover.center_card] at hd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Sporadic.Mathieu.M22TripleCover)).exists_card_eq
  have hcop : Nat.Coprime 2 (Nat.card (pCore 2 Sporadic.Mathieu.M22TripleCover)) :=
    (by decide : Nat.Coprime 2 3).of_dvd_right hd
  rw [hn] at hcop
  have he : n = 0 := by
    by_contra h
    have hd2 : 2 ∣ 2^n := dvd_pow_self 2 h
    exact (by decide : ¬Nat.Coprime 2 2) (hcop.of_dvd_right hd2)
  exact card_eq_one.mp (by simpa [he] using hn)

private theorem jankoFour_first_cover_image
    (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents P)
    (hn : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (t : Janko4.Model)
    (hpair : B ⊔ (P : Subgroup Janko4.Model) ≤ centralizer ({t} : Set Janko4.Model))
    (d : centralizer ({t} : Set Janko4.Model) ≃* Janko4.InvolutionCentralizers.First.centralizer) :
    ∃ (Q : Sylow 2 Sporadic.Mathieu.M22TripleCover)
      (C : Subgroup Sporadic.Mathieu.M22TripleCover),
      C ∈ localCComponents Q ∧
      (Q : Subgroup Sporadic.Mathieu.M22TripleCover) ≤ normalizer (C : Set Sporadic.Mathieu.M22TripleCover) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (C ⧸ pCore 2 C)) := by
  let Z := centralizer ({t} : Set Janko4.Model)
  have hBZ : B ≤ Z := le_sup_left.trans hpair
  have hPZ : (P : Subgroup Janko4.Model) ≤ Z := le_sup_right.trans hpair
  let B' := (B.subgroupOf Z).map d.toMonoidHom
  let P' := (P.subtype hPZ).mapSurjective (f := d.toMonoidHom) d.surjective
  let : Group.IsSolvable d.toMonoidHom.ker := by
    rw [d.toMonoidHom.ker_eq_bot d.injective]; infer_instance
  have hB' : B' ∈ localCComponents P' :=
    localCComponents_map_of_solvable_ker (local_restrict hB hBZ) d.toMonoidHom
  have hnZ : (P.subtype hPZ : Subgroup Z) ≤ normalizer (B.subgroupOf Z : Set Z) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : Janko4.Model)
  have hn' : (P' : Subgroup Janko4.InvolutionCentralizers.First.centralizer) ≤
      normalizer (B' : Set Janko4.InvolutionCentralizers.First.centralizer) :=
    (map_mono hnZ).trans ((B.subgroupOf Z).le_normalizer_map d.toMonoidHom)
  let u : B ≃* B' := (subgroupOfEquivOfLe hBZ).symm.trans (d.subgroupMap (B.subgroupOf Z))
  let a' := QuotientGroup.congr _ _ u (pCore_map_iso 2 u)
  obtain ⟨Q,C,hC,hQC,⟨v⟩⟩ := first_point_cover_image P' B' hB' hn'
  exact ⟨Q,C,hC,hQC,⟨a'.trans v⟩⟩

private def core_quotient_equiv_of_top {A : Type*} [Group A]
    (hc : pCore 2 A = ⊥) (C : Subgroup A) (hfull : C = ⊤) :
    (C ⧸ pCore 2 C) ≃* A := by
  let w : C ≃* A := (MulEquiv.subgroupCongr hfull).trans topEquiv
  exact (QuotientGroup.congr _ _ w (pCore_map_iso 2 w)).trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The original point image in the first J₄ involution centralizer has the
literal genuine triple M₂₂ cover as its intrinsic two-core quotient. -/
theorem ofFlag_jankoFour_point_equiv_mathieuCover
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hp : JankoFourPointPlacement (ofFlag S f X z H) J) :
    Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      Sporadic.Mathieu.M22TripleCover) := by
  obtain ⟨⟨b⟩,P,B,hB,_,hn,⟨a⟩,_,_,t,ht,hpair,⟨d⟩⟩ := hp
  let := point_quasisimple_in_jankoFour h hJ hlt b
  have hdegree := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne
    hlinear h1132 e hJ hlt).1
  obtain ⟨Q,C,hC,hQC,⟨v⟩⟩ := jankoFour_first_cover_image P B hB hn t hpair d
  have hfull := ofFlag_mathieuCover_point_eq_top S f X z H h hne hlinear h1132 e
    hdegree Q C hC hQC (a.trans v)
  exact ⟨a.trans (v.trans (core_quotient_equiv_of_top cover_core_eq_bot C hfull))⟩

private theorem three_cover_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hm : IsM22Cover B) : IsM22Cover A := by
  let := hm.1
  refine ⟨IsQuasisimple.of_mulEquiv e.symm,
    ⟨(centerCongr e).trans hm.2.1.some⟩,?_⟩
  exact ⟨(QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
    hm.2.2.some⟩

private theorem triple_cover_model : IsM22Cover Sporadic.Mathieu.M22TripleCover := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact ⟨inferInstance,
    ⟨mulEquivOfPrimeCardEq Sporadic.Mathieu.M22TripleCover.center_card
      (show Nat.card (Multiplicative (ZMod 3)) = 3 from Nat.card_zmod 3)⟩,
    ⟨Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv⟩⟩

/-- The complete original point and containing catalogues yield the source
proper embedding, including the genuine triple-M₂₂-in-J₄ pair. -/
theorem ofFlag_proper_embedding
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧ ProperEmbedding (ofFlag S f X z H).Kz J := by
  obtain ⟨hd,hpair | hp⟩ := ofFlag_proper_embedding_or_jankoFour_placement
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  · exact ⟨hd,hpair⟩
  · obtain ⟨a⟩ := ofFlag_jankoFour_point_equiv_mathieuCover
      S f X z H h hne hlinear h1132 e hJ.1 hlt hp
    exact ⟨hd,.quasisimple (.mathieuCoverJanko (three_cover_transport a triple_cover_model) hp.1)
      (ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
