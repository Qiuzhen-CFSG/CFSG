module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.JankoMathieu
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.SelfCentralizingCoreCenter
public import Theory.GroupTheory.Commutator.SmallNormalizedImage
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# Remaining local exclusions for the ordinary field-four J4 configuration

The full SL3(4) quotient has three-part 27, excluding the symmetric-linear
local by its actual quotient order. It also excludes every local with an
actual binary L5 quotient, whose three-part is only nine. A nontrivial perfect
normal subgroup of the first involution centralizer has order divisible by eleven, by its
literal M22 quotient and solvable lower series. The second involution
centralizer is contained in the already excluded Mathieu local.

For placement of the radical normalizer in the first centralizer, radicality
forces the extraspecial local two-core into the radical. Its self-centralizing
core then bounds the radical center by two. This contradicts a nonzero central
module equal to its commutator with the residual. Applying these results to
the literal central quotient of C.2.8 preserves the entire original W.

The binary L5 branch uses a literal quotient equivalence and does not
construct or classify its embedding in J4. These are exclusions of specified
placements. Exhaustive placement of the actual radical normalizer, and the
degree-two centralizer and 11.1.5 assembly,
remain with qt-d-1222-natural-point-fixed-summand. The Source extension applies
the shared covering statements at B=L; the odd-normalizer owner can use the
same statements without assuming shortness or W=V. Earlier-source discharge
remains with qt-d-1222-natural-normalizer-source.

Source: Aschbacher--Smith, C.3.5 and the local inspections on printed
pp.611--612 and622; GLS3 Table5.3i. The imported native model modules retain
their ATLAS word attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem full_linear_three_card (F : BinaryField) (hF : F.degree = 2)
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* SL(3,F.Carrier)) :
    ∃ k : ℕ, Nat.card A = 2 ^ k * 60480 := by
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  refine ⟨k,?_⟩
  rw [← (pCore 2 A).card_mul_index,hk,index_eq_card,Nat.card_congr e.toEquiv,
    OddNormalizer.linear_three_order]
  norm_num [F.card_eq,hF]

theorem janko_symmetric_linear_not_twentySeven :
    ¬ 27 ∣ Nat.card Janko4.LocalStructure.SymmetricLinear.max4Subgroup := by
  obtain ⟨k,hk⟩ := Janko4.LocalStructure.SymmetricLinear.max4_card_dvd_twoPower_mul
  intro hd
  have ht := hd.trans hk
  have he := ((by decide : Nat.Coprime 27 2).pow_right k).dvd_of_dvd_mul_left ht
  norm_num at he

theorem janko_cover_not_le_symmetric_linear_conjugate
    (F : BinaryField) (hF : F.degree = 2) (X : Subgroup Janko4.Model)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier)) (g : Janko4.Model) :
    ¬ X ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
      (MulAut.conj g).toMonoidHom := by
  intro hX
  have hd : 27 ∣ Nat.card X := by
    obtain ⟨k,hk⟩ := full_linear_three_card F hF e
    rw [hk]
    exact dvd_mul_of_dvd_right (by decide : 27 ∣ 60480) _
  have ht := hd.trans (card_dvd_of_le hX)
  rw [card_map_of_injective (MulAut.conj g).injective] at ht
  exact janko_symmetric_linear_not_twentySeven ht

private theorem binary_linear_five_card {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Nat.card PSL(5,F) = 9999360 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hF,Fin.prod_univ_succ] at hc
  exact hc

/-- An actual local quotient L5(2) has three-part at most nine, regardless
of the size or splitting of its two-core. -/
theorem binary_linear_five_local_not_twentySeven
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* PSL(5,ZMod 2)) : ¬ 27 ∣ Nat.card A := by
  have hcN : Nat.card PSL(5,ZMod 2) = 9999360 :=
    binary_linear_five_card (by simp)
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  intro hd
  rw [← (pCore 2 A).card_mul_index,hk,index_eq_card,Nat.card_congr e.toEquiv,hcN] at hd
  have ht := ((by decide : Nat.Coprime 27 2).pow_right k).dvd_of_dvd_mul_left hd
  norm_num at ht

/-- The full field-four residual cannot lie in a local with the actual
binary L5 quotient. This uses a quotient equivalence, not a family label. -/
theorem janko_cover_not_le_linear_five_local_conjugate
    (F : BinaryField) (hF : F.degree = 2) (X C : Subgroup Janko4.Model)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2)) (g : Janko4.Model) :
    ¬ X ≤ C.map (MulAut.conj g).toMonoidHom := by
  intro hX
  have hd : 27 ∣ Nat.card X := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    rw [← (pCore 2 X).card_mul_index,hk,index_eq_card,Nat.card_congr e.toEquiv,
      OddNormalizer.linear_three_order]
    norm_num [F.card_eq,hF]
    exact dvd_mul_of_dvd_right (by decide : 27 ∣ 60480) _
  have ht := hd.trans (card_dvd_of_le hX)
  rw [card_map_of_injective (MulAut.conj g).injective] at ht
  exact binary_linear_five_local_not_twentySeven eC ht

private theorem perfect_le_kernel_of_commutative
    {A Q : Type*} [Group A] [Group Q] [IsMulCommutative Q]
    (X : Subgroup A) [Group.IsPerfect X] (f : A →* Q) : X ≤ f.ker := by
  let g := f.comp X.subtype
  let := Group.IsPerfect.range g
  have hs : Subsingleton g.range := inferInstance
  intro x hx
  have he : g.rangeRestrict ⟨x,hx⟩ = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val he

theorem janko_first_centralizer_normal_perfect_eleven
    (X : Subgroup Janko4.InvolutionCentralizers.First.centralizer)
    [X.Normal] [Group.IsPerfect X] (hne : X ≠ ⊥) : 11 ∣ Nat.card X := by
  open Janko4.InvolutionCentralizers.First.QuotientExtension in
  have hXH : X ≤ H := by
    rw [← centralizerOuterCharacter_ker]
    exact perfect_le_kernel_of_commutative X centralizerOuterCharacter
  let H := Janko4.InvolutionCentralizers.First.QuotientExtension.H
  let R := Janko4.InvolutionCentralizers.First.QuotientExtension.R
  let Q := Janko4.InvolutionCentralizers.First.QuotientExtension.Q
  let f := Janko4.InvolutionCentralizers.First.QuotientExtension.mathieuProjection
  let Y := X.subgroupOf H
  let a : Y ≃* X := subgroupOfEquivOfLe hXH
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : (Y.map f).Normal := (inferInstance : Y.Normal).map f
    Janko4.InvolutionCentralizers.First.QuotientExtension.mathieuProjection_surjective
  let := Sporadic.Mathieu.m22_isSimpleGroup
  rcases (inferInstance : (Y.map f).Normal).eq_bot_or_eq_top with hz | ht
  · have hXR : X ≤ R := by
      have hk := (map_eq_bot_iff Y).mp hz
      rw [Janko4.InvolutionCentralizers.First.QuotientExtension.mathieuProjection_ker] at hk
      intro x hx
      exact hk (show (⟨x,hXH hx⟩ : H) ∈ Y from hx)
    let Z := X.subgroupOf R
    let b : Z ≃* X := subgroupOfEquivOfLe hXR
    let : Group.IsPerfect Z := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
    have hZQ := perfect_le_kernel_of_commutative Z
      ((Janko4.InvolutionCentralizers.First.QuotientExtension.RQuotientEquivC3).toMonoidHom.comp
        (QuotientGroup.mk' (Q.subgroupOf R)))
    have hXQ : X ≤ Q := by
      rw [MonoidHom.ker_comp_of_injective _ _
        Janko4.InvolutionCentralizers.First.QuotientExtension.RQuotientEquivC3.injective,
        QuotientGroup.ker_mk'] at hZQ
      intro x hx
      exact hZQ (show (⟨x,hXR hx⟩ : R) ∈ Z from hx)
    let : Nontrivial X := (nontrivial_iff_ne_bot X).mpr hne
    exact (Group.IsPerfect.not_isNilpotent X (pCore_isPGroup.to_le hXQ).isNilpotent).elim
  · have hd : 11 ∣ Nat.card (Y.map f) := by
      rw [ht,card_top,Sporadic.Mathieu.m22_order]
      decide
    have hb := hd.trans (card_dvd_of_surjective _ (f.subgroupMap_surjective Y))
    rwa [Nat.card_congr a.toEquiv] at hb

theorem janko_first_centralizer_no_normal_full_linear_three
    (F : BinaryField) (hF : F.degree = 2)
    (X : Subgroup Janko4.InvolutionCentralizers.First.centralizer)
    [X.Normal] [Group.IsPerfect X]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier)) : False := by
  obtain ⟨k,hk⟩ := full_linear_three_card F hF e
  have hne : X ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hk
    have hp : 0 < 2 ^ k := pow_pos (by decide) _
    omega
  have hd := janko_first_centralizer_normal_perfect_eleven X hne
  rw [hk] at hd
  have ht := ((by decide : Nat.Coprime 11 2).pow_right k).dvd_of_dvd_mul_left hd
  norm_num at ht

private theorem subgroup_le_inverse_conjugate {G : Type*} [Group G]
    (X C : Subgroup G) (g : G) (h : X ≤ C.map (MulAut.conj g).toMonoidHom) :
    X.map (MulAut.conj g⁻¹).toMonoidHom ≤ C := by
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
  have ht : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext z
    change g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z
    group
  rwa [map_map,ht,map_id] at hh

theorem janko_cover_not_normal_in_first_centralizer_conjugate
    (F : BinaryField) (hF : F.degree = 2) (X : Subgroup Janko4.Model)
    [Group.IsPerfect X] (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (g : Janko4.Model)
    (hX : X ≤ Janko4.InvolutionCentralizers.First.centralizer.map
      (MulAut.conj g).toMonoidHom) :
    ¬ Janko4.InvolutionCentralizers.First.centralizer.map
        (MulAut.conj g).toMonoidHom ≤ normalizer (X : Set Janko4.Model) := by
  intro hn
  let C := Janko4.InvolutionCentralizers.First.centralizer
  let t := MulAut.conj g⁻¹
  let Y := X.map t.toMonoidHom
  have hY : Y ≤ C := subgroup_le_inverse_conjugate X C g hX
  have hnY : C ≤ normalizer (Y : Set Janko4.Model) := by
    have ht : (normalizer (X : Set Janko4.Model)).map t.toMonoidHom =
        normalizer (Y : Set Janko4.Model) := map_equiv_normalizer_eq X t
    have hh := (map_mono (f := t.toMonoidHom) hn).trans_eq ht
    have he : (C.map (MulAut.conj g).toMonoidHom).map t.toMonoidHom = C := by
      rw [map_map]
      have hi : t.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
        ext z
        change g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z
        group
      rw [hi,map_id]
    rwa [he] at hh
  let A := Y.subgroupOf C
  let a : A ≃* X := (subgroupOfEquivOfLe hY).trans (t.subgroupMap X).symm
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnY
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  let q := a.toMonoidHom.quotientPCoreEquivOfSurjective a.surjective
    (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_subsingleton 2 _)
  exact janko_first_centralizer_no_normal_full_linear_three F hF A (q.trans e)

theorem janko_cover_not_le_second_centralizer_conjugate
    (F : BinaryField) (hF : F.degree = 2) (X : Subgroup Janko4.Model)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier)) (g : Janko4.Model) :
    ¬ X ≤ Janko4.InvolutionCentralizers.Second.ambientCentralizer.map
      (MulAut.conj g).toMonoidHom := by
  intro hX
  exact janko_cover_not_le_mathieu_conjugate F hF X e g
    (hX.trans (map_mono Janko4.InvolutionCentralizers.Second.ambient_le_max1))

private theorem radical_moved_module_not_le_small_core_center
    {A : Type*} [Group A] [Finite A] (P X U C : Subgroup A)
    (hP : IsPRadical 2 P) (hne : U ≠ ⊥)
    (hUP : U ≤ P ⊓ centralizer (P : Set A)) (hmove : U = ⁅U,X⁆)
    (hC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C)
    (hcard : Nat.card (center (pCore 2 C)) ≤ 2) :
    ¬ normalizer (P : Set A) ≤ C := by
  intro hn
  have hPC : P ≤ C := P.le_normalizer.trans hn
  have hQP : C.pCoreIn 2 ≤ P :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le P (C.pCoreIn 2)
      hP.isPGroup (isPGroup_pCoreIn 2 C) hP.2.le
      (hn.trans (C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))
  have hQ : pCore 2 C ≤ P.subgroupOf C := by
    intro q hq
    exact hQP (mem_map_of_mem C.subtype hq)
  have hsize : Nat.card (center P) ≤ 2 := by
    have hh := center_card_le_of_centralizer_le (pCore 2 C) (P.subgroupOf C) hQ hC
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hPC)).toEquiv] at hh
    exact hh.trans hcard
  have hUcenter : U ≤ (center P).map P.subtype := by
    intro u hu
    refine ⟨⟨u,(hUP hu).1⟩,?_,rfl⟩
    exact mem_center_iff.mpr (fun p => Subtype.ext ((hUP hu).2 p p.property))
  have hUcard : Nat.card U ≤ 2 := by
    have hh := card_le_of_le hUcenter
    rw [card_map_of_injective P.subtype_injective] at hh
    exact hh.trans hsize
  have hXU : X ≤ normalizer (U : Set A) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm,←hmove]
  have hb := commutator_le_ker_of_normalized_image_card_le_two
    (MonoidHom.id A) X U hXU (by simpa using hUcard)
  rw [MonoidHom.ker_id,commutator_comm,←hmove] at hb
  exact hne (bot_unique hb)

/-- A radical with a nonzero fully moved central module cannot have its
full normalizer inside a conjugate of the first involution centralizer.
The extraspecial core is forced into the radical by normalizer saturation. -/
theorem janko_radical_normalizer_not_le_first_conjugate
    (P X U : Subgroup Janko4.Model) (hP : IsPRadical 2 P) (hne : U ≠ ⊥)
    (hUP : U ≤ P ⊓ centralizer (P : Set Janko4.Model)) (hmove : U = ⁅U,X⁆)
    (g : Janko4.Model) :
    ¬ normalizer (P : Set Janko4.Model) ≤
      Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom := by
  let C := Janko4.InvolutionCentralizers.First.centralizer
  let Cg := C.map (MulAut.conj g).toMonoidHom
  let e : Cg ≃* C := ((MulAut.conj g).subgroupMap C).symm
  have hC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    (@Theory.Quasithin.centralizer_pCore_le_iff C
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.involutionCentralizer
      inferInstance inferInstance 2 Janko4.InvolutionCentralizers.First.centralizerEquiv).mpr
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.localTwoCoreCentralizerControl.1
  have hCg : centralizer (pCore 2 Cg : Set Cg) ≤ pCore 2 Cg :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hC
  have hcard : Nat.card (center (pCore 2 Cg)) ≤ 2 := by
    let ep : pCore 2 Cg ≃* pCore 2 C :=
      (e.subgroupMap (pCore 2 Cg)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
    rw [Nat.card_congr (centerCongr ep).toEquiv]
    let := Janko4.InvolutionCentralizers.First.centralizer_twoCore_extraspecial
    exact (IsExtraspecial.center_order_p 2 (pCore 2 C)).le
  exact radical_moved_module_not_le_small_core_center P X U Cg hP hne hUP hmove hCg hcard

open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The covering residual avoids the binary L5 local row under its literal
quotient identification. Full W and the original inclusion are unchanged. -/
theorem c28_covering_jankoFour_avoids_linear_five
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model)
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (g : Janko4.Model) :
    ¬ (ordinaryCoverProjection h K hK).range.map ek.toMonoidHom ≤
      C.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_,hf,⟨a⟩,_⟩ := c28_covering_ordinary_jankoFour D S h hBL hc hVB e K hK
  let t := ek.subgroupMap (ordinaryCoverProjection h K hK).range
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  exact janko_cover_not_le_linear_five_local_conjugate S.field hf _ C
    (q.symm.trans ((ordinaryCoverQuotient h K hK).symm.trans (e.trans a))) eC g

/-- The full ordinary C.2.8 module excludes first-centralizer placement of
the actual projected radical normalizer, without any seed identification. -/
theorem ordinary_jankoFour_radical_normalizer_avoids_first
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) (g : Janko4.Model) :
    ¬ normalizer (((ordinaryComponentSubgroup R K).map
        (QuotientGroup.mk' (center K))).map ek.toMonoidHom : Set Janko4.Model) ≤
      Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom := by
  let q := QuotientGroup.mk' (center K)
  let P := (ordinaryComponentSubgroup R K).map q
  let X := (ordinaryCoverProjection h K hK).range
  let U := (ordinaryComponentSubgroup W K).map q
  obtain ⟨_,hne,_,hUP,hm⟩ := ordinary_projected_module h hn K hK
  have hP : IsPRadical 2 P := ordinary_projected_radical h K hK
  have hUc : U.map ek.toMonoidHom ≤ centralizer (P.map ek.toMonoidHom : Set Janko4.Model) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
      (hUP.trans inf_le_right),Subgroup.map_bot]
  have hm' : U.map ek.toMonoidHom = ⁅U.map ek.toMonoidHom,X.map ek.toMonoidHom⁆ := by
    rw [←map_commutator,←hm]
  exact janko_radical_normalizer_not_le_first_conjugate
    (P.map ek.toMonoidHom) (X.map ek.toMonoidHom) (U.map ek.toMonoidHom)
    (hP.map_equiv ek)
    (fun hz => hne ((map_eq_bot_iff_of_injective U ek.injective).mp hz))
    (le_inf (map_mono (hUP.trans inf_le_left)) hUc) hm' g

/-- The ordinary covering residual avoids the symmetric-linear and second
involution-centralizer placements. If it lies in a first centralizer, the
literal image of M cannot contain that entire centralizer. -/
theorem c28_covering_jankoFour_local_restrictions
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) :
    let X := (ordinaryCoverProjection h K hK).range.map ek.toMonoidHom
    let N := ((ordinaryComponentSubgroup M K).map
      (QuotientGroup.mk' (center K))).map ek.toMonoidHom
    ∀ g : Janko4.Model,
      (¬ X ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
        (MulAut.conj g).toMonoidHom) ∧
      (¬ X ≤ Janko4.InvolutionCentralizers.Second.ambientCentralizer.map
        (MulAut.conj g).toMonoidHom) ∧
      (X ≤ Janko4.InvolutionCentralizers.First.centralizer.map
        (MulAut.conj g).toMonoidHom →
        ¬ Janko4.InvolutionCentralizers.First.centralizer.map
          (MulAut.conj g).toMonoidHom ≤ N) := by
  dsimp only
  obtain ⟨_,hf,_,hN,a,_,_⟩ := c28_covering_jankoFour_local D S h hstrict hn
    hBL hc hVB e he K hK
  let X₀ := (ordinaryCoverProjection h K hK).range
  let X := X₀.map ek.toMonoidHom
  let t := ek.subgroupMap X₀
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  let aX : (X ⧸ pCore 2 X) ≃* SL(3,S.field.Carrier) := q.symm.trans a
  let : Group.IsPerfect X₀ := (ordinary_projected_geometry h hn K hK).1
  let : Group.IsPerfect X := Group.IsPerfect.map ek.toMonoidHom
  intro g
  refine ⟨janko_cover_not_le_symmetric_linear_conjugate S.field hf X aX g,
    janko_cover_not_le_second_centralizer_conjugate S.field hf X aX g,?_⟩
  intro hX
  have heN : normalizer (X : Set Janko4.Model) =
      ((ordinaryComponentSubgroup M K).map
        (QuotientGroup.mk' (center K))).map ek.toMonoidHom := by
    rw [← map_equiv_normalizer_eq X₀ ek,hN]
  rw [←heN]
  exact janko_cover_not_normal_in_first_centralizer_conjugate S.field hf X aX g hX

/-- The three displayed native J4 locals are impossible placements of the full
normalizer of the literal projected radical. Exhaustive placement of that
normalizer is the remaining source obligation, not a premise discharged here. -/
theorem c28_covering_jankoFour_radical_normalizer_avoids_locals
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) :
    let P := ((ordinaryComponentSubgroup R K).map
      (QuotientGroup.mk' (center K))).map ek.toMonoidHom
    ∀ g : Janko4.Model,
      (¬ normalizer (P : Set Janko4.Model) ≤
        (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
          Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom) ∧
      (¬ normalizer (P : Set Janko4.Model) ≤
        Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∧
      (¬ normalizer (P : Set Janko4.Model) ≤
        Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom) := by
  dsimp only
  let P₀ := (ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))
  have hXN := (map_mono (f := ek.toMonoidHom)
    (ordinary_projected_cover_normalizes_radical h hn K hK)).trans
      (P₀.le_normalizer_map ek.toMonoidHom)
  intro g
  refine ⟨?_,ordinary_jankoFour_radical_normalizer_avoids_first h hn K hK ek g,?_⟩
  · intro hp
    exact c28_covering_jankoFour_avoids_mathieu D S h hBL hc hVB e K hK ek g
      (hXN.trans hp)
  · intro hp
    exact (c28_covering_jankoFour_local_restrictions D S h hstrict hn hBL hc hVB
      e he K hK ek g).1 (hXN.trans hp)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
