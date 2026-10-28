module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Applications
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.FixedSections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.ModelCounts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.CubicCentralizer
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Fixed orders and the original kernel in 14.7.73

The actual Sylow three-subgroup of L₁ injects through the two-kernels of
both original markings. The qL parabolic image of order twelve therefore
gives cubic images in both models. Coprime lifting of the original natural
and Steinberg coordinate maps gives fixed orders two and eight. The cubic
centralizer in SL₂(4) has odd order, placing C_S(B) in P, and the original
natural P/E coordinates place it in E. Lifting across E/U then proves its
order four. The original |U|=32 finally gives |P|=2¹¹.

The same natural section supplies P=[P,L₁](S∩P). The final consumer combines
these results with Applications.source_quotient_outputs, including its
actual Sylow witness. The parabolic two-core and index identifications
remain with the owning assembly and need the separate S=[S,L₁] lift.

Source: Aschbacher–Smith 14.7.73, printed pp.1076–1077,
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting

private theorem prime_three_coprime_two {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 2 A) : Nat.Coprime 3 (Nat.card A) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

private theorem sylow_three_card_of_range {A D : Type*} [Group A] [Finite A] [Group D]
    (q : A →* D) (hq : IsPGroup 2 q.ker) (hcard : Nat.card q.range = 12)
    (B : Sylow 3 A) : Nat.card B = 3 := by
  let : Finite q.range := Finite.of_surjective q.rangeRestrict q.rangeRestrict_surjective
  let r := q.rangeRestrict
  let C := B.mapSurjective q.rangeRestrict_surjective
  have hC : Nat.card C = 3 := by
    rw [C.card_eq_multiplicity, hcard]
    decide +kernel
  have hr : Nat.Coprime 3 (Nat.card r.ker) := by
    change Nat.Coprime 3 (Nat.card q.rangeRestrict.ker)
    rw [MonoidHom.ker_rangeRestrict]
    exact prime_three_coprime_two hq
  exact (Nat.card_congr (B.equivOfSurjectiveCoprime r q.rangeRestrict_surjective hr C).toEquiv).trans hC

private theorem image_three_card {A D : Type*} [Group A] [Finite A] [Group D]
    (q : A →* D) (hq : IsPGroup 2 q.ker) (B : Subgroup A) (hB : Nat.card B = 3) :
    Nat.card (B.map q) = 3 := by
  have hinj := injective_comp_subtype_of_coprime_ker q (prime_three_coprime_two hq) B
    (IsPGroup.of_card (n := 1) (by simpa using hB))
  let e : B ≃* B.map q := MulEquiv.ofBijective (q.subgroupMap B)
    ⟨fun x y h => hinj (congrArg Subtype.val h), q.subgroupMap_surjective B⟩
  exact (Nat.card_congr e.toEquiv).symm.trans hB

open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

set_option backward.isDefEq.respectTransparency false in
omit [Finite G] in
theorem parabolic_le_K : F.Li L 1 ≤ K F := by
  simpa only [InvariantFlag.Li, InvariantFlag.H, K,
    show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, if_false] using
    (embedded_pResidual_mono 2 (inf_le_right : L ⊓ F.H ≤ F.H))

/-- The original Sylow three-subgroup, embedded in G. -/
def cubic (B : Sylow 3 (F.Li L 1)) : Subgroup G :=
  (B : Subgroup (F.Li L 1)).map (F.Li L 1).subtype

omit [Finite G] in
theorem cubic_le (B : Sylow 3 (F.Li L 1)) : cubic B ≤ F.Li L 1 := map_subtype_le _

/-- The marked parabolic has order twelve modulo S. Its actual Sylow
three-subgroups inject through both original two-kernels. -/
theorem cubic_image_cards
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12)
    (B : Sylow 3 (F.Li L 1)) :
    Nat.card (cubic B) = 3 ∧
      Nat.card (((cubic B).subgroupOf L).map d.qL) = 3 ∧
      Nat.card (((cubic B).subgroupOf (K F)).map (qK d)) = 3 := by
  have hJL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  let f := d.qL.comp (inclusion hJL)
  have hfker : IsPGroup 2 f.ker := by
    change IsPGroup 2 (d.qL.ker.comap (inclusion hJL))
    rw [d.qL_ker]
    exact ((isPGroup_pCoreIn 2 L).comap_subtype).comap_of_injective _ (inclusion_injective hJL)
  have hfrange : f.range = ((F.Li L 1).subgroupOf L).map d.qL := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨inclusion hJL j, j.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  have hBc := sylow_three_card_of_range f hfker (hfrange ▸ hpar) B
  have hB : Nat.card (cubic B) = 3 :=
    (Nat.card_congr ((B : Subgroup (F.Li L 1)).equivMapOfInjective
      (F.Li L 1).subtype (F.Li L 1).subtype_injective).toEquiv).symm.trans hBc
  refine ⟨hB, image_three_card d.qL ?_ _ ?_, image_three_card (qK d) (qK_ker_isPGroup d) _ ?_⟩
  · rw [d.qL_ker]
    exact (isPGroup_pCoreIn 2 L).comap_subtype
  · exact (Nat.card_congr (subgroupOfEquivOfLe ((cubic_le B).trans hJL)).toEquiv).trans hB
  · exact (Nat.card_congr (subgroupOfEquivOfLe ((cubic_le B).trans parabolic_le_K)).toEquiv).trans hB

/-- Transport the genuine Steinberg and natural cubic fixed counts on the
same original B. The only model-size input is the marked parabolic image. -/
theorem source_fixed_counts
    (hS : S L F = L.pCoreIn 2) (hUK : F.U ≤ K F)
    (hpoint : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12)
    (B : Sylow 3 (F.Li L 1)) :
    Nat.card (S L F ⊓ centralizer (cubic B : Set G) : Subgroup G) = 8 ∧
      Nat.card (F.U ⊓ centralizer (cubic B : Set G) : Subgroup G) = 2 := by
  have hBL : cubic B ≤ L := (cubic_le B).trans ((F.Li_le L 1).trans inf_le_left)
  have hBK : cubic B ≤ K F := (cubic_le B).trans parabolic_le_K
  obtain ⟨hB, hBLcard, hBKcard⟩ := cubic_image_cards d hpar B
  have hBp : IsPGroup 3 (cubic B) := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hSp : IsPGroup 2 (S L F) := hS.symm ▸ isPGroup_pCoreIn 2 L
  have hVp : IsPGroup 2 V := hSp.of_injective (inclusion s.kernel_le) (inclusion_injective _)
  let := hVp.isNilpotent
  let := hSp.isNilpotent
  let := d.U_elementary
  have hUp : IsPGroup 2 F.U := IsElementaryAbelian.isPGroup 2 _
  let := hUp.isNilpotent
  have hCV := fixed_coordinates_card (d.natural_section (s.kernel_le.trans s.section_le))
    hBL inferInstance (IsPGroup.coprime_card_of_ne 3 2 (by decide) _ _ hBp hVp)
  rw [natural_three_cubic_fixed_card _ hBLcard, bot_inf_eq, card_bot, mul_one] at hCV
  have hCS := fixed_coordinates_card s hBL inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) _ _ hBp hSp)
  rw [steinberg_cubic_fixed_card _ hBLcard, hCV] at hCS
  have hCU := fixed_coordinates_card (natural_U_section d hpoint hUK) hBK inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) _ _ hBp hUp)
  have hpointfix : F.Vi 1 ≤ centralizer (cubic B : Set G) :=
    le_centralizer_iff.mp (hBK.trans ((K_le_H F).trans d.H_centralizes_point))
  have hzero : Nat.card (⊥ : Submodule (ZMod 2) SL2FourNatural.V) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [natural_four_cubic_fixed _ hBKcard, hzero,
    one_mul, inf_eq_left.mpr hpointfix] at hCU
  exact ⟨hCS, hCU.trans (by simpa using F.card 1 (by decide))⟩

/-- Fixed points on the original P/E natural section lie in its literal kernel. -/
theorem source_core_fixed_le_E (k : K F)
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12)
    (B : Sylow 3 (F.Li L 1)) :
    (K F).pCoreIn 2 ⊓ centralizer (cubic B : Set G) ≤ E L F k := by
  have hX := (cubic_image_cards d hpar B).2.2
  intro x hx
  have hfix : (n.coordinates ⟨x, hx.1⟩).toAdd ∈ fixedSpace SL2FourNatural.naturalRepresentation
      (((cubic B).subgroupOf (K F)).map (qK d)) := by
    rintro ⟨_, b, hb, rfl⟩
    have he := n.equivariant b ⟨x, hx.1⟩
    have hc : (b : G) * x * (b : G)⁻¹ = x :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx.2 b hb)
    have heq : (⟨(b : G) * x * (b : G)⁻¹,
        (mem_normalizer_iff.mp (n.normalized b.property) x).mp hx.1⟩ : (K F).pCoreIn 2) = ⟨x, hx.1⟩ := Subtype.ext hc
    rw [heq] at he
    exact he.symm
  rw [natural_four_cubic_fixed _ hX] at hfix
  exact (n.coordinates_eq_one_iff _).mp (Multiplicative.toAdd.injective hfix)

/-- A cubic centralizer in S first enters the original two-kernel, then E. -/
theorem source_cubic_centralizer_le_E (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12)
    (B : Sylow 3 (F.Li L 1)) :
    S L F ⊓ centralizer (cubic B : Set G) ≤ E L F k := by
  have hX := (cubic_image_cards d hpar B).2.2
  let X := ((cubic B).subgroupOf (K F)).map (qK d)
  have hSK : S L F ≤ K F := le_sup_left.trans hgen.ge
  have hSp : IsPGroup 2 (S L F) := hS.symm ▸ isPGroup_pCoreIn 2 L
  have hIm : IsPGroup 2 (((S L F).subgroupOf (K F)).map (qK d)) := hSp.comap_subtype.map _
  have hC : IsPGroup 3 (centralizer (X : Set SL2FourNatural.SL)) := by
    intro x
    exact ⟨1, Subtype.ext (cubic_centralizer_cube X hX x x.property)⟩
  have hdis := hIm.disjoint_of_coprime hC (by decide)
  intro x hx
  let xK : K F := ⟨x, hSK hx.1⟩
  have hxC : qK d xK ∈ centralizer (X : Set SL2FourNatural.SL) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    apply congrArg (qK d)
    exact Subtype.ext (mem_centralizer_iff.mp hx.2 b hb)
  have hz : qK d xK = 1 := Subgroup.disjoint_def.mp hdis
    (mem_map_of_mem (qK d) hx.1) hxC
  have hP : x ∈ (K F).pCoreIn 2 := by
    have hh : xK ∈ (qK d).ker := hz
    rw [qK_ker] at hh
    exact hh
  exact source_core_fixed_le_E d k n hpar B ⟨hP, hx.2⟩

/-- The original natural P/E action generates P modulo S ∩ P under L₁.
This is the commutator-generation step needed to place P in the parabolic. -/
theorem source_core_parabolic_generation (k : K F)
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12) :
    (K F).pCoreIn 2 = ⁅(K F).pCoreIn 2, F.Li L 1⁆ ⊔
      (S L F ⊓ (K F).pCoreIn 2) := by
  let B : Sylow 3 (F.Li L 1) := Classical.choice inferInstance
  have hp := isPGroup_pCoreIn 2 (K F)
  let := hp.isNilpotent
  have hBp : IsPGroup 3 (cubic B) := B.isPGroup'.map _
  have hn : F.Li L 1 ≤ normalizer ((K F).pCoreIn 2) :=
    parabolic_le_K.trans ((K F).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))
  have hC := source_core_fixed_le_E d k n hpar B
  have hdecomp := eq_commutator_sup_centralizer_of_solvable_coprime ((K F).pCoreIn 2)
    (cubic B) ((cubic_le B).trans hn) inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) _ _ hBp hp)
  apply le_antisymm
  · exact hdecomp.le.trans (sup_le_sup (commutator_mono le_rfl (cubic_le B))
      (hC.trans (le_inf inf_le_left n.kernel_le)))
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp hn) inf_le_right

/-- The actual coprime quotient lifting proves the fixed-kernel count and
then the core order; centralizer placement and both fixed counts are proved above. -/
theorem source_fixed_kernel_count (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (hpoint : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12)
    (B : Sylow 3 (F.Li L 1)) :
    F.U.relIndex (E L F k) = 4 ∧ Nat.card ((K F).pCoreIn 2) = 2 ^ 11 := by
  have hplace := source_cubic_centralizer_le_E d k hS hgen n hpar B
  have hUE : F.U ≤ E L F k := U_le_E d k
  have hEK : E L F k ≤ K F := n.kernel_le.trans (pCoreIn_le 2 _)
  have hBK : cubic B ≤ K F := (cubic_le B).trans parabolic_le_K
  have hSp : IsPGroup 2 (S L F) := hS.symm ▸ isPGroup_pCoreIn 2 L
  have hEp : IsPGroup 2 (E L F k) :=
    hSp.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let := hEp.isNilpotent
  have hBp : IsPGroup 3 (cubic B) := B.isPGroup'.map _
  have hd : ⁅S L F, S L F⁆ ≤ F.U :=
    derived_le_of_frattini_image_le hSp (hPhi.le.trans (Data.V_le_U F))
  have hBE : cubic B ≤ normalizer (E L F k) := hBK.trans (K_normalizes_E d k hgen hd)
  have hcomm : ⁅E L F k, cubic B⁆ ≤ F.U :=
    (commutator_mono le_rfl hBK).trans (E_commutator_le_U d k hgen hd)
  have hCE : E L F k ⊓ centralizer (cubic B : Set G) =
      S L F ⊓ centralizer (cubic B : Set G) :=
    le_antisymm (inf_le_inf inf_le_left le_rfl) (le_inf hplace inf_le_right)
  have hsplit : E L F k = F.U ⊔ (S L F ⊓ centralizer (cubic B : Set G)) := by
    have hc := eq_commutator_sup_centralizer_of_solvable_coprime (E L F k) (cubic B)
      hBE inferInstance (IsPGroup.coprime_card_of_ne 3 2 (by decide) _ _ hBp hEp)
    apply le_antisymm
    · rw [hc, hCE]
      exact sup_le_sup hcomm le_rfl
    · exact sup_le hUE hplace
  obtain ⟨hCS, hCU⟩ := source_fixed_counts d hS (hUE.trans hEK) hpoint s hpar B
  have hnorm : S L F ⊓ centralizer (cubic B : Set G) ≤ normalizer F.U :=
    hplace.trans (hEK.trans ((K_le_H F).trans d.conjugationSection.normalized))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.U
    (S L F ⊓ centralizer (cubic B : Set G)) hnorm
  rw [hCS, ← inf_assoc, inf_eq_left.mpr (hUE.trans inf_le_left), hCU, ← hsplit] at hprod
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) F.U (E L F k) bot_le hUE
  simp only [relIndex_bot_left] at hcard
  have hmul : Nat.card F.U * 8 = Nat.card F.U * (2 * F.U.relIndex (E L F k)) := by
    rw [← hcard] at hprod
    nlinarith [hprod]
  have hindex : F.U.relIndex (E L F k) = 4 := by
    have h := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F.U)) hmul
    omega
  exact ⟨hindex, core_card d k hpoint n hindex⟩

/-- The counted original quotient, together with the actual Sylow witness
and the elementary and commutator conclusions supplied by the root algebra. -/
theorem source_counted_quotients (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _))
    (hpoint : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hpar : Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12) :
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2)) ∧
      ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 ∧
      (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
        ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      (∃ R' : Sylow 2 (K F),
        (R' : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2) ∧
      F.U.relIndex (E L F k) = 4 ∧ Nat.card ((K F).pCoreIn 2) = 2 ^ 11 := by
  obtain ⟨he, hc, hp, hSyl⟩ := source_quotient_outputs d k hS hPhi hTL hgen R hR n
  obtain ⟨hEU, hcard⟩ := source_fixed_kernel_count d k hS hPhi hgen hpoint s n hpar
    (Classical.choice inferInstance)
  exact ⟨he, hc, hp, hSyl, hEU, hcard⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
