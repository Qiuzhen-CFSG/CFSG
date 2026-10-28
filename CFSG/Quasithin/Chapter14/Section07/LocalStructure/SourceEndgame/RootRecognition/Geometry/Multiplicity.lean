module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# One natural summand and the centralizer kernel in 14.7.73

Write P = O₂(K), E = S ∩ Sᵏ and C = C_H(U), retaining the original right
conjugate and the original qK marking. Commutator generation puts P inside
Q_K = [O₂(H),K]C. The dual coordinates on Q_K/C kill E, since [E,K] ≤ U
and the natural dual has no fixed vectors. Conversely, the exact 14.7.71
bound [K,C] ≤ U kills C_P(U) in the natural sum P/E supplied by G.1.3.
Thus E = C_P(U).

The restricted dual image of P is nonzero: otherwise P ≤ C, whence P ≤ U,
and |K| ≤ 60·32 < |S| = 2048, contrary to the original Steinberg section.
Transitivity on nonzero natural vectors makes this image the full dual.
Natural self-duality preserves qK and gives the actual natural P/E section;
comparison of orders proves that the G.1.3 multiplicity is exactly one.
The final theorem applies the existing source quotient consumer.

The genuine 71 dual coordinates and centralizer bound, the 72 Steinberg,
core, Frattini and U₀ = V₁ facts, the earlier T-normalization, the independently
constructed marked images, and universal G.1.3 are explicit source premises.
The marked images retain the original k chosen outside M₁. Their construction
and the universal recognition theorem remain with the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.71–73, printed pp.1075–1077 (PDF pp.1092–1094), especially the
application of 14.7.71(1) immediately after G.1.3 on printed p.1076.
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Multiplicity
open Chapter12.Section08 CriticalFusion.Source
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (k : K F)
  (hS : S L F = L.pCoreIn 2)
  (hPhi : (frattini (S L F)).map (S L F).subtype = V)
  (hTL : (T : Subgroup G) ≤ normalizer L)
  (m : MarkedImages d k)

include hS hPhi hTL m in
/-- Commutator generation places the original two-core inside the literal Q_K.
Only the central summand U uses the containment U ≤ C_H(U). -/
theorem core_le_QK : (K F).pCoreIn 2 ≤ ChiefFactors.QK F := by
  rw [← core_commutator_generation d k hS hPhi hTL m]
  exact sup_le ((commutator_mono (K_core_eq_intersection.le.trans inf_le_right)
    le_rfl).trans le_sup_left) ((ChiefFactors.U_le_C d).trans le_sup_right)

private theorem naturalAction_restrict (a : K F) (v : SL2FourNatural.V) :
    ChiefFactors.naturalAction d ⟨a, K_le_H F a.property⟩ v =
      SL2FourNatural.action (qK d a) v := by
  change d.naturalQuotient.action (d.qH ⟨a, K_le_H F a.property⟩) v = _
  rw [qK_marking]
  exact d.naturalQuotient.restriction _ _

private theorem dual_marking (a : K F) (v : SL2FourNatural.V) :
    (ChiefFactors.naturalAction d).dual ⟨a, K_le_H F a.property⟩
      (SL2FourNatural.selfDual v) =
        SL2FourNatural.selfDual (SL2FourNatural.action (qK d a) v) := by
  rw [SL2FourNatural.selfDual_equivariant]
  change (SL2FourNatural.selfDual v).comp
    (ChiefFactors.naturalAction d (⟨a, K_le_H F a.property⟩ : F.H)⁻¹) = _
  apply congrArg (LinearMap.comp (SL2FourNatural.selfDual v))
  apply LinearMap.ext
  intro x
  have h := naturalAction_restrict d a⁻¹ x
  rw [map_inv (qK d)] at h
  exact h

private theorem dual_fixed_eq_zero (v : Module.Dual (ZMod 2) SL2FourNatural.V)
    (hv : ∀ a : K F,
      (ChiefFactors.naturalAction d).dual ⟨a, K_le_H F a.property⟩ v = v) : v = 0 := by
  obtain ⟨w, rfl⟩ := SL2FourNatural.selfDual.surjective v
  have hw : w = 0 := SL2FourNatural.natural_fixed_eq_zero w (by
    intro a
    obtain ⟨b, rfl⟩ := qK_surjective d a
    apply SL2FourNatural.selfDual.injective
    exact (dual_marking d b w).symm.trans (hv b))
  rw [hw, map_zero]

include hS hPhi hTL m in
/-- Centrality of E/U kills E in the genuine dual section Q_K/C_H(U). -/
theorem intersection_le_C (q : ChiefFactors.QKDualCoordinates d) :
    E L F k ≤ ChiefFactors.C F := by
  intro e he
  let eQ : ChiefFactors.QK F := ⟨e,
    core_le_QK d k hS hPhi hTL m (intersection_le_core d k hS hPhi hTL m he)⟩
  apply (q.qSection.coordinates_eq_one_iff eQ).mp
  apply Multiplicative.toAdd.injective
  apply dual_fixed_eq_zero d
  intro a
  have hbound : ⁅K F, E L F k⁆ ≤ ChiefFactors.C F := by
    rw [commutator_comm]
    exact (E_commutator_le_U d k (generation d k hS hTL m)
      (derived_le_U hS hPhi)).trans (ChiefFactors.U_le_C d)
  exact q.qSection.fixed_on_imageSpace_of_commutator_le (K F) (E L F k) hbound
    ⟨a, K_le_H F a.property⟩ a.property _
    ((q.qSection.mem_imageSpace_iff _ _).mpr ⟨eQ, he, rfl⟩)

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

private theorem copies_fixed_eq_zero (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    {s : ℕ} (hs : NaturalCopies σ s) (v : M) (hv : ∀ a, σ a v = v) : v = 0 := by
  obtain ⟨e, he⟩ := hs
  apply e.injective
  rw [map_zero]
  funext i
  exact SL2FourNatural.natural_fixed_eq_zero (e v i) (fun a => by
    change Matrix.mulVec a.val (e v i) = e v i
    rw [← he, hv])

include hS hPhi hTL m in
/-- The exact 71 centralizer bound kills the image of C_P(U) in the natural
sum P/E. Together with the dual calculation this identifies the actual kernel. -/
theorem intersection_eq_centralizer (q : ChiefFactors.QKDualCoordinates d)
    (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U)
    (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (σ.comp (qK d))) {s : ℕ} (hs : NaturalCopies σ s) :
    E L F k = (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
  apply le_antisymm
  · exact le_inf (intersection_le_core d k hS hPhi hTL m)
      ((intersection_le_C d k hS hPhi hTL m q).trans inf_le_right)
  · intro p hp
    let pP : (K F).pCoreIn 2 := ⟨p, hp.1⟩
    apply (c.coordinates_eq_one_iff pP).mp
    apply Multiplicative.toAdd.injective
    apply copies_fixed_eq_zero σ hs
    intro a
    obtain ⟨b, rfl⟩ := qK_surjective d a
    apply c.fixed_on_imageSpace_of_commutator_le (K F) (ChiefFactors.C F)
      (h71.trans (U_le_E d k)) b b.property
    exact (c.mem_imageSpace_iff _ _).mpr
      ⟨pP, ⟨K_le_H F (pCoreIn_le 2 _ hp.1), hp.2⟩, rfl⟩

private theorem source_card_S
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)) :
    Nat.card (S L F) = 2048 := by
  have hv : Nat.card V = 2 ^ 3 := by simpa only [F.last] using F.card 3 (by decide)
  have hs : Nat.card BinaryLinearThree.Steinberg = 2 ^ 8 := by
    classical
    let : Finite BinaryLinearThree.Steinberg :=
      Finite.of_surjective (fun s => (st.coordinates s).toAdd)
        (fun w => st.onto (Multiplicative.ofAdd w))
    let := Fintype.ofFinite BinaryLinearThree.Steinberg
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
      BinaryLinearThree.finrank_steinberg, ZMod.card]
  rw [st.card_section, hs, hv]
  norm_num

include hS hPhi hTL m in
/-- The original Steinberg section excludes the zero dual image of P.
Indeed P ≤ C_H(U) would imply P ≤ U and then |S| ≤ |K| ≤ 60·32 < 2048. -/
theorem core_not_le_C (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U)
    (hpoint : d.U₀ = F.Vi 1)
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)) :
    ¬ (K F).pCoreIn 2 ≤ ChiefFactors.C F := by
  intro hp
  have hPU : (K F).pCoreIn 2 ≤ F.U := by
    rw [← core_commutator_generation d k hS hPhi hTL m]
    exact sup_le ((commutator_comm _ _).le.trans
      ((commutator_mono le_rfl hp).trans h71)) le_rfl
  have hcP : Nat.card ((K F).pCoreIn 2) ≤ 32 :=
    (card_le_of_le hPU).trans_eq (U_card d hpoint)
  have hcSL : Nat.card SL2FourNatural.SL = 60 := by
    rw [Nat.card_congr d.naturalQuotient.marking.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcK : Nat.card (K F) = 60 * Nat.card ((K F).pCoreIn 2) := by
    rw [card_eq_card_quotient_mul_card_subgroup (qK d).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (qK d) (qK_surjective d)).toEquiv, qK_ker,
      Nat.card_congr (subgroupOfEquivOfLe (pCoreIn_le 2 (K F))).toEquiv, hcSL]
  have hSK := card_le_of_le m.le_residual
  rw [source_card_S d st, hcK] at hSK
  omega

private noncomputable def coreCoordinates (q : ChiefFactors.QKDualCoordinates d) :
    (K F).pCoreIn 2 →* Multiplicative SL2FourNatural.V :=
  (AddMonoidHom.toMultiplicative SL2FourNatural.selfDual.symm.toAddEquiv.toAddMonoidHom).comp
    (q.qSection.coordinates.comp (inclusion (core_le_QK d k hS hPhi hTL m)))

private theorem coreCoordinates_eq_one_iff (q : ChiefFactors.QKDualCoordinates d)
    (p : (K F).pCoreIn 2) :
    coreCoordinates d k hS hPhi hTL m q p = 1 ↔ (p : G) ∈ ChiefFactors.C F := by
  change SL2FourNatural.selfDual.symm (q.qSection.coordinates _).toAdd = 0 ↔ _
  rw [← SL2FourNatural.selfDual.symm.map_zero,
    SL2FourNatural.selfDual.symm.injective.eq_iff]
  exact q.qSection.coordinates_eq_one_iff _

omit [Finite G] in
private theorem core_normalized : K F ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
  (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)

private theorem coreCoordinates_equivariant (q : ChiefFactors.QKDualCoordinates d)
    (a : K F) (p : (K F).pCoreIn 2) :
    (coreCoordinates d k hS hPhi hTL m q
      ⟨(a : G) * p * (a : G)⁻¹,
        (mem_normalizer_iff.mp (core_normalized a.property) p).mp p.property⟩).toAdd =
      SL2FourNatural.action (qK d a)
        (coreCoordinates d k hS hPhi hTL m q p).toAdd := by
  change SL2FourNatural.selfDual.symm (q.qSection.coordinates _).toAdd =
    SL2FourNatural.action (qK d a)
      (SL2FourNatural.selfDual.symm (q.qSection.coordinates _).toAdd)
  apply SL2FourNatural.selfDual.injective
  rw [SL2FourNatural.selfDual.apply_symm_apply, ← dual_marking,
    SL2FourNatural.selfDual.apply_symm_apply]
  exact q.qSection.equivariant ⟨a, K_le_H F a.property⟩
    ⟨p, core_le_QK d k hS hPhi hTL m p.property⟩

private theorem coreCoordinates_surjective (q : ChiefFactors.QKDualCoordinates d)
    (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U) (hpoint : d.U₀ = F.Vi 1)
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)) :
    Function.Surjective (coreCoordinates d k hS hPhi hTL m q) := by
  obtain ⟨p, hp, hpC⟩ := SetLike.not_le_iff_exists.mp
    (core_not_le_C d k hS hPhi hTL m h71 hpoint st)
  let pP : (K F).pCoreIn 2 := ⟨p, hp⟩
  have hp0 : (coreCoordinates d k hS hPhi hTL m q pP).toAdd ≠ 0 := by
    intro he
    exact hpC ((coreCoordinates_eq_one_iff d k hS hPhi hTL m q pP).mp he)
  intro v
  by_cases hv : v = 1
  · exact ⟨1, by rw [map_one, hv]⟩
  obtain ⟨a, ha⟩ := SL2FourNatural.transitive_nonzero
    (coreCoordinates d k hS hPhi hTL m q pP).toAdd v.toAdd hp0 hv
  obtain ⟨b, rfl⟩ := qK_surjective d a
  refine ⟨⟨(b : G) * pP * (b : G)⁻¹,
    (mem_normalizer_iff.mp (core_normalized b.property) pP).mp hp⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  exact (coreCoordinates_equivariant d k hS hPhi hTL m q b pP).trans ha

/-- Restrict the genuine dual coordinates to P and use natural self-duality.
Transitivity makes the nonzero image surjective, with the original E kernel
and the original qK; no new quotient marking is selected. -/
noncomputable def naturalSection (q : ChiefFactors.QKDualCoordinates d)
    (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U) (hpoint : d.U₀ = F.Vi 1)
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (σ.comp (qK d))) {s : ℕ} (hs : NaturalCopies σ s) :
    BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)) where
  section_le := pCoreIn_le 2 _
  kernel_le := intersection_le_core d k hS hPhi hTL m
  normalized := core_normalized
  coordinates := coreCoordinates d k hS hPhi hTL m q
  onto := coreCoordinates_surjective d k hS hPhi hTL m q h71 hpoint st
  kernel_eq := by
    ext p
    rw [MonoidHom.mem_ker, coreCoordinates_eq_one_iff,
      mem_subgroupOf, intersection_eq_centralizer d k hS hPhi hTL m q h71 σ c hs]
    exact ⟨fun h => ⟨p.property, h.2⟩,
      fun h => ⟨K_le_H F (pCoreIn_le 2 _ p.property), h.2⟩⟩
  equivariant := coreCoordinates_equivariant d k hS hPhi hTL m q

include hS hPhi hTL m in
/-- Any natural decomposition of the constructed P/E has exactly one summand. -/
theorem multiplicity_eq_one (q : ChiefFactors.QKDualCoordinates d)
    (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U) (hpoint : d.U₀ = F.Vi 1)
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (σ.comp (qK d))) {s : ℕ} (hs : NaturalCopies σ s) : s = 1 := by
  let n := naturalSection d k hS hPhi hTL m q h71 hpoint st σ c hs
  have hc : Nat.card M = 16 := by
    have hn : Nat.card SL2FourNatural.V = 16 := by
      rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]
    have hmul := c.card_section.symm.trans n.card_section
    rw [hn] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  obtain ⟨e, _⟩ := hs
  have he : Nat.card M = 16 ^ s := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin,
      show Nat.card (Fin 2 → SL2FourNatural.F) = 16 from
        (Nat.card_eq_fintype_card.trans SL2FourNatural.card_vector)]
  apply Nat.pow_right_injective (by decide : 2 ≤ 16)
  simpa only [pow_one] using he.symm.trans hc

/-- Apply universal G.1.3 to the constructed action, then discharge both the
multiplicity and centralizer conclusions from the genuine 71/72 inputs. -/
theorem exists_one_copy (q : ChiefFactors.QKDualCoordinates d)
    (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U) (hpoint : d.U₀ = F.Vi 1)
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (recognition : NaturalRecognition.{u}) :
    let := intersection_normal d k hS hPhi hTL m
    let := quotient_elementary d k hS hPhi hTL m
    ∃ (σ : Representation (ZMod 2) SL2FourNatural.SL
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2))))
      (_c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
        (σ.comp (qK d))),
      NaturalCopies σ 1 ∧
      E L F k = (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
  let := intersection_normal d k hS hPhi hTL m
  let := quotient_elementary d k hS hPhi hTL m
  obtain ⟨σ, c, s, hs⟩ := exists_natural_copies d k hS hPhi hTL m recognition
  have hs1 := multiplicity_eq_one d k hS hPhi hTL m q h71 hpoint st σ c hs
  subst s
  exact ⟨σ, c, hs, intersection_eq_centralizer d k hS hPhi hTL m q h71 σ c hs⟩

include hS hPhi hTL m in
/-- Actual application to `RootRecognition.source_quotient_outputs`, after
constructing its natural section. Only the expressly earlier source inputs,
the independent marked images, and universal G.1.3 remain as premises. -/
theorem source_outputs (q : ChiefFactors.QKDualCoordinates d)
    (h71 : ⁅K F, ChiefFactors.C F⁆ ≤ F.U) (hpoint : d.U₀ = F.Vi 1)
    (st : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (recognition : NaturalRecognition.{u}) :
    Nonempty (BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d))) ∧
    E L F k = (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) ∧
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2)) ∧
      ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 ∧
      (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
        ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      ∃ R' : Sylow 2 (K F),
        (R' : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2 := by
  let := intersection_normal d k hS hPhi hTL m
  let := quotient_elementary d k hS hPhi hTL m
  obtain ⟨σ, c, hs, hcentral⟩ :=
    exists_one_copy d k hS hPhi hTL m q h71 hpoint st recognition
  obtain ⟨hn, hout⟩ := source_outputs_of_one_copy d k hS hPhi hTL m σ c hs
  exact ⟨hn, hcentral, hout⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Multiplicity
