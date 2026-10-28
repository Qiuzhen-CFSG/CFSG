module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFiltration
public import Theory.Representation.BinaryConjugationSection.tensorChief
public import Theory.Representation.InvertedCubicTensor.naturalChief
public import Theory.GroupTheory.NoncentralChiefRefinement.fourGroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.Representation.Quotient
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients


/-!
# Chief-factor accounting for the literal opposite image

The G.2.3 series has one noncentral binary chief factor on its natural
four-plane, none on the middle quotient, and one per natural summand
on S/S₂. Refinement and equivariant Jordan–Hölder therefore give exactly
rank(A*)+1 factors, with A* defined using the original faithful projection.
The quotient I/S has order six and adds no noncentral binary factors.

For the original cubic C, the same count is its fixed-index length on S.
Thus a lower bound of three on an actual subgroup of S implies rank(A*)>1.
The original ambient lower bound and middle-layer fixedness remain to be
proved; this module does not assert the abelian-span conclusion.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645,
refs/quasithin.pdf. The Chapter 12 extension applies the rank calculation
to the original Cartan and the existing D.2.13 consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open NoncentralChiefRefinement InvertedCubicTensor
open scoped IsMulCommutative commutatorElement TensorProduct
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

private theorem plane_fixed_free (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    D.V ⊓ centralizer (D.L : Set G) = ⊥ := by
  have hn : D.L ≤ normalizer (D.V ⊓ centralizer (D.L : Set G) : Set G) :=
    (le_inf b.L_normalizes_V
      (D.L.le_normalizer.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  rcases b.irreducible _ inf_le_left hn with hz | heq
  · exact hz
  · have hLV : D.L ≤ centralizer (D.V : Set G) :=
      le_centralizer_iff.mp (heq.ge.trans inf_le_right)
    exact (hgN ((hLV.trans ((centralizer_le h.point_le).trans
      (Subgroup.centralizer_le_normalizer _))) hgL)).elim

/-- Every chief refinement of the actual two-core has one more noncentral
binary factor than the rank of the original opposite action image. -/
theorem binary_noncentral_chief_count
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (s : ChiefSeries (D.I g)) (hs0 : s.head = ⊥)
    (hs1 : s.last.val = (D.S g).subgroupOf (D.I g)) :
    s.noncentralTwoCount =
      rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h)) + 1 := by
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  let e := binarySourceCoreEquiv h b hUT g hgL hgN
  obtain ⟨hN,hA,σ,d,hS,hprod,hVE,hES,hVC,hVN,hEN,hEC,hEE,
    hcoord,hfinite,hcompl,⟨j,hj⟩,hcard,hmarks,hfix⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI e hnorm hindex
  let := hN
  let := hA
  let := hfinite
  let I := D.I g
  let Vn : NormalNode I := ⟨D.V.subgroupOf I,hVN⟩
  let En : NormalNode I := d.lowerChiefNode
  let Sn : NormalNode I := d.upperChiefNode
  have hVI : D.V ≤ I := hVE.trans (inf_le_left.trans le_sup_left)
  have hLI : D.L ≤ I := le_sup_left.trans hI.ge
  have hVcard : Nat.card Vn.val = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVI).toEquiv).trans b.card_V
  have hVz : Vn.val ⊓ center I = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hxL : (x : G) ∈ centralizer (D.L : Set G) := by
      intro l hl
      exact congrArg Subtype.val ((mem_center_iff.mp hx.2) ⟨l,hLI hl⟩)
    have hz : (x : G) = 1 := (plane_fixed_free h b g hgL hgN).le ⟨hx.1,hxL⟩
    exact Subtype.ext hz
  obtain ⟨sV,hV0,hV1,_,hcV⟩ := exists_four_chief_refinement Vn hVcard hVz
  have hVE' : Vn ≤ En := subgroupOf_mono I hVE
  have hcentral : IsCentral Vn En := by
    rw [isCentral_iff_commutator_le, Subgroup.commutator_le]
    intro a _ x hx
    rw [commutator_comm] at hEC
    exact hEC (commutator_mem_commutator a.property hx)
  obtain ⟨sE,hE0,hE1⟩ := exists_chiefSeries Vn En hVE'
  have hcE : sE.noncentralTwoCount = 0 :=
    sE.noncentralTwoCount_eq_zero_of_central (by rw [hE0,hE1]; exact hcentral)
  let p := D.binaryCoreProjection g e
  have hp : Function.Surjective p := by
    dsimp only [p]
    rw [D.binaryCoreProjection_eq]
    exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  let τ := (BinaryPermutation.coreRepresentation (Fin 3)).comp p
  let : Representation.IsIrreducible τ :=
    (irreducible_comp_surjective_iff p hp _).mpr natural_irreducible
  have hτ : ∃ a v, τ a v ≠ v := by
    obtain ⟨a,v,hv⟩ := natural_noncentral
    obtain ⟨x,rfl⟩ := hp a
    exact ⟨x,v,hv⟩
  have hj' : ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) I
      (multiplicitySpace σ)) τ) a z) = (σ.comp p) a (j z) := by
    intro a z
    exact hj (p a) z
  obtain ⟨sS,hS0,hS1,_,hcS⟩ := d.exists_tensor_chief_refinement τ j hj' hτ
  let sVE : ChiefSeries I := sV.smash sE (hV1.trans hE0.symm)
  let t : ChiefSeries I := sVE.smash sS (by simpa only [sVE,RelSeries.last_smash] using hE1.trans hS0.symm)
  have ht0 : t.head = ⊥ := by
    simpa only [t,sVE,RelSeries.head_smash] using hV0
  have ht1 : t.last = Sn := by
    simpa only [t,RelSeries.last_smash] using hS1
  have htc : t.noncentralTwoCount = Module.finrank (ZMod 2) (multiplicitySpace σ) + 1 := by
    dsimp only [t,sVE]
    rw [ChiefSeries.noncentralTwoCount_smash,ChiefSeries.noncentralTwoCount_smash,hcV,hcE,hcS]
    omega
  have hcount : s.noncentralTwoCount = Module.finrank (ZMod 2) (multiplicitySpace σ) + 1 := by
    rw [← htc]
    apply s.noncentralTwoCount_eq t (hs0.trans ht0.symm)
    exact (Subtype.ext hs1).trans ht1.symm
  let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
  obtain ⟨hel,hi⟩ := binary_opposite_image h b g hgL hgN
  let : IsElementaryAbelian 2 E := hel
  have hc : Nat.card E = 2 ^ rank E := by
    unfold rank
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [hm,Nat.log_pow (by decide : 1 < 2)]
  have hv := relIndex_mul_relIndex D.V (D.S₂ g) D.U hVE inf_le_left
  have hb := relIndex_mul_relIndex (⊥ : Subgroup G) D.V D.U bot_le
    (hVE.trans inf_le_left)
  rw [relIndex_bot_left,relIndex_bot_left,b.card_V] at hb
  rw [← hv,hi] at hb
  change Nat.card D.U = 2 ^ (Module.finrank (ZMod 2) (multiplicitySpace σ) + 3) *
    D.V.relIndex (D.S₂ g) at hcard
  rw [hc,hcard] at hb
  have heq : 2 ^ (rank E + 3) * D.V.relIndex (D.S₂ g) =
      2 ^ (Module.finrank (ZMod 2) (multiplicitySpace σ) + 3) * D.V.relIndex (D.S₂ g) := by
    calc
      _ = 4 * (D.V.relIndex (D.S₂ g) * (2 * 2 ^ rank E)) := by rw [pow_add]; ring
      _ = _ := hb
  have hi0 : 0 < D.V.relIndex (D.S₂ g) := Nat.pos_of_ne_zero (D.V.subgroupOf (D.S₂ g)).index_ne_zero_of_finite
  have hr : rank E = Module.finrank (ZMod 2) (multiplicitySpace σ) := by
    have he := Nat.eq_of_mul_eq_mul_right hi0 heq
    have he' := Nat.pow_right_injective (by decide : 2 ≤ 2) he
    omega
  exact hcount.trans (by rw [hr])

/-- The quotient I/S has order six, so extending to a complete chief series
adds no noncentral binary factors. -/
theorem binary_complete_noncentral_chief_count
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (s : ChiefSeries (D.I g)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount =
      rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h)) + 1 := by
  let I := D.I g
  let Q : NormalNode I := ⟨pCore 2 I,inferInstanceAs (pCore 2 I).Normal⟩
  have hQ : Q.val = (D.S g).subgroupOf I := by
    change pCore 2 I = ((pCore 2 I).map I.subtype).comap I.subtype
    rw [comap_map_eq_self_of_injective I.subtype_injective]
  obtain ⟨a,ha0,ha1⟩ := exists_chiefSeries (⊥ : NormalNode I) Q bot_le
  have hca := binary_noncentral_chief_count h b g hgL hgN a ha0
    ((congrArg Subtype.val ha1).trans hQ)
  let e := binarySourceCoreEquiv h b h.U_normal_in_T.1 g hgL hgN
  have ht : HasCentralPChiefFactors 2 (I ⧸ Q.val) :=
    centralTwoChiefFactors_of_not_four_dvd (by
      change ¬ 4 ∣ Nat.card (I ⧸ pCore 2 I)
      rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
      decide)
  obtain ⟨a',ha'0,ha'1⟩ := exists_chiefSeries Q (⊤ : NormalNode I) le_top
  have hca' : a'.noncentralTwoCount = 0 :=
    a'.noncentralTwoCount_eq_zero_of_centralTwo_quotient Q ha'0.ge ht
  let t : ChiefSeries I := a.smash a' (ha1.trans ha'0.symm)
  have he := s.noncentralTwoCount_eq t
    (hs0.trans (by simpa only [t,RelSeries.head_smash] using ha0.symm))
    (hs1.trans (by simpa only [t,RelSeries.last_smash] using ha'1.symm))
  rw [he]
  dsimp only [t]
  rw [ChiefSeries.noncentralTwoCount_smash,hca,hca',add_zero]

/-- The same count is the fixed-index length of the original cubic on S. -/
theorem binary_cubic_length_eq_opposite_rank_add_one
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (C : Subgroup G) (hC : Nat.card C = 3) (hCI : C ≤ D.I g) :
    conjugationCubicLength C (D.S g) =
      rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h)) + 1 := by
  let I := D.I g
  let e := binarySourceCoreEquiv h b h.U_normal_in_T.1 g hgL hgN
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 I := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 I) x) = 1 ↔ x ∈ pCore 2 I
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := hk.symm ▸ pCore_isPGroup
  have hc : Nat.card (C.subgroupOf I) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCI).toEquiv).trans hC
  obtain ⟨s,hs0,hs1⟩ := exists_chiefSeries (⊥ : NormalNode I) ⊤ bot_le
  have hcount := CubicComparison.symmetricThree_count f hf hp (C.subgroupOf I) hc s hs0 hs1
  have hQ : (D.S g).subgroupOf I = pCore 2 I := by
    change ((pCore 2 I).map I.subtype).comap I.subtype = pCore 2 I
    exact comap_map_eq_self_of_injective I.subtype_injective _
  rw [hk,← hQ,CubicComparison.length_subgroupOf C (D.S g) I hCI (pCoreIn_le 2 I)] at hcount
  exact hcount.symm.trans (binary_complete_noncentral_chief_count h b g hgL hgN s hs0 hs1)

/-- Cubic fixed-index length at least three on a subgroup of S forces m>1,
measured on the original faithful projection. The lower bound is the
remaining ambient chief-factor calculation of 5.1.23. -/
theorem binary_opposite_rank_gt_one_of_cubic_length
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (C R : Subgroup G) (hC : Nat.card C = 3) (hCI : C ≤ D.I g)
    (hRS : R ≤ D.S g) (hthree : 3 ≤ conjugationCubicLength C R) :
    1 < rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h)) := by
  have hm := conjugationCubicLength_mono C hRS
  rw [binary_cubic_length_eq_opposite_rank_add_one h b g hgL hgN C hC hCI] at hm
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
