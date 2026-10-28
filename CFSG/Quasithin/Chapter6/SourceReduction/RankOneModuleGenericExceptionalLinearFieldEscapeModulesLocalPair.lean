module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalSpan
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversalIndices
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankBounds
public import Theory.Representation.BinaryOffender.CommonCenterBound

/-!
# Mutual local spans under a strict quadratic bound

For an elementary local span U with its faithful action on U/Z, mutual
containment of U and a conjugate in the corresponding local groups gives
quadratic actions in both orientations. The common displacement line bounds
each fixed codimension by the sum of the two actor ranks. A strict quadratic
ratio greater than two therefore forces both actors to vanish. The actual
commutator then lies in both conjugate point kernels.

In the original cubic geometry, containment of the H-span in W supplies
this mutual containment. The Chapter 12 application uses the disjoint
point lines to obtain commutativity and containment in the literal O₂(H).
This does not assume global commutativity of intersecting conjugate planes.

Source: Aschbacher--Smith F.9.12--17 and 5.1.23, printed pp.322--324,
645--646, refs/quasithin.pdf. The rank argument adapts the common-line proof
in Chapter13/Section08/SourceCompletion/QuadraticBound.lean.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open Chapter13.Section08 Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open PairConsequences Chapter13.Section08.CriticalGeometry
variable {G M : Type*} [Group G] [Finite G]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) M}

private theorem pair_codimension
    (s : ConjugationSection H UH Z ρ) (Ug₀ A₀ : Subgroup G)
    [IsElementaryAbelian 2 Ug₀]
    (hUg : Ug₀ ≤ H) (hA : Nat.card A₀ = 2)
    (hnorm : UH ≤ normalizer (A₀ : Set G))
    (hcent : Ug₀ ≤ centralizer (A₀ : Set G)) :
    fixedCodim ρ (Source.starImage H Ug₀) ≤ rank (Source.starImage H Ug₀) +
      Module.finrank (ZMod 2) (M ⧸ s.image (Source.DH UH Ug₀ A₀)) := by
  let Ug := Ug₀
  let A := A₀
  let Dh := Source.DH UH Ug A
  let B := Source.starImage H Ug
  have hUgH : Ug ≤ H := hUg
  have hUA : UH ≤ normalizer (A : Set G) := hnorm
  have hUgA : Ug ≤ centralizer (A : Set G) := hcent
  have hn : Ug ≤ normalizer (Dh : Set G) :=
    commutatorPreimage_normalized _ _ _ _ hUA (hUgH.trans s.normalizes)
      Ug.le_normalizer (hUgA.trans (Subgroup.centralizer_le_normalizer _))
  let : IsElementaryAbelian 2 B := starImage_isElementaryAbelian H Ug hUgH
  let τ := ρ.comp B.subtype
  let W : Subrepresentation τ := {
    toSubmodule := s.image Dh
    apply_mem_toSubmodule := by
      rintro ⟨b, hb⟩ v hv
      obtain ⟨a, ha, rfl⟩ := hb
      obtain ⟨u, hu, rfl⟩ := (s.mem_image Dh v).mp hv
      change ρ (QuotientGroup.mk' (pCore 2 H) a) (s.quotient u).toAdd ∈ s.image Dh
      rw [s.conjugates]
      exact ⟨_, (mem_normalizer_iff.mp (hn ha) u).mp hu, rfl⟩ }
  have hcardA : Nat.card A = 2 := hA
  obtain ⟨hdim, hdisp⟩ := s.critical_line_displacement Ug A hUA hcardA
  have hfixed : ∀ b : B, ∀ z ∈ s.image A, τ b z = z := by
    rintro ⟨b, hb⟩ z hz
    obtain ⟨a, ha, rfl⟩ := hb
    obtain ⟨u, hu, rfl⟩ := (s.mem_image A z).mp hz
    apply sub_eq_zero.mp
    change ρ (QuotientGroup.mk' (pCore 2 H) a) (s.quotient u).toAdd - (s.quotient u).toAdd = 0
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    have hc : ⁅(a : G), (u : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hUgA ha) u hu).symm
    change ⁅(a : G), (u : G)⁆ ∈ Z
    rw [hc]
    exact Z.one_mem
  have hbound := CommonCenter.fixedCodim_top_le_rank_add_codim τ W (s.image A) hdim
    (fun b v hv => hdisp b b.property v hv) hfixed
  have hcodim : fixedCodim τ ⊤ = fixedCodim ρ B := by
    change Module.finrank (ZMod 2) (M ⧸ fixedSpace (ρ.comp B.subtype) ⊤) = _
    rw [fixedSpace_comp_map, ←MonoidHom.range_eq_map, B.range_subtype]
    rfl
  rw [hcodim] at hbound
  exact hbound

omit [Finite G] [FiniteDimensional (ZMod 2) M] in
private theorem pair_quadratic
    (s : ConjugationSection H UH Z ρ) (Ug : Subgroup G)
    [IsMulCommutative Ug] (hn : UH ≤ normalizer (Ug : Set G)) :
    IsQuadratic ρ (Source.starImage H Ug) := by
  have hd : ⁅Ug, ⁅Ug, UH⁆⁆ ≤ Z := by
    rw [commutator_comm Ug UH, commutator_comm Ug]
    exact (quadratic_of_normalizes_abelian UH Ug hn inferInstance).le.trans bot_le
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
  have hv : (s.quotient u).toAdd = v := congrArg Multiplicative.toAdd hu
  rw [← hv, s.displacement]
  apply sub_eq_zero.mp
  rw [s.displacement]
  exact (s.quotient_eq_zero_iff _).mpr
    (commutator_le.mp hd a ha _ (commutator_mem_commutator hb u.property))

/-- Mutual conjugate containment and the strict quadratic bound force the
commutator into the intersection of the two original point kernels. -/
theorem conjugate_pair_trivial_of_strict_ratio
    [IsElementaryAbelian 2 UH]
    (s : ConjugationSection H UH Z ρ) (hz : Nat.card Z = 2)
    (hf : Function.Injective ρ) (hr : 2 < quadraticRatio ρ)
    (g : G)
    (hforward : UH.map (MulAut.conj g).toMonoidHom ≤ H)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom) :
    Source.starImage H (UH.map (MulAut.conj g).toMonoidHom) = ⊥ ∧
      Source.starImage H (UH.map (MulAut.conj g⁻¹).toMonoidHom) = ⊥ ∧
      ⁅UH, UH.map (MulAut.conj g).toMonoidHom⁆ ≤
        Z ⊓ Z.map (MulAut.conj g).toMonoidHom := by
  let Ug := UH.map (MulAut.conj g).toMonoidHom
  let Ur := UH.map (MulAut.conj g⁻¹).toMonoidHom
  let Zg := Z.map (MulAut.conj g).toMonoidHom
  let Zr := Z.map (MulAut.conj g⁻¹).toMonoidHom
  let E := Source.starImage H Ug
  let F := Source.starImage H Ur
  let : IsElementaryAbelian 2 Ug := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 Ur := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := starImage_isElementaryAbelian H Ug hforward
  have hback : Ur ≤ H := reversed_actor_le H UH g hreverse
  let : IsElementaryAbelian 2 F := starImage_isElementaryAbelian H Ur hback
  have hUHr : UH ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hforward
    rwa [conjugate_inverse_cancel] at hh
  have hnorm (a : G) (ha : UH ≤ H.map (MulAut.conj a).toMonoidHom) :
      UH ≤ normalizer ((UH.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) :=
    ha.trans ((map_mono s.normalizes).trans_eq (map_equiv_normalizer_eq _ _))
  have hc₁ := pair_codimension s Ug Zg hforward
    (by rw [card_map_of_injective (MulAut.conj g).injective, hz])
    (hreverse.trans ((s.centralizes_conjugate_line g).trans (Subgroup.centralizer_le_normalizer _)))
    ((map_mono (s.le.trans s.centralizes)).trans
      (map_centralizer_le_centralizer_image _ _))
  have hc₂ := pair_codimension s Ur Zr hback
    (by rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hz])
    (hUHr.trans ((s.centralizes_conjugate_line g⁻¹).trans (Subgroup.centralizer_le_normalizer _)))
    ((map_mono (s.le.trans s.centralizes)).trans
      (map_centralizer_le_centralizer_image _ _))
  obtain ⟨he, hf'⟩ := reversed_rank_and_codimension s g hforward hreverse hf
  change rank F = _ at he
  change _ = rank E at hf'
  change fixedCodim ρ E ≤ rank E + _ at hc₁
  change fixedCodim ρ F ≤ rank F + _ at hc₂
  rw [← he] at hc₁
  rw [hf'] at hc₂
  have hstrict (A : Subgroup (Source.Hstar H)) [IsElementaryAbelian 2 A]
      (hq : IsQuadratic ρ A) (hn : A ≠ ⊥) : 2 * rank A < fixedCodim ρ A := by
    apply Nat.lt_of_not_ge
    intro hd
    exact not_le_of_gt hr ((quadraticRatio_le_two_iff ρ).mpr ⟨A, ⟨hn, inferInstance⟩, hq, hd⟩)
  have hzE : E = ⊥ := by
    by_contra heN
    have hs := hstrict E (pair_quadratic s Ug (hnorm g hreverse)) heN
    have hzF : F ≠ ⊥ := by
      intro hh
      simp only [hh, Representation.BinaryOffender.rank_bot] at hc₁
      omega
    have hs' := hstrict F (pair_quadratic s Ur (hnorm g⁻¹ hUHr)) hzF
    omega
  have hzF : F = ⊥ := by
    by_contra hfN
    have hs := hstrict F (pair_quadratic s Ur (hnorm g⁻¹ hUHr)) hfN
    rw [hzE, Representation.BinaryOffender.rank_bot, add_zero] at hc₂
    omega
  have hcomm (A : Subgroup G) (hAH : A ≤ H) (he : Source.starImage H A = ⊥) :
      ⁅UH, A⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let a' : H := ⟨a, hAH ha⟩
    have hπ : QuotientGroup.mk' (pCore 2 H) a' = 1 := by
      have hh : QuotientGroup.mk' (pCore 2 H) a' ∈ Source.starImage H A :=
        mem_map_of_mem _ ha
      simpa only [he, mem_bot] using hh
    apply (s.quotient_eq_zero_iff ⟨⁅a, u⁆, s.commutator_mem a' ⟨u, hu⟩⟩).mp
    rw [← s.displacement a' ⟨u, hu⟩, hπ, map_one, Module.End.one_apply, sub_self]
  refine ⟨hzE, hzF, le_inf (hcomm Ug hforward hzE) ?_⟩
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (hcomm Ur hback hzF)
  rw [map_commutator] at hh
  have hc := conjugate_inverse_cancel g⁻¹ UH
  simp only [inv_inv] at hc
  change ⁅Ug, Ur.map (MulAut.conj g).toMonoidHom⁆ ≤ Zg at hh
  rw [hc, commutator_comm] at hh
  exact hh

open ChapterG.Section02 ChapterG.Section02.Setup
variable {T : Sylow 2 G} {C : Subgroup G} {z : G}

omit [FiniteDimensional (ZMod 2) M] [Module (ZMod 2) M] [AddCommGroup M] in
/-- The original local span and its cubic conjugate lie in each other's local groups. -/
theorem LocalData.local_pair_containment
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hle : (setup T H C z).U ≤ (setup T (centralizer ({z} : Set G)) C z).W g) :
    conjugate (setup T H C z).U g ≤ H ∧
      (setup T H C z).U ≤ conjugate H g := by
  let D := setup T (centralizer ({z} : Set G)) C z
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨_, _, _, _, hgI⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  have hST : D.S g ≤ (T : Subgroup G) :=
    (binary_S_le_LT_core s.U_normal_in_T.1 g hga
      (binaryStarEquiv s.toBaseHypothesis b s.U_normal_in_T.1)
      (binary_source_star_generation s b s.U_normal_in_T.1 g hga hgn)).trans
        s.toBaseHypothesis.binary_core_le_T
  have hSH : D.S g ≤ H := hST.trans (le_sup_right.trans d.g2.local_le)
  have hUS : (setup T H C z).U ≤ D.S g := hle.trans inf_le_right
  have hSg : conjugate (D.S g) g = D.S g :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.S g : Set G)).inv_mem (D.binary_core_normalized g hgI))
  exact ⟨(map_mono hUS).trans (hSg.le.trans hSH),
    hUS.trans (hSg.ge.trans (map_mono hSH))⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
