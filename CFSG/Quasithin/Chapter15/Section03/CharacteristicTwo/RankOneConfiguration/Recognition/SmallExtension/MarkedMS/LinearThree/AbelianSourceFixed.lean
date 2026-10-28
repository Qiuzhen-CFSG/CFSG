module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.Point
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.Radical

/-!
# The literal index-seven subgroup in the fixed-line MS branch

For an abelian MS core of order sixteen, the proved natural quotient has
one copy and a fixed kernel of order two. The ambient-action construction
retains its literal projection, and a two-subgroup fixes a nonzero quotient
point. Mapping that point stabilizer through the inclusion of L ∨ R gives
an actual subgroup of the original group, of relative index seven and with
exactly the commutator membership condition in C.1.34(5).

The omega-center assertion follows from the nonsplit-cover fixed-space
argument. The fixed-vector and odd-index radical argument identifies the
two-core of this same point subgroup with R. Both conclusions transport
through the literal join inclusion, retaining the specified action on
Q/C_Q(L).

Source: Aschbacher–Smith C.1.34(5), printed p.137; Meierfrankenfeld–Stellmacher,
“Pushing up weak BN-pairs of rank two” (1993), Main Theorem (8), p.830.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- Order sixteen selects the single natural cover, retaining its actual kernel. -/
theorem SmallMSPair.abelian_source_fixed_quotient (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16) :
    ∃ _q : BinaryMS.AbelianCore.NaturalQuotient (h.binaryInput e) 1,
      Nat.card (BinaryMS.coreFixed (L.subgroupOf (L ⊔ R))) = 2 := by
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  obtain ⟨m, hm, ⟨q⟩⟩ := BinaryMS.AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h.binaryInput e) hc'
  have hd : Nat.card (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) = 16 :=
    (Nat.card_congr (binaryCoreEquiv L R).toEquiv).trans hcard
  have hq := q.card
  rw [hd] at hq
  rcases hm with rfl | rfl
  · exact ⟨q, by norm_num at hq; omega⟩
  · norm_num at hq
    omega

/-- The required literal point subgroup exists and has index seven.
Its two-core is not identified with R by this construction alone. -/
theorem SmallMSPair.abelian_source_fixed_point (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) :
    let C := msQ L R ⊓ centralizer (L : Set G)
    ∃ (G₁ : Subgroup G) (q : msQ L R), (q : G) ∉ C ∧ G₁ ≤ L ⊔ R ∧
      S ≤ G₁ ∧ (G₁.subgroupOf (L ⊔ R)).index = 7 ∧
      ∀ g ∈ L ⊔ R, g ∈ G₁ ↔ g * (q : G) * g⁻¹ * (q : G)⁻¹ ∈ C := by
  obtain ⟨q,_⟩ := h.abelian_source_fixed_quotient e hc hcard
  let J := L ⊔ R
  let K := L.subgroupOf J
  let b := h.binaryInput e
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore K) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  let := b.abelianCore_elementary_of_naturalQuotient hc' q
  obtain ⟨hSp,hSJ,_⟩ := Chapter1.isSylowIn_iff.mp hS
  obtain ⟨d,hd,hSP,hindex⟩ := q.exists_pointSubgroup b (S.subgroupOf J) hSp.comap_subtype
  let P := q.pointSubgroup b ((q.projection d).toAdd 0)
  let H := P.map J.subtype
  let d' : msQ L R := ⟨(d.val : G), by
    rw [← binaryCore_map L R]
    exact mem_map_of_mem J.subtype d.property⟩
  have hmem (g : J) : (g : G) ∈ H ↔ g ∈ P := mem_map_iff_mem J.subtype_injective
  refine ⟨H,d',?_,map_subtype_le P,?_,?_,?_⟩
  · intro hcD
    apply hd
    intro l hl
    apply Subtype.ext
    exact hcD.2 l hl
  · intro s hs
    exact (hmem ⟨s,hSJ hs⟩).mpr (hSP hs)
  · have he : H.subgroupOf J = P :=
      comap_map_eq_self_of_injective J.subtype_injective P
    rw [he]
    exact hindex
  · intro g hg
    rw [hmem ⟨g,hg⟩, q.mem_pointSubgroup_iff]
    have hdq : g * (d' : G) * g⁻¹ * (d' : G)⁻¹ ∈ msQ L R := by
      change g * (d.val : G) * g⁻¹ * (d.val : G)⁻¹ ∈ msQ L R
      rw [← binaryCore_map L R]
      have hn : (BinaryMS.commutatorCore K).Normal := by
        let := b.component_normal
        infer_instance
      exact mem_map_of_mem J.subtype
        ((BinaryMS.commutatorCore K).mul_mem
          (hn.conj_mem d d.property ⟨g,hg⟩) ((BinaryMS.commutatorCore K).inv_mem d.property))
    constructor
    · intro hfix
      refine ⟨hdq, ?_⟩
      intro l hl
      exact congrArg Subtype.val (hfix ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)
    · intro hfix l hl
      apply Subtype.ext
      exact hfix.2 l hl

/-- The fixed-line branch supplies the original omega-center containment,
using the center mapped from the actual join. -/
theorem SmallMSPair.abelian_source_fixed_omega (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    omegaCenterIn S ≤
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ R) := by
  obtain ⟨q,_⟩ := h.abelian_source_fixed_quotient e hc hcard
  let J := L ⊔ R
  let b := h.binaryInput e
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf J)) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  let := b.abelianCore_elementary_of_naturalQuotient hc' q
  obtain ⟨P,hP⟩ := hS
  have hrP : R.subgroupOf J ≤ (P : Subgroup J) := by
    intro r hr
    have hs : (r : G) ∈ (P : Subgroup J).map J.subtype := hP ▸ hRS hr
    exact (mem_map_iff_mem J.subtype_injective).mp hs
  have hd : Nat.card (BinaryMS.commutatorCore (L.subgroupOf J)) = 16 :=
    (Nat.card_congr (binaryCoreEquiv L R).toEquiv).trans hcard
  have hh := map_mono (f := J.subtype) (q.sylow_omega_le_center b hd P hrP)
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
    hP] at hh
  exact hh

/-- MS3 yields a vector in the actual nonsplit core, outside its fixed line,
centralized by the original radical R. -/
theorem SmallMSPair.abelian_source_fixed_radical_vector (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16) :
    ∃ d : msQ L R, (d : G) ∉ msQ L R ⊓ centralizer (L : Set G) ∧
      (d : G) ∈ centralizer (R : Set G) := by
  obtain ⟨q,_⟩ := h.abelian_source_fixed_quotient e hc hcard
  let J := L ⊔ R
  let b := h.binaryInput e
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf J)) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  let := b.abelianCore_elementary_of_naturalQuotient hc' q
  have hd : Nat.card (BinaryMS.commutatorCore (L.subgroupOf J)) = 16 :=
    (Nat.card_congr (binaryCoreEquiv L R).toEquiv).trans hcard
  obtain ⟨d,hdC,hdR⟩ := q.exists_radical_fixed_core b hd
  let d' : msQ L R := ⟨(d.val : G), by
    rw [← binaryCore_map L R]
    exact mem_map_of_mem J.subtype d.property⟩
  refine ⟨d',?_,?_⟩
  · intro hdC'
    apply hdC
    intro l hl
    apply Subtype.ext
    exact hdC'.2 l hl
  · intro r hr
    have he := congrArg (fun x : BinaryMS.commutatorCore (L.subgroupOf J) =>
      ((x : J) : G)) (hdR ⟨r,(show R ≤ J from le_sup_right) hr⟩ hr)
    have hval := b.coreAmbientConjugation_apply ⟨r,(show R ≤ J from le_sup_right) hr⟩ d
    have hval' := congrArg Subtype.val hval
    have hc : r * (d' : G) * r⁻¹ = (d' : G) := hval'.symm.trans he
    exact mul_inv_eq_iff_eq_mul.mp hc

/-- The fixed-line point stabilizer has the original radical as its two-core. -/
theorem SmallMSPair.abelian_source_fixed_stabilizer (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    MSPointStabilizer L R S := by
  obtain ⟨q,_⟩ := h.abelian_source_fixed_quotient e hc hcard
  let J := L ⊔ R
  let K := L.subgroupOf J
  let b := h.binaryInput e
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore K) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  let := b.abelianCore_elementary_of_naturalQuotient hc' q
  obtain ⟨T,hT⟩ := hS
  have hRT : R.subgroupOf J ≤ (T : Subgroup J) := by
    intro r hr
    have hs : (r : G) ∈ (T : Subgroup J).map J.subtype := hT ▸ hRS hr
    exact (mem_map_iff_mem J.subtype_injective).mp hs
  obtain ⟨d,hd,hTP,hindex⟩ := q.exists_pointSubgroup b (T : Subgroup J) T.isPGroup'
  let P := q.pointSubgroup b ((q.projection d).toAdd 0)
  let H := P.map J.subtype
  let d' : msQ L R := ⟨(d.val : G), by
    rw [← binaryCore_map L R]
    exact mem_map_of_mem J.subtype d.property⟩
  have hmem (g : J) : (g : G) ∈ H ↔ g ∈ P := mem_map_iff_mem J.subtype_injective
  have hdcard : Nat.card (BinaryMS.commutatorCore K) = 16 :=
    (Nat.card_congr (binaryCoreEquiv L R).toEquiv).trans hcard
  have hv : (q.projection d).toAdd 0 ≠ 0 := by
    intro hz
    exact hd ((q.oneProjection_kernel b (Additive.ofMul d)).mp hz)
  have hcore : P.pCoreIn 2 = R.subgroupOf J :=
    q.pointSubgroup_pCoreIn b hdcard T hRT _ hv hTP
  refine ⟨H,d',?_,map_subtype_le P,?_,?_,?_,?_⟩
  · intro hcD
    apply hd
    intro l hl
    apply Subtype.ext
    exact hcD.2 l hl
  · rw [← hT]
    exact map_mono hTP
  · have he : H.subgroupOf J = P :=
      comap_map_eq_self_of_injective J.subtype_injective P
    rw [he]
    exact hindex
  · change (P.map J.subtype).pCoreIn 2 = R
    rw [← map_pCoreIn_of_injective 2 P J.subtype J.subtype_injective, hcore,
      map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)]
  · intro g hg
    rw [hmem ⟨g,hg⟩, q.mem_pointSubgroup_iff]
    have hdq : g * (d' : G) * g⁻¹ * (d' : G)⁻¹ ∈ msQ L R := by
      change g * (d.val : G) * g⁻¹ * (d.val : G)⁻¹ ∈ msQ L R
      rw [← binaryCore_map L R]
      have hn : (BinaryMS.commutatorCore K).Normal := by
        let := b.component_normal
        infer_instance
      exact mem_map_of_mem J.subtype
        ((BinaryMS.commutatorCore K).mul_mem
          (hn.conj_mem d d.property ⟨g,hg⟩) ((BinaryMS.commutatorCore K).inv_mem d.property))
    constructor
    · intro hfix
      refine ⟨hdq, ?_⟩
      intro l hl
      exact congrArg Subtype.val (hfix ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)
    · intro hfix l hl
      apply Subtype.ext
      exact hfix.2 l hl

/-- Both geometric clauses of C.1.34(5), for the literal fixed-line cover. -/
theorem SmallMSPair.abelian_source_fixed_geometry (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    omegaCenterIn S ≤
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ R) ∧
      MSPointStabilizer L R S :=
  ⟨h.abelian_source_fixed_omega e hc hcard S hS hRS,
    h.abelian_source_fixed_stabilizer e hc hcard S hS hRS⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
