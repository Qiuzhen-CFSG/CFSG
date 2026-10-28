module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreFactors
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CodeInputs.MarkedCode

/-!
# Binary coordinates on the original core section

Conjugation on the literal elementary quotient P/U gives a binary
representation with the same full kernel as its multiplicative action.
For a selected degree-one pair, the original B/U and its conjugate generate
P/U. Their orders show that their sum is a linear isomorphism, with the
second summand given by the actual selected inverse conjugator. Restriction
to the original I has kernel exactly O₂(I).

These statements construct the quotient action and its two summands; they
do not assume a native hexacode marking or the later tensor decomposition.
Source: Aschbacher--Smith E.2.10, E.2.13--14 and 8.2.8(4--5), printed
pp.222--226,718--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open Normalizer.SmallOvergroups Normalizer.TensorRecognition
open ChapterE HermitianSource Offenders.Parabolic.Construction
variable {G : Type*} [Group G]

/-- Conjugation on the original elementary quotient, regarded as a binary action. -/
@[expose] def sectionRepresentation (K P U : Subgroup G) [(U.subgroupOf P).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G)) :
    Representation (ZMod 2) K (Additive (P ⧸ U.subgroupOf P)) where
  toFun k := (sectionAction K P U hKP hKU k).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext; intro x
    change Additive.ofMul (sectionAction K P U hKP hKU 1 x.toMul) = x
    rw [map_one]; rfl
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change Additive.ofMul (sectionAction K P U hKP hKU (a*b) x.toMul) = _
    rw [map_mul]; rfl

theorem sectionRepresentation_apply (K P U : Subgroup G) [(U.subgroupOf P).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (k : K) (p : P) :
    sectionRepresentation K P U hKP hKU k
      (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) p)) =
      Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P)
        (P.normalizerMonoidHom (inclusion hKP k) p)) := rfl

theorem sectionRepresentation_kernel (K P U : Subgroup G) [(U.subgroupOf P).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G)) :
    (sectionRepresentation K P U hKP hKU).ker = (sectionAction K P U hKP hKU).ker := by
  ext k
  constructor
  · intro hk
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (LinearMap.congr_fun hk (Additive.ofMul x))
  · intro hk
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul (MulEquiv.congr_fun hk x.toMul)

/-- Restricting the actor retains the same literal quotient conjugation. -/
theorem sectionRepresentation_comp (K J P U : Subgroup G)
    [(U.subgroupOf P).Normal] [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hJK : J ≤ K) :
    (sectionRepresentation K P U hKP hKU).comp (inclusion hJK) =
      sectionRepresentation J P U (hJK.trans hKP) (hJK.trans hKU) := by
  apply MonoidHom.ext
  intro j
  apply LinearMap.ext
  intro x
  obtain ⟨p,hp⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) x.toMul
  have hx : x = Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) p) :=
    congrArg Additive.ofMul hp.symm
  rw [hx]
  rfl

/-- The original inclusion B/U → P/U intertwines the two quotient actions. -/
theorem quotientInclusion_equivariant (K P B U : Subgroup G) (hBP : B ≤ P)
    [(U.subgroupOf P).Normal] [(U.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (hKP : K ≤ normalizer (P : Set G)) (hKB : K ≤ normalizer (B : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (k : K)
    (v : Additive (B ⧸ U.subgroupOf B)) :
    quotientInclusion P B U hBP (sectionRepresentation K B U hKB hKU k v) =
      sectionRepresentation K P U hKP hKU k (quotientInclusion P B U hBP v) := by
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b) :=
    congrArg Additive.ofMul hb.symm
  rw [hv,sectionRepresentation_apply,quotientInclusion_mk,quotientInclusion_mk,
    sectionRepresentation_apply]
  rfl

/-- Cardinality of the original quotient agrees with its literal image in P/U. -/
theorem quotientInclusion_card (P B U : Subgroup G) (hBP : B ≤ P)
    [(U.subgroupOf P).Normal] [(U.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)] :
    Nat.card (B ⧸ U.subgroupOf B) =
      Nat.card ((B.subgroupOf P).map (QuotientGroup.mk' (U.subgroupOf P))) := by
  let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl) hBP
  have hi : Function.Injective q := quotientInclusion_injective P B U hBP
  have hr : q.range = (B.subgroupOf P).map (QuotientGroup.mk' (U.subgroupOf P)) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) y
      exact ⟨inclusion hBP b,b.property,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨QuotientGroup.mk' (U.subgroupOf B) ⟨p,hp⟩,rfl⟩
  rw [←hr]
  exact Nat.card_congr (MonoidHom.ofInjective hi).toEquiv

/-- Two-conjugate generation makes the literal code pair map onto P/U. -/
theorem codePairMap_surjective (I V U K : Subgroup G)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [(U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    [IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸
      U.subgroupOf (V ⊓ I.pCoreIn 2))]
    (hKP : K ≤ normalizer (I.pCoreIn 2 : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (a : K)
    (hgen : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj a.val).toMonoidHom = I.pCoreIn 2) :
    Function.Surjective (codePairMap I V U (sectionRepresentation K _ U hKP hKU) a) := by
  let P := I.pCoreIn 2
  let B := V ⊓ P
  let ρ := sectionRepresentation K P U hKP hKU
  let f := codePairMap I V U ρ a
  let Z : Subgroup P := f.range.toAddSubgroup.toSubgroup.comap
    (QuotientGroup.mk' (U.subgroupOf P))
  let ZG := Z.map P.subtype
  have hb : B ≤ ZG := by
    intro b hb
    refine ⟨⟨b,hb.2⟩,?_,rfl⟩
    change Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) ⟨b,hb.2⟩) ∈ f.range
    refine ⟨(Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) ⟨b,hb⟩),0),?_⟩
    rw [codePairMap_apply,map_zero, map_zero, add_zero]
    rfl
  have hb' : B.map (MulAut.conj a.val).toMonoidHom ≤ ZG := by
    rintro _ ⟨b,hb,rfl⟩
    let p : P := ⟨b,hb.2⟩
    let p' := P.normalizerMonoidHom (inclusion hKP a) p
    refine ⟨p',?_,rfl⟩
    change Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) p') ∈ f.range
    refine ⟨(0,Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) ⟨b,hb⟩)),?_⟩
    rw [codePairMap_apply,map_zero,zero_add]
    rfl
  have hp : P ≤ ZG := by
    change I.pCoreIn 2 ≤ ZG
    rw [←hgen]
    exact sup_le hb hb'
  intro v
  obtain ⟨p,hp0⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) v.toMul
  obtain ⟨p',hp',he⟩ := hp p.property
  have hpp : p' = p := Subtype.ext he
  have hv : v ∈ f.range := by
    change Additive.ofMul v.toMul ∈ f.range
    rw [←hp0,←hpp]
    exact hp'
  exact hv
variable [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]
  {T : Sylow 2 G} {H M I : Subgroup G} {i : I} {S : Sylow 2 I}

/-- The literal B/U has the selected actor's rank. -/
theorem selected_intersection_quotient_card (s : Selected H T M V I 1 i S)
    (U : Subgroup G) (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [(U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    (r : ℕ) (hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = r) :
    Nat.card ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2)) = 2^r := by
  let B := V ⊓ I.pCoreIn 2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ V from inf_le_left)
  let q := QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
  let Bq := (B.subgroupOf (I.pCoreIn 2)).map q
  let : IsElementaryAbelian 2 (B.subgroupOf (I.pCoreIn 2)) :=
    IsElementaryAbelian.subgroupOf inf_le_right
  let : IsElementaryAbelian 2 Bq := IsElementaryAbelian.map q
  have hdim : rank Bq = r := (selected_core_quotient_factors s U hU r hr).2.2.1
  have hc : Nat.card Bq = 2^r := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 Bq).exists_card_eq
    rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hdim
    simpa only [hdim] using hn
  exact (quotientInclusion_card (I.pCoreIn 2) B U inf_le_right).trans hc

/-- The actual selected conjugator gives the two-copy coordinates of P/U. -/
theorem selected_codePairMap_bijective (s : Selected H T M V I 1 i S)
    (U K : Subgroup G) (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hIC : I ≤ centralizer (U : Set G))
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [(U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    (hKP : K ≤ normalizer (I.pCoreIn 2 : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hIK : I ≤ K)
    [IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸
      U.subgroupOf (V ⊓ I.pCoreIn 2))] :
    Function.Bijective (codePairMap I V U (sectionRepresentation K _ U hKP hKU)
      (inclusion hIK i⁻¹)) := by
  let r := rank (inducedAutomizer V
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2))
  obtain ⟨hjoin,_,hBA,_⟩ := selected_core_factor_geometry s U hU
  have hg : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj (inclusion hIK i⁻¹).val).toMonoidHom = I.pCoreIn 2 := by
    change (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2
    rw [hBA]
    exact hjoin
  have hs := codePairMap_surjective I V U K hKP hKU (inclusion hIK i⁻¹) hg
  have hB := selected_intersection_quotient_card s U hU r rfl
  obtain ⟨_,_,hP,_⟩ := selected_core_section_of_ranks s U hU hIC r (rank U) rfl rfl
  apply hs.bijective_of_nat_card_le
  rw [Nat.card_prod]
  change Nat.card ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2)) *
      Nat.card ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2)) ≤
      Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))
  rw [hB,hP,←pow_add,two_mul]

/-- The full two-core is the kernel of the original I action in these coordinates. -/
theorem selected_sectionRepresentation_kernel (s : Selected H T M V I 1 i S)
    (U K : Subgroup G) (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    (hKP : K ≤ normalizer (I.pCoreIn 2 : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hIK : I ≤ K) :
    ((sectionRepresentation K _ U hKP hKU).comp (inclusion hIK)).ker = pCore 2 I := by
  obtain ⟨hUN,hker⟩ := selected_core_action_kernel s U hU
  let := hUN
  change (sectionRepresentation K _ U hKP hKU).ker.comap (inclusion hIK) = _
  rw [sectionRepresentation_kernel]
  ext r
  rw [←hker,mem_centralizerModulo_iff]
  simp only [mem_top,true_and]
  rw [show r ∈ (sectionAction K (I.pCoreIn 2) U hKP hKU).ker.comap (inclusion hIK) ↔
      ∀ p : I.pCoreIn 2, ⁅(r : G),(p : G)⁆ ∈ U from
    mem_sectionAction_ker K _ U hKP hKU (inclusion hIK r)]
  constructor
  · intro hr p hp
    have hc := hr ⟨p.val,mem_map_of_mem I.subtype hp⟩
    change ⁅(p : G),(r : G)⁆ ∈ U
    simpa only [commutatorElement_inv] using U.inv_mem hc
  · intro hr p
    obtain ⟨p0,hp0,he⟩ := p.property
    have hc : ⁅(p0 : G),(r : G)⁆ ∈ U := hr p0 hp0
    change ⁅(r : G),(p : G)⁆ ∈ U
    rw [←he]
    change ⁅(r : G),(p0 : G)⁆ ∈ U
    simpa only [commutatorElement_inv] using U.inv_mem hc
end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

