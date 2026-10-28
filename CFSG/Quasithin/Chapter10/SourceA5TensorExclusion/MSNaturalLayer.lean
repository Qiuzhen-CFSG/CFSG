module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerModel
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.InitialCore

/-!
# Initial natural Sp4(4) layer in the original tensor branch

The original outside H/K construction and its literal symplectic quotient
supply every input of the FF recognition: the initial module and faithful
quotient action, a simple self-centralizing component, its order and SQTK.
The output is the natural action on the canonical moved/fixed section of
Ω₁(Z(O₂(H))). No initial natural-module or offender premise is assumed.
The equality of this moving layer with the whole intrinsic commutator core
still requires the MS93 critical-distance and distance-two arguments.

Source: Aschbacher--Smith9.3.10/C.1.32 and MS93 (3.2)(vi).
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal image of the original component has every group hypothesis
used by initial FF recognition, including SQTK inherited from the ambient setup. -/
theorem source_tensor_sp4_quotient_data
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g) :
    let B := K.map (QuotientGroup.mk' (pCore 2 H))
    K.Normal ∧ B.Normal ∧ IsSimpleGroup B ∧ IsQuasisimple B ∧
      centralizer (B : Set (H ⧸ pCore 2 H)) = ⊥ ∧
      Nat.card B = 979200 ∧ IsSQTK KnownSimple.IsKnownSimple B ∧
      pCore 2 H ≠ ⊥ := by
  let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
  let B := K.map (QuotientGroup.mk' (pCore 2 H))
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 2) hF
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup
    (F := F) (by omega)
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (eK.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv).isSimpleGroup
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  obtain ⟨hKN,hBN,hBS,hBQ,hBC⟩ := component_image_structure K R hK hodd.isPGroup hprod
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  have hQne : pCore 2 H ≠ ⊥ := by
    intro hz
    have ht : (⊤ : Subgroup H) ≤ ⊥ := by
      intro h _
      have hc : h ∈ centralizer (pCore 2 H : Set H) := by
        rw [hz]
        intro x hx
        have hx1 : x = 1 := hx
        simp only [hx1,one_mul,mul_one]
      exact hz ▸ hself hc
    exact hK.ne_bot (le_bot_iff.mp (le_top.trans ht))
  have hlocal : H ∈ Chapter1.H G := by
    exact fun hz => hQne ((map_eq_bot_iff_of_injective (pCore 2 H) H.subtype_injective).mp hz)
  have hsq : IsSQTK KnownSimple.IsKnownSimple B :=
    (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hlocal).subgroup B
  have hc : Nat.card B = 979200 := by
    rw [← Nat.card_congr (cComponentTwoCoreQuotientEquiv hK).toEquiv,
      Nat.card_congr eK.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF]
    norm_num
  exact ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩

/-- The original initial moving section is the natural symplectic module,
with all ambient classification inputs discharged from the source setup. -/
theorem source_tensor_sp4_initial_natural
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g) :
    let X := omegaCenterIn (pCore 2 H)
    let B := K.map (QuotientGroup.mk' (pCore 2 H))
    ∃ hBN : B.Normal,
      ∃ ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive X),
        Function.Injective ρ ∧ IsFFModule ρ ∧
        (∀ (h : H) (x : Additive X),
          ((ρ (QuotientGroup.mk' (pCore 2 H) h) x).toMul : H) =
            h * (x.toMul : H) * h⁻¹) ∧
        IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) ∧
        letI := hBN
        ChapterC.RankTwo.Sp4Four.HasNaturalMovingSection ρ B := by
  let B := K.map (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,_⟩ :=
    source_tensor_sp4_quotient_data D hn H hRH hLH hout hs K hK hF eK hfit hprod
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨ρ,hf,hff,hact⟩ :=
    source_tensor_sp4_msFFModule D hn H hRH hLH hout hs K hK hF eK hfit hprod
  obtain ⟨hirr,E,hE,he⟩ :=
    ChapterC.RankTwo.Sp4Four.ff_card_sp4_four_moved_natural ρ B hc hBC hsq hf hff
  exact ⟨hBN,ρ,hf,hff,hact,hirr,E,hE,he⟩


/-- The original initial orbit and full central omega layer generate the
same actual commutator subgroup; no natural-module input is assumed. -/
theorem source_tensor_sp4_initialCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g) :
    ⁅omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H),K⁆ =
      ⁅omegaCenterIn (pCore 2 H),K⁆ := by
  let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
  let B := K.map (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D hn H hRH hLH hout hs K hK hF eK hfit hprod
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  obtain ⟨_,hfaith,_⟩ :=
    source_tensor_sp4_msCentralOrbit D hn H hRH hLH hout hs K hK hF eK hfit hprod
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  have hRne : R ≠ ⊥ := fun hr =>
    hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  exact ChapterC.RankTwo.Sp4Four.initialCore_eq R hms hodd.isPGroup hRne
    hodd.twoCore_le hself hfaith (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    K B rfl hc hBC hsq

end CFSG.Quasithin.Chapter10
