module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Generation by the distinguished subgroup

The outside conjugate of Z lies in U and is not central in L.
The proved normal-layer dichotomy of a short block forces its L-normal
closure to be all of U. This is original 2.4.16(3), printed pp.533–534.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Original 2.4.16(3): the actual conjugate Zˣ generates U under L.
The short-layer dichotomy replaces an explicit enumeration of natural lines. -/
theorem source_distinguished_generates_module
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    conjugateSpanBy ((distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom)
      (d.block.map d.H.subtype) = sourceModule (d.block.map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let A := R ⊓ centralizer (R : Set G)
  let U := sourceModule L
  let e := MulAut.conj x⁻¹
  let E := Z.map e.toMonoidHom
  let W := conjugateSpanBy E L
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hq : 1 < Nat.card Z := by
    rw [hb.2.1]
    exact Nat.one_lt_pow (by have hn := hL.1; omega) (by decide)
  have hEn : E ≠ ⊥ := by
    intro he
    have hc : Nat.card E = Nat.card Z := card_map_of_injective e.injective
    rw [he,card_bot] at hc
    omega
  have hEU : E ≤ U := by
    have hEA : E ≤ A := by
      by_cases hz : center L = ⊥
      · have he : E = Z := mem_normalizer_iff_map_conj_eq.mp
          (source_distinguished_normalized_by_sylow d hG T hST hsingle hL hz (T.inv_mem hxT))
        exact he ▸ hb.2.2.1
      · exact le_sup_right.trans_eq
          (source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS).2
    exact hEA.trans ((source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left)
  have hLU : L ≤ normalizer (U : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hWU : W ≤ U := conjugateSpanBy_le hEU hLU
  have hWL : W ≤ L := hWU.trans (map_subtype_le _)
  let : (W.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy E L)
  have hWblock : W.subgroupOf L ≤ ChapterC.blockU L := by
    intro w hw
    obtain ⟨u,hu,he⟩ := hWU hw
    exact (Subtype.ext he : u=w) ▸ hu
  rcases ChapterC.RankOne.ChiProduct.short_normal_layer_dichotomy hK.2.1 (W.subgroupOf L) hWblock with hc | he
  · have hEC : E ≤ (center L).map L.subtype := by
      intro a ha
      have hw := le_conjugateSpanBy E L ha
      exact mem_map_of_mem L.subtype (hc (show (⟨a,hWL hw⟩ : L) ∈ W.subgroupOf L from hw))
    by_cases hz : center L = ⊥
    · rw [hz,Subgroup.map_bot] at hEC
      exact False.elim (hEn (bot_unique hEC))
    · have hd := (source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS).1
      have hEZ : E ≤ Z := by
        change E ≤ distinguishedZ d
        rw [distinguishedZ_of_center_ne_bot d hz]
        exact hEC
      exact False.elim (hEn (eq_bot_iff.mpr fun a ha => hd.le_bot ⟨hEZ ha,ha⟩))
  · have hm := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le hWL] at hm
    exact hm
end CFSG.Quasithin.Chapter2.LinearShadows.Single
