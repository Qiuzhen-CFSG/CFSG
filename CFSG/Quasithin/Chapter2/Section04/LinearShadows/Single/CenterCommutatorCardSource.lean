module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideStabilitySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFusionSource
public import Theory.GroupTheory.CentralDisplacementCard
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Orders in the centerless outside-involution row

For the original centerless natural block, put R=J(S) and Z=Z(R).
An outside involution centralizing Z has |[R,t]|=|Z|²: its displacement
homomorphism maps onto Z and has kernel Z. The two conjugate elementary
factors of R each have order |Z|² and intersect in Z, giving |R|=|Z|³.
These are the literal subgroup orders used in the centralizing-involution
exclusion, without an additional model or action hypothesis.

Source: Aschbacher–Smith, Lemma 2.4.21, printed p.536, using 2.4.14(1).
-/
public section
open Subgroup
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_outside_commutator_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hcenter : center (d.block.map d.H.subtype) = ⊥)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1)
    (htZ : t ∈ centralizer
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G) : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    Nat.card (⁅R,zpowers t⁆ : Subgroup G) = Nat.card (R ⊓ centralizer (R : Set G) : Subgroup G)^2 := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  let K := ⁅R,zpowers t⁆
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hL'
  have hKR : K ≤ R := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (ht.2.2 htT))
  have hfix := source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hunique
    t htT htS ht2 htZ
  have hquad := source_outside_involution_double_commutator d hG T hST hsingle hL hM hTM hunique
    t htT htS ht2
  have htrans := (source_centerless_outside_involution_fusion d hG T hST hsingle hL hM hTM hunique
    hcenter t htT htS ht2 htZ).1
  apply card_eq_square_of_central_displacement K Z t hfix.2.le
    ((show Z ≤ centralizer (R:Set G) from inf_le_right).trans (centralizer_le hKR))
    ?_ hquad htrans
  apply le_antisymm
  · exact (inf_le_inf_right _ hKR).trans hfix.1.le
  · exact le_inf hfix.2.le (hfix.1.symm.le.trans inf_le_right)


theorem source_centerless_sylow_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hcenter : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    Nat.card R = Nat.card (R ⊓ centralizer (R : Set G) : Subgroup G)^3 := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let U := sourceModule L
  let Z := R ⊓ centralizer (R : Set G)
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hgen : U ⊔ V = R :=
    ((source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS).1.symm
  have hinter : U ⊓ V = Z :=
    source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hRU : R ≤ normalizer (U:Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V
    ((le_sup_right.trans_eq hgen).trans hRU)
  have hcard : Nat.card U = Nat.card Z^2 :=
    source_centerless_elementary_pair_card d hG T hST hsingle hL hM hTM hunique hcenter
  have hV : Nat.card V = Nat.card U := card_map_of_injective (MulAut.conj x⁻¹).injective
  rw [hV,hcard,hinter,hgen] at hprod
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=Z))
  change Nat.card Z * Nat.card R = Nat.card Z * Nat.card Z^3
  rw [←hprod]
  ring
end CFSG.Quasithin.Chapter2.LinearShadows.Single
