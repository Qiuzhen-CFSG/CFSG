module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.BaumannNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.Replacement
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual.Structure

/-!
# B.2.5–10: internal offenders and factorization

The family below is the literal family of images of maximum elementary
subgroups.  Its closure is proved separately from nonemptiness: the latter
requires that the Thompson subgroup acts nontrivially.  This is the point at
which the internal formulation in B.2 is connected to the stable-family
interfaces of B.1. Counting the elementary subgroup `B₀ C_V(B₀)` gives
the equal-score lift. Frattini’s argument in `C_G(V)`, followed by
Thompson heredity, gives the normalizer factorization.

For B.2.10(2), the quasisimple-or-order-three structure theorem gives a normal
Sylow two-subgroup of the centralizer and identifies `L*` with `F*(G*)`.
If `J(R)` centralizes `V`, Thompson and Baumann heredity give the first
alternative. Otherwise the relative stable family supplies a nontrivial
elementary two-subgroup of its generated normal subgroup, whose generalized
Fitting subgroup therefore has the same image `L*`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.2.5–10, printed pp.76–77.
-/

@[expose] public section
set_option linter.unusedSectionVars false
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection

namespace CFSG.Quasithin.ChapterB

universe u v

variable {G : Type u} [Group G] [Finite G]
  {H : Type v} [Group H] [Finite H]

/-- The image family used in B.2.5.  The nontriviality condition is part of
the source definition of `P_G`; it is intentionally not a nonemptiness claim.
-/
def maxOffenderImages (S _V : Subgroup G) (q : G →* H) : Set (Subgroup H) :=
  {E | ∃ A, A ∈ elementaryAbelianMaxSubgroups S ∧ A.map q = E ∧ E ≠ ⊥}

/-- The relative family in B.2.10.  We write the union of the `H`-conjugates
of the images of `A(R)`; surjectivity of the quotient map identifies this
with the union of the `G`-conjugates used in the source. -/
def relativeMaxOffenderImages (R _V : Subgroup G) (q : G →* H) : Set (Subgroup H) :=
  {E | ∃ A, A ∈ elementaryAbelianMaxSubgroups R ∧ ∃ h : H,
    (A.map q).map (MulAut.conj h).toMonoidHom = E ∧ E ≠ ⊥}

omit [Finite H] in
private theorem map_conj_mul_right (A : Subgroup H) (g h : H) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  exact A.conjBy_conjBy h g

omit [Finite H] in
private theorem map_conj_inv_cancel_right (A : Subgroup H) (g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_conj_mul_right, inv_mul_cancel]
  have h1 : (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by
    ext x
    simp
  rw [h1, Subgroup.map_id]

omit [Finite G] in
private theorem elementary_le {E A : Subgroup G} [IsElementaryAbelian 2 A]
    (h : E ≤ A) : IsElementaryAbelian 2 E := by
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact Subtype.ext (congrArg (fun a : A => (a : G))
      (mul_comm (⟨x, h x.property⟩ : A) ⟨y, h y.property⟩))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G)
      (h x.property))

omit [Finite G] [Finite H] in
private theorem card_kernel_mul_image (q : G →* H) (A : Subgroup G) :
    Nat.card (q.ker ⊓ A : Subgroup G) * Nat.card (A.map q) = Nat.card A := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ A) A bot_le inf_le_right
  simpa only [relIndex_bot_left, inf_relIndex_right, relIndex_ker] using h

omit [Finite G] in
private theorem maxFamily_map_conj
    (e : G ≃* G) (S A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    A.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups
      (S.map e.toMonoidHom) := by
  rcases hA with ⟨hAS, hAe, hAmax⟩
  refine ⟨Subgroup.map_mono hAS, hAe.map e.toMonoidHom, ?_⟩
  intro B hBS hBe
  let B' := B.map e.symm.toMonoidHom
  have hB'S : B' ≤ S := by
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom)
      e.injective).mp
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
    exact hBS
  have hcardB : Nat.card B' = Nat.card B := by
    exact Subgroup.card_map_of_injective e.symm.injective
  have hcardA : Nat.card (A.map e.toMonoidHom) = Nat.card A := by
    exact Subgroup.card_map_of_injective e.injective
  calc
    Nat.card B = Nat.card B' := hcardB.symm
    _ ≤ Nat.card A := hAmax B' hB'S (hBe.map e.symm.toMonoidHom)
    _ = Nat.card (A.map e.toMonoidHom) := hcardA.symm

omit [Finite G] [Finite H] in
private theorem image_conj_eq
    (q : G →* H) (A : Subgroup G) (x : G) :
    (A.map q).map (MulAut.conj (q x)).toMonoidHom =
      (A.map (MulAut.conj x).toMonoidHom).map q := by
  ext y
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨x * a * x⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    change q (x * a * x⁻¹) = (MulAut.conj (q x)) (q a)
    simp only [map_mul, map_inv, MulAut.conj_apply]
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨q a, ⟨a, ha, rfl⟩, ?_⟩
    change (MulAut.conj (q x)) (q a) = q (x * a * x⁻¹)
    simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem maxOffenderImages_best
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S) (E : Subgroup H)
    (hE : E ∈ maxOffenderImages S V q) :
    IsBestOffender (NormalElementaryQuotient.representation V q hq hker) E := by
  rcases hE with ⟨A, hA, rfl, hne⟩
  exact maxElementary_isBestOffender V q hq hker S A hVS hA hne

omit [Finite G] [Finite H] in
private theorem maxOffenderImages_conj
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (_hker : q.ker = centralizer (V : Set G))
    {E : Subgroup H} (hE : E ∈ maxOffenderImages (⊤ : Subgroup G) V q)
    (h : H) : E.map (MulAut.conj h).toMonoidHom ∈
      maxOffenderImages (⊤ : Subgroup G) V q := by
  rcases hq h with ⟨x, rfl⟩
  rcases hE with ⟨A, hA, rfl, hne⟩
  refine ⟨A.map (MulAut.conj x).toMonoidHom,
    ?_, (image_conj_eq q A x).symm, ?_⟩
  · simpa only [show (⊤ : Subgroup G).map (MulAut.conj x).toMonoidHom = ⊤ by
      rw [Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective]] using
      maxFamily_map_conj (MulAut.conj x) ⊤ A hA
  · intro hz
    apply hne
    apply (Subgroup.map_eq_bot_iff_of_injective (f :=
      (MulAut.conj (q x)).toMonoidHom) (map q A)
      (MulAut.conj (q x)).injective).mp
    exact hz

/-- B.2.8: the literal lift is `B₀ C_V(B₀)`, where `B₀` is the preimage in `A`. -/
public theorem lemma_B_2_8_construct
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (B : Subgroup H) (hB : IsElementaryTwo B)
    (hBE : EqualWeightLE
      (NormalElementaryQuotient.representation V q hq hker) B (A.map q)) :
    let B₀ := A ⊓ B.comap q
    (B₀ ⊔ (V ⊓ centralizer (B₀ : Set G))) ∈ elementaryAbelianMaxSubgroups S ∧
      (B₀ ⊔ (V ⊓ centralizer (B₀ : Set G))).map q = B := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let B₀ := A ⊓ B.comap q
  have hB₀A : B₀ ≤ A := inf_le_left
  let _ : IsElementaryAbelian 2 B₀ := elementary_le hB₀A
  have hmap : B₀.map q = B := by
    apply le_antisymm (map_le_iff_le_comap.mpr inf_le_right)
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBE.1 hb
    exact mem_map_of_mem q ⟨ha, hb⟩
  have hVA : V ⊓ centralizer (A : Set G) = V ⊓ A := by
    apply le_antisymm
    · have he : IsElementaryAbelian 2 (V ⊓ centralizer (A : Set G) : Subgroup G) :=
        elementary_le inf_le_left
      let _ := he
      have hs : IsElementaryAbelian 2 (A ⊔ (V ⊓ centralizer (A : Set G)) : Subgroup G) :=
        IsElementaryAbelian.sup_of_le_centralizer inf_le_right
      have hsup : A ⊔ (V ⊓ centralizer (A : Set G)) = A :=
        (eq_of_le_of_card_ge le_sup_left
          (hA.2.2 _ (sup_le hA.1 (inf_le_left.trans hVS)) hs)).symm
      exact le_inf inf_le_left (le_sup_right.trans_eq hsup)
    · exact inf_le_inf_left _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hVB : V ⊓ B₀ = V ⊓ A := by
    apply le_antisymm (inf_le_inf_left _ hB₀A)
    intro v hv
    refine ⟨hv.1, hv.2, ?_⟩
    have hk : v ∈ q.ker := by
      rw [hker]
      exact (le_centralizer_iff_isMulCommutative.mpr inferInstance :
        V ≤ centralizer (V : Set G)) hv.1
    change q v ∈ B
    rw [show q v = 1 from hk]
    exact B.one_mem
  let C := V ⊓ centralizer (B₀ : Set G)
  let _ : IsElementaryAbelian 2 C := elementary_le inf_le_left
  have he : IsElementaryAbelian 2 (B₀ ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hBC : B₀ ⊓ C = V ⊓ A := by
    rw [← hVB]
    apply le_antisymm (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    intro v hv
    exact ⟨hv.2, hv.1,
      (le_centralizer_iff_isMulCommutative.mpr inferInstance :
        B₀ ≤ centralizer (B₀ : Set G)) hv.2⟩
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B₀ C
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [hBC] at hc
  have hkb : q.ker ⊓ B₀ = q.ker ⊓ A := by
    apply le_antisymm (inf_le_inf_left _ hB₀A)
    intro a ha
    refine ⟨ha.1, ha.2, ?_⟩
    change q a ∈ B
    rw [show q a = 1 from ha.1]
    exact B.one_mem
  have hkA := card_kernel_mul_image q A
  have hkB := card_kernel_mul_image q B₀
  rw [hkb, hmap] at hkB
  have hCcard : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ B) := by
    rw [← hmap, ← Nat.card_congr
      (Representation.NormalElementaryQuotient.fixedSpaceEquiv V q hq hker B₀)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (B₀.map q))
  have hAcard : Nat.card (V ⊓ A : Subgroup G) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.map q)) := by
    rw [← hVA, ← Nat.card_congr
      (Representation.NormalElementaryQuotient.fixedSpaceEquiv V q hq hker A)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (A.map q))
  have hpow (D : Subgroup H) [IsElementaryAbelian 2 D] : Nat.card D = 2 ^ rank D := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_card_eq
    rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
  let _ : IsElementaryAbelian 2 B := hB.2
  let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hweight : Nat.card B * Nat.card C =
      Nat.card (A.map q) * Nat.card (V ⊓ A : Subgroup G) := by
    rw [hCcard, hAcard, hpow B, hpow (A.map q), ← pow_add, ← pow_add]
    exact congrArg (fun n : ℕ => 2 ^ n) hBE.2
  have hprod : Nat.card B₀ * Nat.card C =
      Nat.card (V ⊓ A : Subgroup G) * Nat.card A := by
    calc
      Nat.card B₀ * Nat.card C =
          (Nat.card (q.ker ⊓ A : Subgroup G) * Nat.card B) * Nat.card C := by
            rw [hkB]
      _ = Nat.card (q.ker ⊓ A : Subgroup G) *
          (Nat.card B * Nat.card C) := by ac_rfl
      _ = Nat.card (q.ker ⊓ A : Subgroup G) *
          (Nat.card (A.map q) * Nat.card (V ⊓ A : Subgroup G)) := by rw [hweight]
      _ = (Nat.card (q.ker ⊓ A : Subgroup G) * Nat.card (A.map q)) *
          Nat.card (V ⊓ A : Subgroup G) := by ac_rfl
      _ = Nat.card A * Nat.card (V ⊓ A : Subgroup G) := by rw [hkA]
      _ = Nat.card (V ⊓ A : Subgroup G) * Nat.card A := by ac_rfl
  have hcard : Nat.card (B₀ ⊔ C : Subgroup G) = Nat.card A := by
    rw [hc] at hprod
    have hv : 0 < Nat.card (V ⊓ A : Subgroup G) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hv
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod
  have hCker : C ≤ q.ker := by
    intro x hx
    rw [hker]
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance :
      V ≤ centralizer (V : Set G)) hx.1
  have hCmap : C.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact hCker
  refine ⟨?_, ?_⟩
  · have hDS : B₀ ⊔ C ≤ S := sup_le (hB₀A.trans hA.1) (inf_le_left.trans hVS)
    exact ⟨hDS, he, fun D hD hDe => by
      rw [hcard]
      exact hA.2.2 D hD hDe⟩
  · rw [Subgroup.map_sup, hCmap, sup_bot_eq]
    exact hmap

private theorem maxOffenderImages_lift
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (B : Subgroup H) (hB : IsElementaryTwo B)
    (hBE : EqualWeightLE
      (NormalElementaryQuotient.representation V q hq hker) B (A.map q)) :
    ∃ D ∈ elementaryAbelianMaxSubgroups S, D.map q = B :=
  ⟨_, lemma_B_2_8_construct V q hq hker S hVS A hA B hB hBE⟩

/-! The terminology in B.2.6 is kept internal to the quotient map. -/

def IsFFOffender (_V : Subgroup G) (q : G →* H) (S A : Subgroup G) : Prop :=
  A ∈ elementaryAbelianMaxSubgroups S ∧ A.map q ≠ ⊥

def IsStrongFFOffender (V : Subgroup G) (q : G →* H)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (S A : Subgroup G) : Prop :=
  IsFFOffender V q S A ∧ IsStrongOffender ρ (A.map q)

/-! The local part of B.2.7 is independent of conjugacy in the ambient
group.  It is useful for the relative family in B.2.10, where `R` need not
be normal in `G`. -/
public theorem lemma_B_2_7_local
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S)
    (hJ : ¬ elementaryAbelianMaxJ S ≤ q.ker) :
    IsFFModule (NormalElementaryQuotient.representation V q hq hker) ∧
      (∀ E ∈ maxOffenderImages S V q,
        IsBestOffender (NormalElementaryQuotient.representation V q hq hker) E) := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hP : (maxOffenderImages S V q).Nonempty := by
    by_contra hn
    have hempty : maxOffenderImages S V q = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hn
    have hle : elementaryAbelianMaxJ S ≤ q.ker := by
      unfold elementaryAbelianMaxJ
      refine sSup_le ?_
      intro A hA
      have hbot : A.map q = ⊥ := by
        by_contra hne
        have hm : A.map q ∈ maxOffenderImages S V q :=
          ⟨A, hA, rfl, hne⟩
        rw [hempty] at hm
        exact hm
      exact (Subgroup.map_eq_bot_iff A).mp hbot
    exact hJ hle
  refine ⟨Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
      V q hq hker S hVS hJ, ?_⟩
  intro E hE
  exact maxOffenderImages_best V q hq hker S hVS E hE

/-- The two closure clauses of B.2.5.  This theorem deliberately has no
nonemptiness conclusion, since the family can be empty when `J(S)` centralizes
the module. -/
public theorem lemma_B_2_5_closure
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) :
    (∀ E ∈ maxOffenderImages (⊤ : Subgroup G) V q, ∀ h : H,
      E.map (MulAut.conj h).toMonoidHom ∈
        maxOffenderImages (⊤ : Subgroup G) V q) ∧
    (∀ E ∈ maxOffenderImages (⊤ : Subgroup G) V q, ∀ B,
      IsElementaryTwo B → EqualWeightLE
        (NormalElementaryQuotient.representation V q hq hker) B E →
      B ∈ maxOffenderImages (⊤ : Subgroup G) V q) := by
  refine ⟨fun E hE h => maxOffenderImages_conj V q hq hker hE h, ?_⟩
  intro E hE B hB hBE
  rcases hE with ⟨A, hA, rfl, hne⟩
  obtain ⟨C, hC, hCeq⟩ := maxOffenderImages_lift V q hq hker (⊤ : Subgroup G)
    le_top A hA B hB hBE
  exact ⟨C, hC, hCeq, hB.1⟩

public theorem lemma_B_2_7_second
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ q.ker) :
    IsFFModule (NormalElementaryQuotient.representation V q hq hker) ∧
      IsStable (NormalElementaryQuotient.representation V q hq hker)
        (maxOffenderImages (⊤ : Subgroup G) V q) := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hP : (maxOffenderImages (⊤ : Subgroup G) V q).Nonempty := by
    by_contra hn
    have hempty : maxOffenderImages (⊤ : Subgroup G) V q = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hn
    have hle : elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ q.ker := by
      unfold elementaryAbelianMaxJ
      refine sSup_le ?_
      intro A hA
      have hbot : A.map q = ⊥ := by
        by_contra hne
        have hm : A.map q ∈ maxOffenderImages (⊤ : Subgroup G) V q :=
          ⟨A, hA, rfl, hne⟩
        rw [hempty] at hm
        exact hm
      exact (Subgroup.map_eq_bot_iff A).mp hbot
    exact hJ hle
  have hclosure := lemma_B_2_5_closure V q hq hker
  refine ⟨Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
      V q hq hker (⊤ : Subgroup G) le_top hJ, ?_⟩
  refine ⟨hP, ?_, hclosure.1, hclosure.2⟩
  intro A hA
  exact maxOffenderImages_best V q hq hker (⊤ : Subgroup G) le_top A hA

/-! The generated subgroup of the internal family is contained in the usual
offender subgroup of the faithful quotient.  This is the `J_P(G*) ≤ J(G*,V)`
part of B.2.7. -/
public theorem lemma_B_2_7_second_generated
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) :
    generatedBy (maxOffenderImages (⊤ : Subgroup G) V q) (⊤ : Subgroup H) ≤
      offenderSubgroup (NormalElementaryQuotient.representation V q hq hker) := by
  unfold generatedBy offenderSubgroup
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact le_iSup_of_le E (le_iSup_of_le
    ⟨maxOffenderImages_best V q hq hker (⊤ : Subgroup G) le_top E hE.1,
      le_top⟩ le_rfl)

/-! The replacement observation used in B.2.8, made explicit with the
equal-weight relation from the definition of stability. -/
public theorem lemma_B_2_8_replacement
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (B : Subgroup H) (hB : IsElementaryTwo B)
    (hBA : EqualWeightLE
      (NormalElementaryQuotient.representation V q hq hker) B (A.map q)) :
    ∃ D ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G), D.map q = B := by
  exact maxOffenderImages_lift V q hq hker (⊤ : Subgroup G) le_top A hA B hB hBA

/-! B.2.9: weak FF-offenders below an FF-offender lift through the
replacement subgroup.  The two displayed hypotheses are the two source
cases (an FF-star offender, and the ratio formulation). -/
public theorem lemma_B_2_9_lift
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (hAne : A.map q ≠ ⊥)
    (hAweak : ¬ IsStrongOffender
      (NormalElementaryQuotient.representation V q hq hker) (A.map q)) :
    (∀ B : Subgroup H, IsOffender
        (NormalElementaryQuotient.representation V q hq hker) B →
        B ≤ A.map q →
        ∃ D ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G), D.map q = B) ∧
    (∀ B : Subgroup H, IsElementaryTwo B → B ≤ A.map q →
        actionRatio (NormalElementaryQuotient.representation V q hq hker) B ≤ 1 →
        ∃ D ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G), D.map q = B) := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hbest : IsBestOffender ρ (A.map q) :=
    maxOffenderImages_best V q hq hker (⊤ : Subgroup G) le_top (A.map q)
      ⟨A, hA, rfl, hAne⟩
  have hdim : weight ρ (A.map q) = Module.finrank (ZMod 2) (Additive V) := by
    have heq : fixedCodim ρ (A.map q) = rank (A.map q) := by
      apply le_antisymm (hbest.isOffender ρ).2
      apply Nat.le_of_not_gt
      intro hlt
      exact hAweak ⟨hbest.1, hlt⟩
    have hsum := fixedCodim_add_finrank ρ (A.map q)
    unfold weight
    omega
  have lift_of_offender : ∀ B : Subgroup H, IsOffender ρ B → B ≤ A.map q →
      ∃ D ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G), D.map q = B := by
    intro B hB hBA
    have hlow : Module.finrank (ZMod 2) (Additive V) ≤ weight ρ B :=
      (fixedCodim_le_rank_iff ρ B).1 hB.2
    have hupper : weight ρ B ≤ weight ρ (A.map q) := hbest.2 B hBA
    have heq : weight ρ B = weight ρ (A.map q) := by
      apply le_antisymm hupper
      rw [hdim]
      exact hlow
    exact maxOffenderImages_lift V q hq hker (⊤ : Subgroup G) le_top A hA B hB.1
      ⟨hBA, heq⟩
  refine ⟨lift_of_offender, ?_⟩
  intro B hB hBA hratio
  exact lift_of_offender B ⟨hB, (actionRatio_le_one_iff ρ hB).mp hratio⟩ hBA

/-! The relative version needed in B.2.10.  The local maximum-elementary
family is stable under replacement by `lemma_B_2_8_replacement`; adjoining all
quotient conjugates makes it stable under the ambient group. -/
public theorem lemma_B_2_10_relative
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    IsFFModule (NormalElementaryQuotient.representation V q hq hker) ∧
      IsStable (NormalElementaryQuotient.representation V q hq hker)
        (relativeMaxOffenderImages R V q) ∧
      generatedBy (relativeMaxOffenderImages R V q) (⊤ : Subgroup H) ≤
        offenderSubgroup (NormalElementaryQuotient.representation V q hq hker) := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hlocal := lemma_B_2_7_local V q hq hker R hVR hJ
  have hnonempty : (relativeMaxOffenderImages R V q).Nonempty := by
    obtain ⟨A, hA, hne⟩ : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
      by_contra hn
      apply hJ
      unfold elementaryAbelianMaxJ
      refine sSup_le ?_
      intro A hA
      exact (Subgroup.map_eq_bot_iff A).mp (by
        by_contra hne
        exact hn ⟨A, hA, hne⟩)
    exact ⟨A.map q, ⟨A, hA, 1, by
      have h1 : (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [h1, Subgroup.map_id], hne⟩⟩
  have hbest : ∀ E ∈ relativeMaxOffenderImages R V q, IsBestOffender ρ E := by
    intro E hE
    rcases hE with ⟨A, hA, h, rfl, hne⟩
    have hAq : IsBestOffender ρ (A.map q) :=
      hlocal.2 (A.map q) ⟨A, hA, rfl, fun hz => hne (by rw [hz, Subgroup.map_bot])⟩
    exact hAq.map_conj ρ h
  have hconj : ∀ E ∈ relativeMaxOffenderImages R V q, ∀ g : H,
      E.map (MulAut.conj g).toMonoidHom ∈ relativeMaxOffenderImages R V q := by
    intro E hE g
    rcases hE with ⟨A, hA, h, rfl, hne⟩
    refine ⟨A, hA, g * h, ?_, ?_⟩
    · rw [map_conj_mul_right]
    · intro hz
      apply hne
      apply (Subgroup.map_eq_bot_iff_of_injective
        (f := (MulAut.conj g).toMonoidHom)
        ((A.map q).map (MulAut.conj h).toMonoidHom)
        (MulAut.conj g).injective).mp
      exact hz
  have hreplace : ∀ E ∈ relativeMaxOffenderImages R V q, ∀ B,
      IsElementaryTwo B → EqualWeightLE ρ B E →
      B ∈ relativeMaxOffenderImages R V q := by
    intro E hE B hB hBE
    rcases hE with ⟨A, hA, h, rfl, hne⟩
    let B' := B.map (MulAut.conj h⁻¹).toMonoidHom
    let _ : IsElementaryAbelian 2 B := hB.2
    have hB' : IsElementaryTwo B' := by
      refine ⟨?_, IsElementaryAbelian.map (MulAut.conj h⁻¹).toMonoidHom⟩
      intro hz
      apply hB.1
      apply (Subgroup.map_eq_bot_iff_of_injective
        (f := (MulAut.conj h⁻¹).toMonoidHom) B (MulAut.conj h⁻¹).injective).mp
      exact hz
    have hBE' : EqualWeightLE ρ B' (A.map q) := by
      have hh := hBE.map_conj ρ h⁻¹
      rw [map_conj_inv_cancel_right] at hh
      exact hh
    obtain ⟨D, hD, hDmap⟩ := maxOffenderImages_lift V q hq hker R hVR A hA B' hB' hBE'
    refine ⟨D, hD, h, ?_, ?_⟩
    · have hh := congrArg
        (fun X : Subgroup H => X.map (MulAut.conj h).toMonoidHom) hDmap
      have hc := map_conj_inv_cancel_right B h⁻¹
      simp only [inv_inv] at hc
      simpa only [B', hc] using hh
    · exact hB.1
  refine ⟨hlocal.1, ⟨hnonempty, hbest, hconj, hreplace⟩, ?_⟩
  unfold generatedBy offenderSubgroup
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact le_iSup_of_le E (le_iSup_of_le
    ⟨hbest E hE.1, le_top⟩ le_rfl)

/-! The centralizing branch of B.2.10.  The proof uses only the literal
source hypotheses `O₂(G) = C_R(V)` and `J(R) ≤ C_R(V)`; the Sylow
containment is retained as the explicit `hQR` premise. -/
public theorem lemma_B_2_10_centralizing
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (hQR : pCore 2 G ≤ R)
    (hcore : pCore 2 G = R ⊓ centralizer (V : Set G))
    (hJ : thompsonJ R 0 ≤ centralizer (V : Set G)) :
    thompsonJ R 0 = thompsonJ (pCore 2 G) 0 ∧
      baumann R = baumann (pCore 2 G) ∧
      (thompsonJ R 0).Normal ∧ (baumann R).Normal := by
  have hJR : elementaryAbelianMaxJ R ≤ pCore 2 G := by
    have hJ' : elementaryAbelianMaxJ R ≤ centralizer (V : Set G) := by
      simpa only [thompsonJ_zero] using hJ
    have hJRleR : elementaryAbelianMaxJ R ≤ R := by
      simpa only [thompsonJ_zero] using thompsonJ_le R 0
    rw [hcore]
    exact le_inf hJRleR hJ'
  have horders : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder (pCore 2 G) := by
    apply le_antisymm
    · exact (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R (pCore 2 G) hJR).1
    · exact (elementaryAbelianMaxOrder_le_and_j_le_of_eq (pCore 2 G) R hQR).1
  have hJle : elementaryAbelianMaxJ R ≤ elementaryAbelianMaxJ (pCore 2 G) :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R (pCore 2 G) hJR).2 horders
  have hJge : elementaryAbelianMaxJ (pCore 2 G) ≤ elementaryAbelianMaxJ R :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq (pCore 2 G) R hQR).2 horders.symm
  have hJeq : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 G) :=
    le_antisymm hJle hJge
  have hValpha : V ≤ thompsonAlpha R := by
    rw [thompsonAlpha]
    apply elementary_centralizer_maxJ_le_omegaCenter R V hVR
    rw [← thompsonJ_zero]
    exact le_centralizer_iff.mp hJ
  have hBR : baumann R ≤ pCore 2 G := by
    rw [baumann]
    rw [hcore]
    exact le_inf inf_le_left (inf_le_right.trans (centralizer_le hValpha))
  have hBeq : baumann R = baumann (pCore 2 G) := by
    have htmp := baumann_eq_of_intermediate R (pCore 2 G) hBR hQR
    simpa [baumann, thompsonAlpha, hJeq] using htmp.symm
  have hJQnormal : (elementaryAbelianMaxJ (pCore 2 G)).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQnorm : (pCore 2 G).map (MulAut.conj g).toMonoidHom = pCore 2 G := by
      apply (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      rw [Subgroup.normalizer_eq_top]
      trivial
    calc
      (elementaryAbelianMaxJ (pCore 2 G)).map
          (MulAut.conj g).toMonoidHom =
          elementaryAbelianMaxJ ((pCore 2 G).map (MulAut.conj g).toMonoidHom) :=
        (elementaryAbelianMaxJ_map_equiv (MulAut.conj g) (pCore 2 G)).symm
      _ = elementaryAbelianMaxJ (pCore 2 G) := by rw [hQnorm]
  have hJnormal : (thompsonJ R 0).Normal := by
    simpa only [thompsonJ_zero, hJeq] using hJQnormal
  have hBnormal : (baumann R).Normal := by
    have hBQnormal : (baumann (pCore 2 G)).Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      exact (show (⊤ : Subgroup G) ≤ normalizer (pCore 2 G : Set G) by
        rw [Subgroup.normalizer_eq_top]).trans (normalizer_le_normalizer_baumann _)
    rw [hBeq]
    exact hBQnormal
  exact ⟨by rw [thompsonJ_zero, hJeq, ← thompsonJ_zero], hBeq, hJnormal, hBnormal⟩

end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

public theorem maxOffenderImages_generated (S V : Subgroup G) (q : G →* H) :
    (elementaryAbelianMaxJ S).map q = generatedBy (maxOffenderImages S V q) ⊤ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    apply Subgroup.map_le_iff_le_comap.mp
    by_cases hb : A.map q = ⊥
    · rw [hb]
      exact bot_le
    · exact le_iSup_of_le (A.map q) (le_iSup_of_le ⟨⟨A, hA, rfl, hb⟩, le_top⟩ le_rfl)
  · apply iSup_le
    intro E
    apply iSup_le
    rintro ⟨⟨A, hA, rfl, _⟩, _⟩
    exact Subgroup.map_mono (le_sSup hA)

private theorem maxJ_eq_of_intermediate (S R : Subgroup G)
    (hJR : elementaryAbelianMaxJ S ≤ R) (hRS : R ≤ S) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ S := by
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq R S hRS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S R hJR
  have horder : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder S :=
    le_antisymm hsmall.1 hlarge.1
  exact le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)

public theorem thompson_normalizer_factorization (V : Subgroup G) [V.Normal]
    (T : Sylow 2 G)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ∀ g : G, ∃ n ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G),
      ∃ c ∈ centralizer (V : Set G), n * c = g := by
  let C := centralizer (V : Set G)
  let S := (T : Subgroup G) ⊓ C
  have hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ S :=
    le_inf (sSup_le fun _ hA => hA.1) hJ
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hJeq : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    maxJ_eq_of_intermediate (T : Subgroup G) S hJS hST
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal C
  have hmap : (P : Subgroup C).map C.subtype = S := by
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hFr : normalizer (S : Set G) ⊔ C = ⊤ := by
    simpa only [hmap] using P.normalizer_sup_eq_top (G := G)
  have hnorm : normalizer (S : Set G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← hJeq]
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    change S.map (MulAut.conj g).toMonoidHom = S at hg
    change (elementaryAbelianMaxJ S).map (MulAut.conj g).toMonoidHom = elementaryAbelianMaxJ S
    rw [← elementaryAbelianMaxJ_map_equiv, hg]
  have hprod : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ⊔ C = ⊤ :=
    top_unique (by rw [← hFr]; exact sup_le_sup_right hnorm C)
  intro g
  exact Subgroup.mem_sup_of_normal_right.mp (hprod ▸ (show g ∈ (⊤ : Subgroup G) from trivial))

public theorem lemma_B_2_7
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) (T : Sylow 2 G) :
    (elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ centralizer (V : Set G) ∧
      ∀ g : G, ∃ n ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G),
        ∃ c ∈ centralizer (V : Set G), n * c = g) ∨
    (¬ elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ centralizer (V : Set G) ∧
      IsFFModule (NormalElementaryQuotient.representation V q hq hker) ∧
      IsStable (NormalElementaryQuotient.representation V q hq hker)
        (maxOffenderImages (⊤ : Subgroup G) V q) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q =
        generatedBy (maxOffenderImages (⊤ : Subgroup G) V q) ⊤ ∧
      generatedBy (maxOffenderImages (⊤ : Subgroup G) V q) ⊤ ≤
        offenderSubgroup (NormalElementaryQuotient.representation V q hq hker)) := by
  by_cases hJ : elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ centralizer (V : Set G)
  · exact Or.inl ⟨hJ, thompson_normalizer_factorization V T
      ((elementaryAbelianMaxJ_sylow_le_top T).trans hJ)⟩
  · have hn : ¬ elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ q.ker := by rwa [hker]
    obtain ⟨hff, hstable⟩ := lemma_B_2_7_second V q hq hker hn
    exact Or.inr ⟨hJ, hff, hstable, maxOffenderImages_generated ⊤ V q,
      lemma_B_2_7_second_generated V q hq hker⟩

public theorem lemma_B_2_7_quadratic
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S) (hJ : ¬ elementaryAbelianMaxJ S ≤ q.ker) :
    quadraticRatio (NormalElementaryQuotient.representation V q hq hker) ≤ 1 :=
  (isFFModule_iff_quadraticRatio_le_one _).mp
    (lemma_B_2_7_local V q hq hker S hVS hJ).1

public theorem lemma_B_2_10_one
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (T : Sylow 2 G) (hQR : pCore 2 G ≤ R) (_hRT : R ≤ T)
    (hcore : pCore 2 G = R ⊓ centralizer (V : Set G)) :
    (thompsonJ R 0 = thompsonJ (pCore 2 G) 0 ∧
      baumann R = baumann (pCore 2 G) ∧
      (thompsonJ R 0).Normal ∧ (baumann R).Normal) ∨
    (IsStable (NormalElementaryQuotient.representation V q hq hker)
        (relativeMaxOffenderImages R V q) ∧
      generatedBy (relativeMaxOffenderImages R V q) ⊤ ≤
        offenderSubgroup (NormalElementaryQuotient.representation V q hq hker)) := by
  have hVR : V ≤ R := (show V ≤ pCore 2 G from le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  by_cases hJ : elementaryAbelianMaxJ R ≤ q.ker
  · apply Or.inl
    apply lemma_B_2_10_centralizing V R hVR hQR hcore
    simpa only [thompsonJ_zero, hker] using hJ
  · exact Or.inr (lemma_B_2_10_relative V R hVR q hq hker hJ).2

end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

public theorem IsFFOffender.isBestOffender
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    {S A : Subgroup G} (hVS : V ≤ S) (hA : IsFFOffender V q S A) :
    IsBestOffender (NormalElementaryQuotient.representation V q hq hker) (A.map q) :=
  CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    V q hq hker S A hVS hA.1 hA.2

public theorem lemma_B_2_9_construct
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S) (A : Subgroup G) (hA : IsFFOffender V q S A)
    (hweak : ¬ IsStrongOffender (NormalElementaryQuotient.representation V q hq hker) (A.map q))
    (B : Subgroup H) (hB : IsOffender (NormalElementaryQuotient.representation V q hq hker) B)
    (hBA : B ≤ A.map q) :
    let B₀ := A ⊓ B.comap q
    IsFFOffender V q S (B₀ ⊔ (V ⊓ centralizer (B₀ : Set G))) ∧
      (B₀ ⊔ (V ⊓ centralizer (B₀ : Set G))).map q = B := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hbest := hA.isBestOffender V q hq hker hVS
  have hdim : weight ρ (A.map q) = Module.finrank (ZMod 2) (Additive V) := by
    have hle := (hbest.isOffender ρ).2
    have hge : rank (A.map q) ≤ fixedCodim ρ (A.map q) := by
      by_contra! hh
      exact hweak ⟨hbest.1, hh⟩
    have heq : fixedCodim ρ (A.map q) = rank (A.map q) := le_antisymm hle hge
    have hsum := fixedCodim_add_finrank ρ (A.map q)
    unfold weight
    omega
  have hequal : EqualWeightLE ρ B (A.map q) := by
    refine ⟨hBA, le_antisymm (hbest.2 B hBA) ?_⟩
    rw [hdim]
    exact (fixedCodim_le_rank_iff ρ B).mp hB.2
  obtain ⟨hD, hDmap⟩ := lemma_B_2_8_construct V q hq hker S hVS A hA.1 B hB.1 hequal
  exact ⟨⟨hD, by rw [hDmap]; exact hB.1.1⟩, hDmap⟩

/-- B.2.5 includes membership in the best-offender family; closure does not imply nonemptiness. -/
public theorem lemma_B_2_5
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) :
    (∀ E ∈ maxOffenderImages (⊤ : Subgroup G) V q,
      IsBestOffender (NormalElementaryQuotient.representation V q hq hker) E) ∧
    (∀ E ∈ maxOffenderImages (⊤ : Subgroup G) V q, ∀ h : H,
      E.map (MulAut.conj h).toMonoidHom ∈ maxOffenderImages (⊤ : Subgroup G) V q) ∧
    (∀ E ∈ maxOffenderImages (⊤ : Subgroup G) V q, ∀ B, IsElementaryTwo B →
      EqualWeightLE (NormalElementaryQuotient.representation V q hq hker) B E →
      B ∈ maxOffenderImages (⊤ : Subgroup G) V q) := by
  refine ⟨?_, lemma_B_2_5_closure V q hq hker⟩
  rintro E ⟨A, hA, rfl, hne⟩
  exact (show IsFFOffender V q ⊤ A from ⟨hA, hne⟩).isBestOffender V q hq hker le_top

/-- B.2.9 with only the source nontriviality, inclusion and ratio premises. -/
public theorem lemma_B_2_9
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S) (A : Subgroup G) (hA : IsFFOffender V q S A)
    (hweak : ¬ IsStrongOffender (NormalElementaryQuotient.representation V q hq hker) (A.map q)) :
    (∀ B, IsBestOffender (NormalElementaryQuotient.representation V q hq hker) B →
      B ≤ A.map q → ∃ D, IsFFOffender V q S D ∧ D.map q = B) ∧
    (∀ B, B ≠ ⊥ → B ≤ A.map q →
      actionRatio (NormalElementaryQuotient.representation V q hq hker) B ≤ 1 →
      ∃ D, IsFFOffender V q S D ∧ D.map q = B) := by
  let ρ := NormalElementaryQuotient.representation V q hq hker
  constructor
  · intro B hB hBA
    exact ⟨_, lemma_B_2_9_construct V q hq hker S hVS A hA hweak B (hB.isOffender ρ) hBA⟩
  · intro B hB hBA hr
    have hE := (hA.isBestOffender V q hq hker hVS).1.of_le hBA hB
    have hoff : IsOffender ρ B := ⟨hE, (actionRatio_le_one_iff ρ hE).mp hr⟩
    exact ⟨_, lemma_B_2_9_construct V q hq hker S hVS A hA hweak B hoff hBA⟩

/-- The literal relative family supplies the normal nontrivial two-generated
subgroup required in the generalized-Fitting step of B.2.10(2). -/
public theorem relativeMaxOffenderImages_generated_facts
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    (generatedBy (relativeMaxOffenderImages R V q) ⊤).Normal ∧
      generatedBy (relativeMaxOffenderImages R V q) ⊤ ≠ ⊥ ∧
      (∀ E ∈ relativeMaxOffenderImages R V q, IsElementaryTwo E) := by
  have hs := (lemma_B_2_10_relative V R hVR q hq hker hJ).2.1
  refine ⟨hs.generatedBy_normal _, ?_, fun E hE => (hs.2.1 E hE).1⟩
  obtain ⟨E, hE⟩ := hs.1
  intro hz
  have hle : E ≤ generatedBy (relativeMaxOffenderImages R V q) ⊤ :=
    le_iSup_of_le E (le_iSup_of_le ⟨hE, le_top⟩ le_rfl)
  exact (hs.2.1 E hE).1.1 (le_bot_iff.mp (hz ▸ hle))

open Theory.GroupTheory in
/-- B.2.10(2), under the literal factorization `G = LT`. The normal Sylow
subgroup witnesses that `C_G(V)` is two-closed, with its actual ambient image
retained. The final alternative uses the generalized Fitting subgroup of the
subgroup generated by the relative offender family, mapped into `G*`. -/
public theorem lemma_B_2_10_two
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (T : Sylow 2 G) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T)
    (hcore : pCore 2 H = ⊥) (L : Subgroup G)
    (hL : (L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    (∃ P : Sylow 2 (centralizer (V : Set G)),
      (P : Subgroup (centralizer (V : Set G))).Normal ∧
      (P : Subgroup (centralizer (V : Set G))).map
        (centralizer (V : Set G)).subtype = pCore 2 G) ∧
    pCore 2 G = R ⊓ centralizer (V : Set G) ∧
    L.map q = generalizedFitting H ∧
    (baumann R = baumann (pCore 2 G) ∨
      let N := generatedBy (relativeMaxOffenderImages R V q) ⊤
      L.map q = (generalizedFitting N).map N.subtype) := by
  obtain ⟨hT, hP, hF, hshape⟩ :=
    internalModule_residual_structure V q hq hker hcore T L hL hcomm hprod
  have hcoreG : pCore 2 G = R ⊓ centralizer (V : Set G) :=
    le_antisymm (le_inf hQR (hT.le.trans inf_le_right))
      ((inf_le_inf_right _ hRT).trans hT.ge)
  refine ⟨hP, hcoreG, hF, ?_⟩
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  by_cases hJ : elementaryAbelianMaxJ R ≤ q.ker
  · exact Or.inl (lemma_B_2_10_centralizing V R hVR hQR hcoreG
      (by simpa only [thompsonJ_zero, hker] using hJ)).2.1
  · have hs := (lemma_B_2_10_relative V R hVR q hq hker hJ).2.1
    let N := generatedBy (relativeMaxOffenderImages R V q) ⊤
    let : N.Normal := hs.generatedBy_normal _
    obtain ⟨A, hA⟩ := hs.1
    have hAe := (hs.2.1 A hA).1
    let : IsElementaryAbelian 2 A := hAe.2
    have hAN : A ≤ N :=
      le_iSup_of_le A (le_iSup_of_le ⟨hA, le_top⟩ le_rfl)
    exact Or.inr ((generalizedFitting_normal_eq_of_quasisimple_or_three hcore
      (hF ▸ hshape) N A (IsElementaryAbelian.isPGroup 2 A) hAe.1 hAN).trans
        hF.symm).symm

end CFSG.Quasithin.ChapterB
