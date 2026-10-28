module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# The A₅-block omega-center quotient

This is the conditional intrinsic calculation used in E.6.7. The full natural
module lift, the decomposition O₂(L) = U(L) Z(L), and U(L) ∩ Z(L) = 1 are
kept explicit. These are the C.1.13(c) inputs, beyond the defining action on
U(L)/C_U(L). Faithfulness and the order of the Sylow-fixed natural vectors
are the two explicit concrete-model inputs.

Since U(L) lies in every Sylow two-subgroup S, an element of Ω₁(Z(S)) acts
trivially on U(L). Faithfulness places it in O₂(L). Write it as u c with
u in U(L) and c central. Then u is a Sylow-fixed involution and c remains
in the central omega kernel. Thus inclusion identifies U(L) ∩ Ω₁(Z(S))
with Ω₁(Z(S))/(Ω₁(Z(S)) ∩ Z(L)), and equivariance identifies its elements
with the fixed natural vectors. The possible central extension is retained;
no splitting of L or triviality of Z(L) is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.13(c), printed pp.124–125 / PDF pp.135–136,
and E.6.7, printed p.246 / PDF p.257. This helper does not discharge its
explicit earlier-source or concrete-model inputs.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.AlternatingLocal
open Subgroup Theory.GroupTheory ChapterC

variable {L : Type*} [Group L]

private theorem a5_omega_le_core
    (eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (eU : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
    (he : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (eU (blockConjugate L l u)) =
        BinaryPermutation.naturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 L) l)).val
          (Multiplicative.toAdd (eU u)))
    (hfaith : ∀ a : alternatingGroup (Fin 5),
      (∀ v : BinaryPermutation.natural (Fin 5),
        BinaryPermutation.naturalRepresentation (Fin 5) a.val v = v) → a = 1)
    (S : Sylow 2 L) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ≤ pCore 2 L := by
  have hUS : blockU L ≤ (S : Subgroup L) :=
    blockU_le_core.trans (pCore_isPGroup.le_sylow_of_normal S)
  intro z hz
  have hzc := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2
  have hq : eQ (QuotientGroup.mk' (pCore 2 L) z) = 1 := by
    apply hfaith
    intro v
    obtain ⟨u, hu⟩ := eU.surjective (Multiplicative.ofAdd v)
    have hu' : Multiplicative.toAdd (eU u) = v := hu
    rw [← hu', ← he]
    congr 2
    apply Subtype.ext
    change z * (u : L) * z⁻¹ = (u : L)
    rw [← hzc u (hUS u.property), mul_inv_cancel_right]
  exact (QuotientGroup.eq_one_iff z).mp
    (eQ.injective (hq.trans eQ.map_one.symm))

private theorem a5_omega_quotient_card_eq_intersection
    (h : IsAlternatingBlock L 5) (S : Sylow 2 L)
    (hcore : pCore 2 L = blockU L ⊔ center L)
    (hdis : blockU L ⊓ center L = ⊥)
    (hZ : Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ≤ pCore 2 L) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
    Nat.card (Z ⧸ (center L).subgroupOf Z) = Nat.card (blockU L ⊓ Z : Subgroup L) := by
  classical
  let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
  let W := blockU L ⊓ Z
  let C := (center L).subgroupOf Z
  let f : W →* Z ⧸ C := (QuotientGroup.mk' C).comp (inclusion inf_le_right)
  have hUS : blockU L ≤ (S : Subgroup L) :=
    blockU_le_core.trans (pCore_isPGroup.le_sylow_of_normal S)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro w hw
    have hwc' : (inclusion (show W ≤ Z from inf_le_right) w) ∈ C :=
      (QuotientGroup.eq_one_iff _).mp hw
    have hwc : (w : L) ∈ center L := hwc'
    have hwu : (w : L) ∈ blockU L ⊓ center L := ⟨w.property.1, hwc⟩
    rw [hdis, mem_bot] at hwu
    exact Subtype.ext hwu
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective C q
    have hzc := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp z.property |>.2.2
    obtain ⟨u, hu, c, hc, huc⟩ := mem_sup_of_normal_right.mp (hcore ▸ hZ z.property)
    have huZ : u ∈ Z := by
      apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      let : IsElementaryAbelian 2 (blockU L) := h.2.1.elementary
      refine ⟨hUS hu, elemPow_eq_one_of_isElementaryAbelian u hu, ?_⟩
      intro s hs
      apply mul_right_cancel (b := c)
      calc
        s * u * c = s * (u * c) := mul_assoc _ _ _
        _ = s * (z : L) := congrArg (s * ·) huc
        _ = (z : L) * s := hzc s hs
        _ = (u * c) * s := congrArg (· * s) huc.symm
        _ = u * (s * c) := by rw [mul_assoc, ← mem_center_iff.mp hc s]
        _ = (u * s) * c := (mul_assoc _ _ _).symm
    have hcZ : c ∈ Z := by
      have hz : u * c ∈ Z := huc ▸ z.property
      exact (Z.mul_mem_cancel_left huZ).mp hz
    refine ⟨⟨u, hu, huZ⟩, ?_⟩
    have heq : (⟨u, huZ⟩ : Z) * ⟨c, hcZ⟩ = z := Subtype.ext huc
    change QuotientGroup.mk' C ⟨u, huZ⟩ = QuotientGroup.mk' C z
    rw [← heq, map_mul]
    have hcq : QuotientGroup.mk' C ⟨c, hcZ⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    rw [hcq, mul_one]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩)).symm

private theorem a5_mem_omega_iff_fixed
    (h : IsAlternatingBlock L 5)
    (eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (eU : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
    (he : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (eU (blockConjugate L l u)) =
        BinaryPermutation.naturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 L) l)).val
          (Multiplicative.toAdd (eU u)))
    (S : Sylow 2 L) (u : blockU L) :
    let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    (u : L) ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ↔
      ∀ a : alternatingGroup (Fin 5), a ∈ (S : Subgroup L).map q →
        BinaryPermutation.naturalRepresentation (Fin 5) a.val
          (Multiplicative.toAdd (eU u)) = Multiplicative.toAdd (eU u) := by
  dsimp only
  constructor
  · intro hu a ha
    obtain ⟨s, hs, rfl⟩ := ha
    change BinaryPermutation.naturalRepresentation (Fin 5)
      (eQ (QuotientGroup.mk' (pCore 2 L) s)).val
      (Multiplicative.toAdd (eU u)) = Multiplicative.toAdd (eU u)
    rw [← he]
    have hsu := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hu |>.2.2 s hs
    have hc : blockConjugate L s u = u := by
      apply Subtype.ext
      change s * (u : L) * s⁻¹ = (u : L)
      rw [hsu, mul_inv_cancel_right]
    rw [hc]
  · intro hu
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    let : IsElementaryAbelian 2 (blockU L) := h.2.1.elementary
    refine ⟨pCore_isPGroup.le_sylow_of_normal S (blockU_le_core u.property),
      elemPow_eq_one_of_isElementaryAbelian (u : L) u.property, ?_⟩
    intro s hs
    have hc : blockConjugate L s u = u := eU.injective
      ((he s u).trans (hu _ ⟨s, hs, rfl⟩))
    have hval := congrArg Subtype.val hc
    change s * (u : L) * s⁻¹ = (u : L) at hval
    exact (mul_inv_eq_iff_eq_mul).mp hval

/-- The intrinsic A₅-block omega-center quotient has order two, conditional
on the full natural lift and core decomposition from C.1.13(c), disjointness
of U(L) from the center, and the two concrete natural-action facts. -/
theorem a5_omega_center_quotient_card_of_natural_lift [Finite L]
    (h : IsAlternatingBlock L 5)
    (eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (eU : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
    (he : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (eU (blockConjugate L l u)) =
        BinaryPermutation.naturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 L) l)).val
          (Multiplicative.toAdd (eU u)))
    (hcore : pCore 2 L = blockU L ⊔ center L)
    (hdis : blockU L ⊓ center L = ⊥)
    (hfaith : ∀ a : alternatingGroup (Fin 5),
      (∀ v : BinaryPermutation.natural (Fin 5),
        BinaryPermutation.naturalRepresentation (Fin 5) a.val v = v) → a = 1)
    (hfixed : ∀ P : Sylow 2 (alternatingGroup (Fin 5)),
      Nat.card {v : BinaryPermutation.natural (Fin 5) //
        ∀ a : alternatingGroup (Fin 5), a ∈ (P : Subgroup _) →
          BinaryPermutation.naturalRepresentation (Fin 5) a.val v = v} = 2)
    (S : Sylow 2 L) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
    Nat.card (Z ⧸ (center L).subgroupOf Z) = 2 := by
  classical
  let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  have hP : (P : Subgroup (alternatingGroup (Fin 5))) = (S : Subgroup L).map q :=
    Sylow.coe_mapSurjective _ _
  let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
  let W := blockU L ⊓ Z
  let F := {v : BinaryPermutation.natural (Fin 5) //
    ∀ a : alternatingGroup (Fin 5), a ∈ (P : Subgroup _) →
      BinaryPermutation.naturalRepresentation (Fin 5) a.val v = v}
  have hiff (u : blockU L) : (u : L) ∈ Z ↔
      ∀ a : alternatingGroup (Fin 5), a ∈ (P : Subgroup _) →
        BinaryPermutation.naturalRepresentation (Fin 5) a.val
          (Multiplicative.toAdd (eU u)) = Multiplicative.toAdd (eU u) := by
    rw [hP]
    exact a5_mem_omega_iff_fixed h eQ eU he S u
  let f : W → F := fun w => ⟨Multiplicative.toAdd (eU ⟨w, w.property.1⟩),
    (hiff ⟨w, w.property.1⟩).mp w.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hu : (⟨x, x.property.1⟩ : blockU L) = ⟨y, y.property.1⟩ :=
        eU.injective (congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg (fun u : blockU L => (u : L)) hu)
    · intro v
      obtain ⟨u, hu⟩ := eU.surjective (Multiplicative.ofAdd v.val)
      have hu' : Multiplicative.toAdd (eU u) = v.val := hu
      have huz : (u : L) ∈ Z := (hiff u).mpr (by rw [hu']; exact v.property)
      exact ⟨⟨u, u.property, huz⟩, Subtype.ext hu'⟩
  calc
    _ = Nat.card W := a5_omega_quotient_card_eq_intersection h S hcore hdis
      (a5_omega_le_core eQ eU he hfaith S)
    _ = Nat.card F := Nat.card_congr (Equiv.ofBijective f hf)
    _ = 2 := hfixed P

end CFSG.Quasithin.ChapterE.Section06.AlternatingLocal
