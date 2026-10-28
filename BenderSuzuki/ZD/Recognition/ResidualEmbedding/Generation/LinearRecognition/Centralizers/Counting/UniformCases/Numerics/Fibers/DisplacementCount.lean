module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.Pairs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Sizes

/-!
# The moving distinguished displacement count

Write A = ⟨Z ∩ M⟩ and q = |C_A(v)|. Fusion control inside M transports
this fixed-subgroup order to every member of the ambient v-class in M.
Thus each actor has |A| - q nonzero displacements. Conjugation in M also
makes the displacement-pair fibers constant on A \ {1}. Counting all
nonzero displacements by their actors and by their values gives

  (|A| - 1) |P_z| = |v^G ∩ M| (|A| - q).

The local field-action calculation supplies |A| = q² and q ≥ 4, so
cancelling q - 1 yields the required factor q + 1. This counts the literal
published pair type without any centralizing hypothesis on the target z.

Source: GLS4, Chapter 2, proof of Lemma 12.8(b), equations (12E–F),
`refs/KGroup/GLS4/Chapter2.tex`. The double count here partitions all
nonzero displacements directly, combining the source's two local counts.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
namespace ResidualDisplacementCount

private def distinguishedConj (h : IsProductDisconnected Z M) (m : M) :
    MulAut (closure (Z ∩ (M : Set G))) :=
  (closure (Z ∩ (M : Set G))).normalizerMonoidHom
    ⟨m, (distinguishedClosure_normalizer h).symm ▸ m.property⟩

private def fixedSubtypeEquiv (A : Subgroup G) (v : G) :
    {a : A // Commute (a : G) v} ≃ (A ⊓ centralizer ({v} : Set G) : Subgroup G) where
  toFun a := ⟨a.val, a.val.property, mem_centralizer_singleton_iff.mpr a.property.eq⟩
  invFun a := ⟨⟨a.val, a.property.1⟩, mem_centralizer_singleton_iff.mp a.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Conjugation in M transports the actual ambient centralizer intersection. -/
private theorem fixed_card_conjugate (h : IsProductDisconnected Z M) (m : M)
    {v w : G} (hm : (m : G) * v * (m : G)⁻¹ = w) :
    Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) =
      Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  let A := closure (Z ∩ (M : Set G))
  let e : {a : A // Commute (a : G) v} ≃ {a : A // Commute (a : G) w} :=
    Equiv.subtypeEquiv (distinguishedConj h m).toEquiv (fun a => by
      change Commute (a : G) v ↔ Commute (MulAut.conj (m : G) (a : G)) w
      rw [← hm]
      exact (commute_map_iff (MulAut.conj (m : G)).injective).symm)
  exact Nat.card_congr ((fixedSubtypeEquiv A v).symm.trans
    (e.trans (fixedSubtypeEquiv A w)))

/-- Conjugate targets have equally many literal displacement pairs. -/
private theorem pairs_card_conjugate (h : IsProductDisconnected Z M) (m : M)
    {z w v : G} (hm : (m : G) * z * (m : G)⁻¹ = w) :
    Nat.card (ResidualDistinguishedDisplacementPairs Z M z v) =
      Nat.card (ResidualDistinguishedDisplacementPairs Z M w v) := by
  let eA := distinguishedConj h m
  let eM := MulAut.conj m
  let f := MulAut.conj (m : G)
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (eA.toEquiv.prodCongr eM.toEquiv) ?_
  intro p
  change (IsConj v (p.2 : G) ∧ (p.1 : G)⁻¹ * ((p.2 : G) * p.1 * (p.2 : G)⁻¹) = z) ↔
    (IsConj v (eM p.2 : G) ∧ (eA p.1 : G)⁻¹ * ((eM p.2 : G) * eA p.1 * (eM p.2 : G)⁻¹) = w)
  have hi : IsConj (p.2 : G) (eM p.2 : G) := isConj_iff.mpr ⟨(m : G), rfl⟩
  have hd : (eA p.1 : G)⁻¹ * ((eM p.2 : G) * eA p.1 * (eM p.2 : G)⁻¹) =
      f ((p.1 : G)⁻¹ * ((p.2 : G) * p.1 * (p.2 : G)⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rfl
  rw [hd, ← hm]
  exact and_congr ⟨fun hc => hc.trans hi, fun hc => hc.trans hi.symm⟩
    f.injective.eq_iff.symm

variable [Finite G]

private theorem fixed_card_of_isConj (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) {v b : G} (hv : PFAppendixIII.IsInvolution v)
    (hvM : v ∈ M) (hbM : b ∈ M) (hb : IsConj v b) :
    Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({b} : Set G) : Subgroup G) =
      Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  have hbI : PFAppendixIII.IsInvolution b := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hb
    exact BenderSuzuki.IsInvolution.map_of_injective hv
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨S, hSM, hf⟩ := r.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hv hbI hvM hbM hb
  exact (fixed_card_conjugate h m hm).symm

private theorem nonzero_displacements_card (A : Subgroup G) (b : G) :
    Nat.card {a : A // (a : G)⁻¹ * (b * a * b⁻¹) ≠ 1} =
      Nat.card A - Nat.card (A ⊓ centralizer ({b} : Set G) : Subgroup G) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have he (a : A) : (a : G)⁻¹ * (b * a * b⁻¹) = 1 ↔ Commute (a : G) b := by
    rw [inv_mul_eq_one, eq_comm, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => not_congr (he a))),
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (fixedSubtypeEquiv A b)]

/-- Count all nonzero displacements first by actor, then by target. -/
private theorem displacement_count_identity (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    {z v : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M) :
    (Nat.card (closure (Z ∩ (M : Set G))) - 1) *
        Nat.card (ResidualDistinguishedDisplacementPairs Z M z v) =
      Nat.card {b : M // IsConj v (b : G)} *
        (Nat.card (closure (Z ∩ (M : Set G))) -
          Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)) := by
  classical
  let A := closure (Z ∩ (M : Set G))
  let C := {b : M // IsConj v (b : G)}
  let W := {a : A // a ≠ 1}
  let P := (b : C) × {a : A // (a : G)⁻¹ * ((b.val : G) * a * (b.val : G)⁻¹) ≠ 1}
  let Q := (w : W) × ResidualDistinguishedDisplacementPairs Z M (w.val : G) v
  let e : P ≃ Q := {
    toFun p := by
      let d : G := (p.2.val : G)⁻¹ * ((p.1.val : G) * p.2.val * (p.1.val : G)⁻¹)
      have hdA : d ∈ A := A.mul_mem (A.inv_mem p.2.val.property)
        (distinguishedConj h p.1.val p.2.val).property
      have hd1 : (⟨d, hdA⟩ : A) ≠ 1 := fun he => p.2.property (congrArg Subtype.val he)
      exact ⟨⟨⟨d, hdA⟩, hd1⟩, ⟨(p.2.val, p.1.val), p.1.property, rfl⟩⟩
    invFun p := ⟨⟨p.2.val.2, p.2.property.1⟩, ⟨p.2.val.1, by
      intro he
      apply p.1.property
      apply Subtype.ext
      exact p.2.property.2.symm.trans he⟩⟩
    left_inv _ := rfl
    right_inv := by
      rintro ⟨⟨⟨w, hwA⟩, hw1⟩, ⟨⟨a, b⟩, hb, he⟩⟩
      dsimp at he
      subst w
      rfl }
  let : Fintype A := Fintype.ofFinite A
  let : Fintype C := Fintype.ofFinite C
  let : Fintype W := Fintype.ofFinite W
  have hP : Nat.card P = Nat.card C *
      (Nat.card A - Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G)) := by
    have hb (b : C) :
        Nat.card {a : A // (a : G)⁻¹ * ((b.val : G) * a * (b.val : G)⁻¹) ≠ 1} =
          Nat.card A - Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G) := by
      rw [nonzero_displacements_card, fixed_card_of_isConj h r hv hvM b.val.property b.property]
    rw [Nat.card_sigma]
    simp_rw [hb]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hW : Nat.card W = Nat.card A - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card]
  let (w : W) : Finite (ResidualDistinguishedDisplacementPairs Z M (w.val : G) v) := by
    unfold ResidualDistinguishedDisplacementPairs
    infer_instance
  have hQ : Nat.card Q = (Nat.card A - 1) *
      Nat.card (ResidualDistinguishedDisplacementPairs Z M z v) := by
    have hw (w : W) : Nat.card (ResidualDistinguishedDisplacementPairs Z M (w.val : G) v) =
        Nat.card (ResidualDistinguishedDisplacementPairs Z M z v) := by
      have hwZ : (w.val : G) ∈ Z ∩ (M : Set G) := hZA.symm ▸
        ⟨w.val.property, fun he => w.property (Subtype.ext he)⟩
      obtain ⟨m, hm⟩ := productDisconnected_conjugator_mem h hwZ.1 hwZ.2 hz hzM
      exact pairs_card_conjugate h m hm
    rw [Nat.card_sigma]
    simp_rw [hw]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, hW]
  exact hQ.symm.trans ((Nat.card_congr e).symm.trans hP)

end ResidualDisplacementCount

variable [Finite G]

/-- The moving-case pair count in GLS4, Lemma 12.8(b), for the actual
ambient actor class inside M and the literal displacement equation in A. -/
public theorem proper_residualGenerated_displacement_pairs_card
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hc : v ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
    (q + 1) * Nat.card (ResidualDistinguishedDisplacementPairs Z M z v) =
      Nat.card {b : M // IsConj v (b : G)} * q := by
  let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
  change (q + 1) * _ = _ * q
  obtain ⟨k, hk, hfixed, _⟩ := (hlocal.quotient_models v hvD hv).2
  have hA := proper_residualGenerated_moving_distinguished_card
    h r ha hz hzM ht htM hL heven hlocal hvD hv hfixed hc
  change q = 2 ^ k at hfixed
  rw [← hfixed] at hA
  have hq : 4 ≤ q := by
    rw [hfixed]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hZA, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  have hcount := ResidualDisplacementCount.displacement_count_identity
    h.disconnected r hZA hz hzM hv hvD.1
  rw [hA] at hcount
  change (q ^ 2 - 1) * _ = _ * (q ^ 2 - q) at hcount
  have hsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hsq : 1 ≤ q ^ 2 := by nlinarith
  have hsq' : q ≤ q ^ 2 := by nlinarith
  have he1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have := Nat.sub_add_cancel hsq
    nlinarith
  have he2 : q ^ 2 - q = (q - 1) * q := by
    have := Nat.sub_add_cancel hsq'
    nlinarith
  rw [he1, he2] at hcount
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < q - 1)
  calc
    (q - 1) * ((q + 1) * Nat.card (ResidualDistinguishedDisplacementPairs Z M z v)) =
        Nat.card {b : M // IsConj v (b : G)} * ((q - 1) * q) := by
      simpa only [mul_assoc] using hcount
    _ = (q - 1) * (Nat.card {b : M // IsConj v (b : G)} * q) := by ring

end BenderSuzuki.ZD
