module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenSymplecticNormalizer
public import Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive.Natural
public import Theory.Representation.SL2FourNaturalExtensions.Splitting

/-!
# An actual natural linear endpoint in the original sixteen normalizer

Pull back the marked field-natural SL₂(4) inside the full symplectic quotient
of the original normalizer. The original form coordinates identify the
literal kernel with F₄² and preserve every conjugation action. Universal
natural-module splitting then gives a complement in this actual preimage.
Both factors are mapped into the unchanged ambient group, retaining the
original sixteen, the quotient, and the natural action marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "SL" => Representation.SL2FourNatural.SL
local notation "W" => Representation.SL2FourNatural.V

/-- The original sixteen has an actual order960 natural SL₂(4) preimage
inside its full normalizer, with a literal order60 complement and both
original kernel and quotient actions marked. -/
theorem TypeAt.sixteen_natural_endpoint (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    ∃ (P K : Subgroup G) (_hAP : A ≤ P)
      (hPN : P ≤ normalizer (A : Set G)) (hKP : K ≤ P),
      Nat.card P = 960 ∧ Nat.card K = 60 ∧ A ⊓ K = ⊥ ∧ A ⊔ K = P ∧
      ∃ q : P →* SL, Function.Surjective q ∧ q.ker = A.subgroupOf P ∧
        ∃ c : A ≃* Multiplicative W,
          (∀ (g : P) (a : A), c (A.normalizerMonoidHom (inclusion hPN g) a) =
            Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (c a).toAdd)) ∧
          (A.subgroupOf P).IsComplement' (K.subgroupOf P) ∧
          ∃ k : K ≃* SL, ∀ g : K, k g = q (inclusion hKP g) := by
  obtain ⟨B, _, _, _, e, φ, hφ⟩ := h.sixteen_symplectic_normalizer A hA hCA hpure hpoints
  obtain ⟨v, ι, hι, hv⟩ :=
    Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive.exists_marked_symplectic_embedding
  let N := normalizer (A : Set G)
  let AN := A.subgroupOf N
  let qN : N →* Matrix.PSp4Three.Sp 2 (ZMod 2) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' AN)
  have hqN : Function.Surjective qN :=
    φ.surjective.comp (QuotientGroup.mk'_surjective AN)
  have hqNk (g : N) : qN g = 1 ↔ (g : G) ∈ A := by
    change φ (QuotientGroup.mk' AN g) = 1 ↔ _
    rw [← φ.map_one, φ.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  let I := ι.range
  let j : SL ≃* I := MonoidHom.ofInjective hι
  let D := I.comap qN
  let qD : D →* SL := j.symm.toMonoidHom.comp (qN.subgroupComap I)
  have hqD : Function.Surjective qD :=
    j.symm.surjective.comp (qN.subgroupComap_surjective_of_surjective I hqN)
  have hιqD (g : D) : ι (qD g) = qN g :=
    congrArg Subtype.val (j.apply_symm_apply (qN.subgroupComap I g))
  have hqDk (g : D) : qD g = 1 ↔ ((g : N) : G) ∈ A := by
    rw [← hqNk g, ← hιqD g, ← ι.map_one, hι.eq_iff]
  let P := D.map N.subtype
  let d : D ≃* P := D.equivMapOfInjective N.subtype N.subtype_injective
  have hd (g : P) : (((d.symm g : D) : N) : G) = (g : G) :=
    congrArg Subtype.val (d.apply_symm_apply g)
  have hPN : P ≤ N := by
    rintro _ ⟨g, _, rfl⟩
    exact g.property
  have hAP : A ≤ P := by
    intro a ha
    let aN : N := ⟨a, A.le_normalizer ha⟩
    have haD : aN ∈ D := by
      change qN aN ∈ I
      rw [(hqNk aN).mpr ha]
      exact I.one_mem
    exact ⟨aN, haD, rfl⟩
  let q : P →* SL := qD.comp d.symm.toMonoidHom
  have hq : Function.Surjective q := hqD.comp d.symm.surjective
  have hk : q.ker = A.subgroupOf P := by
    ext g
    change qD (d.symm g) = 1 ↔ (g : G) ∈ A
    rw [hqDk, hd]
  have hιq (g : P) : ι (q g) = qN (inclusion hPN g) := by
    change ι (qD (d.symm g)) = _
    rw [hιqD]
    congr 1
    exact Subtype.ext (hd g)
  let l : Additive A ≃ₗ[ZMod 2] W := e.toLinearEquiv.trans v.symm
  let c : A ≃* Multiplicative W := MulEquiv.toAdditive.symm l.toAddEquiv
  have hc (g : P) (a : A) : c (A.normalizerMonoidHom (inclusion hPN g) a) =
      Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (c a).toAdd) := by
    apply Multiplicative.toAdd.injective
    apply v.injective
    change v (v.symm (e (Additive.ofMul (A.normalizerMonoidHom (inclusion hPN g) a)))) =
      v (Representation.SL2FourNatural.action (q g) (v.symm (e (Additive.ofMul a))))
    rw [v.apply_symm_apply, ← hv, v.apply_symm_apply, hιq]
    exact (hφ (inclusion hPN g) a).symm
  let a : q.ker ≃* A := (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hAP)
  let w : q.ker ≃* Multiplicative W := a.trans c
  have hw (g : P) (u : q.ker) : w (MulAut.conjNormal g u) =
      Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (w u).toAdd) := by
    have he : a (MulAut.conjNormal g u) = A.normalizerMonoidHom (inclusion hPN g) (a u) := by
      apply Subtype.ext
      rfl
    change c (a (MulAut.conjNormal g u)) = _
    rw [he]
    exact hc g (a u)
  obtain ⟨C, hC, κ, hκ⟩ :=
    Representation.SL2FourNaturalExtensions.exists_marked_complement q hq w hw
  let K := C.map P.subtype
  let t : C ≃* K := C.equivMapOfInjective P.subtype P.subtype_injective
  have hKP : K ≤ P := by
    rintro _ ⟨g, _, rfl⟩
    exact g.property
  have hKC : K.subgroupOf P = C := by
    ext g
    change (g : G) ∈ C.map P.subtype ↔ g ∈ C
    constructor
    · rintro ⟨x, hx, he⟩
      exact (Subtype.ext he : x = g) ▸ hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hC' : (A.subgroupOf P).IsComplement' (K.subgroupOf P) := by
    rw [hKC, ← hk]
    exact hC
  have hKcard : Nat.card K = 60 := by
    rw [← Nat.card_congr t.toEquiv, Nat.card_congr κ.toEquiv,
      Nat.card_congr Representation.SL2FourNatural.alternatingFiveEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hPcard : Nat.card P = 960 := by
    have hh := hC'.card_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hKP).toEquiv, hA, hKcard] at hh
    omega
  have hAK : A ⊓ K = ⊥ := by
    apply bot_unique
    rintro x ⟨hxA, hxK⟩
    have hh : (⟨x, hAP hxA⟩ : P) = 1 :=
      disjoint_def.mp hC'.disjoint hxA hxK
    exact congrArg Subtype.val hh
  have hjoin : A ⊔ K = P := by
    have hh := congrArg (fun S : Subgroup P => S.map P.subtype) hC'.sup_eq_top
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hAP,
      map_subgroupOf_eq_of_le hKP, ← MonoidHom.range_eq_map, P.range_subtype] at hh
  refine ⟨P, K, hAP, hPN, hKP, hPcard, hKcard, hAK, hjoin, q, hq, hk, c, hc, hC',
    t.symm.trans κ, ?_⟩
  intro g
  change κ (t.symm g) = q (inclusion hKP g)
  rw [hκ]
  apply congrArg q
  apply Subtype.ext
  exact congrArg (fun x : K => (x : G)) (t.apply_symm_apply g)

end CFSG.Quasithin.HigmanSims
