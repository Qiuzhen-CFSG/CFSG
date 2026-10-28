module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.SingleEndpoint
public import Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive.Natural
public import Theory.Representation.SL2FourNaturalExtensions.Splitting

/-!
# The actual endpoint for a specified natural symplectic embedding

The specified subgroup of the literal symplectic quotient is pulled back
into the same original normalizer. The full inverse-image equality is
retained, so any particular radical or cubic whose quotient image lies in
that subgroup belongs to this very endpoint. Natural coordinates and the
actual complement remain marked throughout the construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "SL" => Representation.SL2FourNatural.SL
local notation "W" => Representation.SL2FourNatural.V

/-- The literal inverse image of a specified natural SL₂(4) embedding
is split, with its whole original kernel and quotient action retained. -/
theorem exists_specified_natural_endpoint
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (e : Additive A ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      Matrix.PSp4Three.Sp 2 (ZMod 2))
    (hφ : ∀ (g : normalizer (A : Set G)) (x : A),
      (φ (QuotientGroup.mk g)).val *ᵥ e (Additive.ofMul x) =
        e (Additive.ofMul (A.normalizerMonoidHom g x)))
    (v : W ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (ι : SL →* Matrix.PSp4Three.Sp 2 (ZMod 2)) (hι : Function.Injective ι)
    (hv : ∀ g w, (ι g).val *ᵥ v w = v (Representation.SL2FourNatural.action g w)) :
    ∃ (P K : Subgroup G) (_hAP : A ≤ P)
      (hPN : P ≤ normalizer (A : Set G)) (hKP : K ≤ P),
      P = (ι.range.comap (φ.toMonoidHom.comp
        (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G)))))).map
          (normalizer (A : Set G)).subtype ∧
      Nat.card P = 960 ∧ Nat.card K = 60 ∧ A ⊓ K = ⊥ ∧ A ⊔ K = P ∧
      ∃ q : P →* SL, Function.Surjective q ∧ q.ker = A.subgroupOf P ∧
        ∃ c : A ≃* Multiplicative W,
          (∀ (g : P) (a : A), c (A.normalizerMonoidHom (inclusion hPN g) a) =
            Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (c a).toAdd)) ∧
          (A.subgroupOf P).IsComplement' (K.subgroupOf P) ∧
          ∃ k : K ≃* SL, ∀ g : K, k g = q (inclusion hKP g) := by
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
  let l : Additive A ≃ₗ[ZMod 2] W := e.trans v.symm
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
  refine ⟨P, K, hAP, hPN, hKP, rfl, hPcard, hKcard, hAK, hjoin, q, hq, hk, c, hc, hC',
    t.symm.trans κ, ?_⟩
  intro g
  change κ (t.symm g) = q (inclusion hKP g)
  rw [hκ]
  apply congrArg q
  apply Subtype.ext
  exact congrArg (fun x : K => (x : G)) (t.apply_symm_apply g)

end CFSG.Quasithin.HigmanSims
