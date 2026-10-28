module
public import Theory.GroupTheory.AutomorphismSquareExchangeRank
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.ElementaryAbelian.Injective

/-!
# Prime-order obstructions to exchanged square actors

Schur's lemma embeds an elementary actor in the automorphisms of the
faithful irreducible square. An exchange bounds its rank by one plus the
automorphism rank of one factor. Commuting that exchange with a prime-order
element in one factor gives a prime-order commutator, so binary prime
 displacement bounds the exchange. Factor-preserving involutions are in
the square image whenever involutory factor automorphisms are inner.

The J₁ application uses an element of order19 and automorphism rank three.
Source: Aschbacher--Smith D.3.7, printed pp.197--199.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {S V : Type*} [Group S] [Finite S] [IsQuasisimple S]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (hZ : center S = ⊥)
include hZ

/-- An elementary normalizer actor containing an exchange has the source's
small rank, with no assumption on the full normalizer quotient. -/
theorem square_exchange_rank_le
    (ρ : Representation (ZMod 2) (S × S) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A)
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v)) : rank A ≤ primeRank 2 (MulAut S) + 1 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  have hfi : Function.Injective (f.comp A.subtype) :=
    (MulAut.congr e.symm).injective.comp
      (normalizer_elementary_conjugation_injective ρ hi A)
  let E := (f.comp A.subtype).range
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    (f.comp A.subtype).rangeRestrict (f.comp A.subtype).rangeRestrict_surjective
  have hfa : f a = MulEquiv.prodComm := by
    apply MulEquiv.ext
    intro g
    apply e.injective
    apply Subtype.ext
    have he : (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
      congrArg Subtype.val (e.apply_symm_apply _)
    rw [he]
    apply Units.ext
    apply LinearMap.ext
    intro v
    change a.val.val (ρ g ((a.val⁻¹).val v)) = ρ (g.2,g.1) v
    have hs := hswap g ((a.val⁻¹).val v)
    change a.val.val (ρ g ((a.val⁻¹).val v)) =
      ρ (g.2,g.1) (a.val.val ((a.val⁻¹).val v)) at hs
    rw [hs]
    congr 1
    change (a.val.val * (a.val⁻¹).val) v = v
    rw [←Units.val_mul,mul_inv_cancel,Units.val_one]
    rfl
  have hE : (MulEquiv.prodComm : MulAut (S × S)) ∈ E :=
    ⟨⟨a,ha⟩,hfa⟩
  have hb := AutomorphismSquare.abelian_exchange_rank_le hZ E hE
  let : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype (Subgroup.subtype_injective _)
  have hc := (primeRank_le_iff_elementary_card_le E).mp hb
    (⊤ : Subgroup E) inferInstance
  have hcard : Nat.card A = Nat.card (⊤ : Subgroup E) :=
    (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).trans
      (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv).symm
  rw [←hcard] at hc
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank,Nat.log_pow (by decide : 1 < 2)] using hh

omit hZ [Finite S] [IsQuasisimple S] in
/-- A literal factor exchange moves at least half the binary degree of any
odd prime-order element of the factor. -/
theorem square_exchange_prime_displacement
    (ρ : Representation (ZMod 2) (S × S) V) (hf : Function.Injective ρ)
    (a : linearNormalizer ρ)
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : S) (hx : orderOf x = p) :
    orderOf (2 : ZMod p) ≤ 2 * fixedCodim (normalizerRepresentation ρ) (zpowers a) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let j : S × S →* linearNormalizer ρ :=
    ρ.asGroupHom.codRestrict _ (fun g => (actionImage ρ).le_normalizer ⟨g,rfl⟩)
  have hj : Function.Injective j := by
    intro g h he
    exact hf (congrArg (fun z : linearNormalizer ρ => z.val.val) he)
  have he : a * j (x,1) * a⁻¹ = j (1,x) := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    change a.val.val (ρ (x,1) ((a.val⁻¹).val v)) = ρ (1,x) v
    have hs := hswap (x,1) ((a.val⁻¹).val v)
    change a.val.val (ρ (x,1) ((a.val⁻¹).val v)) =
      ρ (1,x) (a.val.val ((a.val⁻¹).val v)) at hs
    rw [hs]
    congr 1
    change (a.val.val * (a.val⁻¹).val) v = v
    rw [←Units.val_mul,mul_inv_cancel,Units.val_one]
    rfl
  have hcomm : a * j (x,1) * a⁻¹ * (j (x,1))⁻¹ = j (x⁻¹,x) := by
    rw [he,←map_inv,←map_mul]
    simp only [Prod.inv_mk,Prod.mk_mul_mk,inv_one,one_mul,mul_one]
  have hord : orderOf (a * j (x,1) * a⁻¹ * (j (x,1))⁻¹) = p := by
    rw [hcomm,orderOf_injective j hj,Prod.orderOf,orderOf_inv,hx,Nat.lcm_self]
  exact (prime_order_le_fixedCodim (normalizerRepresentation ρ)
    (fun _ _ he => Subtype.ext (Units.ext he)) hp hp2 _ hord).trans
      (fixedCodim_commutator_le_twice (normalizerRepresentation ρ) a (j (x,1)))

/-- The prime-order displacement contradicts a small elementary exchange. -/
theorem square_exchanged_actor_strict_bound
    (ρ : Representation (ZMod 2) (S × S) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A)
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : S) (hx : orderOf x = p)
    (hdegree : 4 * (primeRank 2 (MulAut S) + 1) < orderOf (2 : ZMod p)) :
    2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  have hr := square_exchange_rank_le hZ ρ hi hf A a ha hswap
  have hd := square_exchange_prime_displacement ρ hf a hswap hp hp2 x hx
  have hm := Submodule.finrank_mono (show fixedSpace (normalizerRepresentation ρ) A ≤
      fixedSpace (normalizerRepresentation ρ) (zpowers a) from
        fun v hv b => hv ⟨b,(zpowers_le.mpr ha) b.property⟩)
  have h1 := fixedCodim_add_finrank (normalizerRepresentation ρ) (zpowers a)
  have h2 := fixedCodim_add_finrank (normalizerRepresentation ρ) A
  omega

variable (hinner : ∀ α : MulAut S, α ^ 2 = 1 → ∃ x : S, α = MulAut.conj x)
include hinner
omit [FiniteDimensional (ZMod 2) V] in
/-- A factor-preserving normalizer involution belongs to the actual square image. -/
theorem square_preserving_involution_mem
    (ρ : Representation (ZMod 2) (S × S) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (a : linearNormalizer ρ) (h2 : a ^ 2 = 1)
    (hpres : a.val ∈ normalizer
      (((⊤ : Subgroup (S)).prod ⊥).map ρ.asGroupHom : Set _)) :
    a.val ∈ actionImage ρ := by
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  have hconj (g : S × S) :
      (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hdiag : ∃ α β : MulAut S, f a = α.prodCongr β := by
    rcases AutomorphismSquare.normal_form hZ (f a) with h | ⟨α,β,h⟩
    · exact h
    · let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
      let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
      obtain ⟨x,hx⟩ := exists_ne (1 : S)
      have hg : (e (f a (x,1))).val ∈
          ((⊤ : Subgroup S).prod ⊥).map ρ.asGroupHom := by
        rw [hconj]
        exact (mem_normalizer_iff.mp hpres _).mp ⟨(x,1),⟨mem_top _,rfl⟩,rfl⟩
      obtain ⟨y,hy,he⟩ := hg
      have hxy : y = f a (x,1) := e.injective (Subtype.ext he)
      have hb : β x = 1 := by
        have hh := mem_bot.mp hy.2
        rw [hxy,h] at hh
        exact hh
      exact (hx (β.injective (hb.trans β.map_one.symm))).elim
  obtain ⟨α,β,hdiag⟩ := hdiag
  have hfa2 : (f a) ^ 2 = 1 := by rw [←map_pow,h2,map_one]
  have hα : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun (hdiag ▸ hfa2) (x,1))
  have hβ : β ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun (hdiag ▸ hfa2) (1,x))
  obtain ⟨x,hx⟩ := hinner α hα
  obtain ⟨y,hy⟩ := hinner β hβ
  have hfinner : f a = MulAut.conj (x,y) := by rw [hdiag,hx,hy]; rfl
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  let : IsIrreducible (τ.comp (actionImage ρ).subtype) := imageRepresentation_isIrreducible ρ hi
  exact involution_mem_of_inner τ (actionImage ρ) (fun _ _ h => Units.ext h) a
    (congrArg Subtype.val h2) ⟨e (x,y),by
      apply MulEquiv.ext
      intro z
      obtain ⟨g,rfl⟩ := e.surjective z
      have hh : e (f a g) = (actionImage ρ).normalizerMonoidHom a (e g) :=
        e.apply_symm_apply _
      rw [hfinner] at hh
      exact hh.symm.trans (by simp only [MulAut.conj_apply,map_mul,map_inv])⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- Factor preservation places an elementary actor in the actual square image. -/
theorem square_preserving_actor_le
    (ρ : Representation (ZMod 2) (S × S) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (hpres : ∀ a ∈ A, a.val ∈ normalizer
      (((⊤ : Subgroup (S)).prod ⊥).map ρ.asGroupHom : Set _)) :
    A ≤ (actionImage ρ).subgroupOf (linearNormalizer ρ) := by
  intro a ha
  exact square_preserving_involution_mem hZ hinner ρ hi hf a
    (elemPow_eq_one_of_isElementaryAbelian a ha) (hpres a ha)

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : S) (hx : orderOf x = p)
  (hdegree : 4 * (primeRank 2 (MulAut S) + 1) < orderOf (2 : ZMod p))
include hp hp2 x hx hdegree
omit hinner in
/-- The exchange exclusion is unchanged by a twist of the factor marking. -/
theorem square_twisted_exchange_strict_bound
    (ρ : Representation (ZMod 2) (S × S) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A) (α : MulAut (S))
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v)) :
    2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  let δ := α.prodCongr (MulEquiv.refl (S))
  let σ : Representation (ZMod 2) (S × S) V :=
    ρ.comp δ.toMonoidHom
  have himage : actionImage σ = actionImage ρ := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨δ g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := δ.surjective g
      exact ⟨g,Units.ext rfl⟩
  have hn : linearNormalizer ρ ≤ linearNormalizer σ := by
    unfold linearNormalizer
    rw [himage]
  let j := inclusion hn
  have hj : Function.Injective j := inclusion_injective hn
  let C := A.map j
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map j
  have hiσ : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff δ.toMonoidHom δ.surjective ρ).mpr hi
  have hfσ : Function.Injective σ := hf.comp δ.injective
  have hs : ∀ g v, normalizerRepresentation σ (j a) (σ g v) =
      σ (g.2,g.1) (normalizerRepresentation σ (j a) v) := by
    rintro ⟨x,y⟩ v
    have hh := hswap (α x,y) v
    change normalizerRepresentation ρ a (ρ (α x,y) v) =
      ρ (α y,x) (normalizerRepresentation ρ a v)
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hb := square_exchanged_actor_strict_bound hZ σ hiσ hfσ C (j a)
    (mem_map_of_mem j ha) hs hp hp2 x hx hdegree
  have hcod : fixedCodim (normalizerRepresentation σ) C =
      fixedCodim (normalizerRepresentation ρ) A :=
    (fixedCodim_map_equivariant (normalizerRepresentation ρ) (normalizerRepresentation σ)
      j (LinearEquiv.refl _ _) (fun _ _ => rfl) A).symm
  rw [hcod,show rank C = rank A from rank_map_injective j hj A] at hb
  exact hb
/-- Every elementary actor of ratio at most two lies in the actual square image. -/
theorem small_actor_le_square_image
    (ρ : Representation (ZMod 2) (S × S) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (normalizerRepresentation ρ) A ≤ 2 * rank A) :
    A ≤ (actionImage ρ).subgroupOf (linearNormalizer ρ) := by
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  intro a ha
  have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hconj (g : S × S) :
      (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply _)
  rcases AutomorphismSquare.normal_form hZ (f a) with ⟨α,β,hdiag⟩ | ⟨α,β,hswap⟩
  · apply square_preserving_involution_mem hZ hinner ρ hi hf a h2
    let J := ((⊤ : Subgroup S).prod ⊥).map ρ.asGroupHom
    have hJ : J ≤ actionImage ρ := by rintro _ ⟨g,_,rfl⟩; exact ⟨g,rfl⟩
    have hmem (g : S × S) : (e g).val ∈ J ↔ g.2 = 1 := by
      constructor
      · rintro ⟨k,hk,hkg⟩
        have he : k = g := e.injective (Subtype.ext hkg)
        exact he ▸ mem_bot.mp hk.2
      · intro hg
        exact ⟨g,⟨mem_top _,hg⟩,rfl⟩
    apply mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      obtain ⟨g,rfl⟩ := hJ hz
      change (e g).val ∈ J at hz
      change a.val * (e g).val * a.val⁻¹ ∈ J
      rw [←hconj,hdiag]
      apply (hmem _).mpr
      change β g.2 = 1
      rw [(hmem g).mp hz,β.map_one]
    · intro hz
      have hz' : z ∈ actionImage ρ := (mem_normalizer_iff.mp a.property z).mpr (hJ hz)
      obtain ⟨g,rfl⟩ := hz'
      change a.val * (e g).val * a.val⁻¹ ∈ J at hz
      rw [←hconj,hdiag] at hz
      apply (hmem g).mpr
      exact β.injective (((hmem _).mp hz).trans β.map_one.symm)
  · have hfa2 : (f a) ^ 2 = 1 := by rw [←map_pow,h2,map_one]
    have hba (x : S) : β (α x) = x :=
      congrArg Prod.snd (DFunLike.congr_fun (hswap ▸ hfa2) (1,x))
    have hβ : β = α.symm := by
      apply MulEquiv.ext
      intro x
      obtain ⟨x,rfl⟩ := α.surjective x
      exact (hba x).trans (α.symm_apply_apply x).symm
    have hex : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
        ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v) := by
      intro g v
      have hh := congrArg (fun x : (Module.End (ZMod 2) V)ˣ => x.val
        (normalizerRepresentation ρ a v)) (hconj g).symm
      rw [hswap,hβ] at hh
      change a.val.val (ρ g ((a.val⁻¹).val (a.val.val v))) =
        ρ (α g.2,α.symm g.1) (a.val.val v) at hh
      have hv : (a.val⁻¹).val (a.val.val v) = v := by
        change ((a.val⁻¹).val * a.val.val) v = v
        rw [←Units.val_mul,inv_mul_cancel,Units.val_one]
        rfl
      rwa [hv] at hh
    exact ((not_lt_of_ge hsmall)
      (square_twisted_exchange_strict_bound hZ hp hp2 x hx hdegree ρ hi hf A a ha α hex)).elim

end Representation.BinaryOffender
