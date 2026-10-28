module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers

/-!
# The line from the center of the J₂ local quotient

Suppose a source pair R,S lies in an automorphism-invariant local group N with
|O₂(N)| = 64 and N/O₂(N) isomorphic to S₃ × C₃. Let C be the inverse image
of the center of this quotient. Then |N| = 1152 and |C| = 192. The source
odd-complement alternatives force R to be elementary abelian of order nine.
The intersection R ∩ C is nonzero because |N/C| = 6, and proper because
nine does not divide |C|. Its image in R/Φ(R) is the required invariant line.

The argument uses the intrinsic two-core and the actual quotient homomorphism.
It assumes no splitting of N and uses the extending automorphism of each member
of the pair automizer. The local quotient and preservation hypotheses are
explicit: this module alone makes no concrete J₂ calculation.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of refs/quasithin.pdf); GLS3, Table 5.3g, the normalizer of J(S₂).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2

variable {G : Type*} [Group G]

/-- The full inverse image of the center of the intrinsic two-core quotient. -/
def localCenter (N : Subgroup G) : Subgroup N :=
  (center (N ⧸ pCore 2 N)).comap (QuotientGroup.mk' (pCore 2 N))

instance localCenter_characteristic (N : Subgroup G) : (localCenter N).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk inferInstance

private def restrictAut (N : Subgroup G) (b : MulAut G)
    (hN : ∀ x, b x ∈ N ↔ x ∈ N) : MulAut N where
  toFun x := ⟨b x, (hN x).mpr x.property⟩
  invFun x := ⟨b.symm x, (hN _).mp (by simp only [MulEquiv.apply_symm_apply]; exact x.property)⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x)
  right_inv x := Subtype.ext (b.apply_symm_apply x)
  map_mul' x y := Subtype.ext (b.map_mul x y)

theorem localCenter_image_preserved (N : Subgroup G) (b : MulAut G)
    (hN : ∀ x, b x ∈ N ↔ x ∈ N) {x : G}
    (hx : x ∈ (localCenter N).map N.subtype) :
    b x ∈ (localCenter N).map N.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨restrictAut N b hN y,
    characteristic_iff_le_comap.mp inferInstance (restrictAut N b hN) hy, rfl⟩

/-- Characteristicity is relative to S; the resulting normalizer is ambient. -/
theorem normalizer_preserved_of_characteristic {S K : Subgroup G}
    (hKS : K ≤ S) (hchar : (K.subgroupOf S).Characteristic)
    (b : MulAut G) (hS : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ normalizer (K : Set G) ↔ x ∈ normalizer (K : Set G) := by
  have hf (c : MulAut G) (hc : ∀ x, c x ∈ S ↔ x ∈ S)
      {x : G} (hx : x ∈ K) : c x ∈ K :=
    characteristic_iff_le_comap.mp hchar (restrictAut S c hc)
      (show (⟨x, hKS hx⟩ : S) ∈ K.subgroupOf S from hx)
  have hK : K.comap b.toMonoidHom = K := by
    ext x
    constructor
    · intro hx
      have hh := hf b.symm (fun y => by
        simpa only [MulEquiv.apply_symm_apply] using (hS (b.symm y)).symm) hx
      change b.symm (b x) ∈ K at hh
      simpa only [MulEquiv.symm_apply_apply] using hh
    · exact hf b hS
  have hnorm : (normalizer (K : Set G)).comap b.toMonoidHom = normalizer (K : Set G) := by
    rw [comap_normalizer_eq_of_surjective K b.surjective, hK]
  intro x
  exact SetLike.ext_iff.mp hnorm x

variable [Finite G]

abbrev LocalQuotient := Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)

private theorem localQuotient_card : Nat.card LocalQuotient = 18 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem localQuotient_center_card : Nat.card (center LocalQuotient) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

omit [Finite G] in
/-- The orders used in the line argument follow from the actual local quotient. -/
theorem local_center_orders (N : Subgroup G)
    (hcore : Nat.card (pCore 2 N) = 64)
    (e : (N ⧸ pCore 2 N) ≃* LocalQuotient) :
    Nat.card N = 1152 ∧ Nat.card (localCenter N) = 192 := by
  have hquot : Nat.card (N ⧸ pCore 2 N) = 18 :=
    (Nat.card_congr e.toEquiv).trans localQuotient_card
  have hcenter : Nat.card (center (N ⧸ pCore 2 N)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans localQuotient_center_card
  have hNcard : Nat.card N = 1152 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 N), hquot, hcore]
  have hindex : (center (N ⧸ pCore 2 N)).index = 6 := by
    have hc := (center (N ⧸ pCore 2 N)).card_mul_index
    rw [hcenter, hquot] at hc
    omega
  have hCindex : (localCenter N).index = 6 := by
    rw [localCenter, index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hindex]
  refine ⟨hNcard, ?_⟩
  have hc := (localCenter N).card_mul_index
  rw [hCindex, hNcard] at hc
  omega

/-- The intersection with the local central preimage gives a common invariant line. -/
theorem invariant_line_of_local_center {S : Sylow 2 G} {R N : Subgroup G}
    (h : PairInput S R) (hRN : R ≤ N)
    (hN : ∀ b : MulAut G, (∀ x, b x ∈ S ↔ x ∈ S) →
      ∀ x, b x ∈ N ↔ x ∈ N)
    (hNcard : Nat.card N = 1152) (hCcard : Nat.card (localCenter N) = 192) :
    ∃ A : Subgroup (R ⧸ frattini R), Nat.card A = 3 ∧ A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ a ∈ pairAutomizer (S : Subgroup G) R, ∀ x ∈ A,
        quotientAut (frattini R) a x ∈ A := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  have hRcard : Nat.card R = 9 := by
    have hd := card_dvd_of_le hRN
    rw [hNcard] at hd
    rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩
    · exact hc
    · rw [hc] at hd
      norm_num at hd
  have hPhi : frattini R = ⊥ := by
    rcases h.oddComplement with ⟨he, _⟩ | ⟨_, hc, _⟩
    · let _ := he
      exact frattini_eq_bot_of_isElementaryAbelian (p := 3)
    · rw [hRcard] at hc
      norm_num at hc
  let C := localCenter N
  let i : R →* N := inclusion hRN
  let K : Subgroup R := C.comap i
  have hquot : Nat.card (N ⧸ C) = 6 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    change Nat.card N = Nat.card (N ⧸ C) * Nat.card (localCenter N) at hc
    rw [hNcard, hCcard] at hc
    omega
  have hKb : K ≠ ⊥ := by
    intro hK
    let f := (QuotientGroup.mk' C).comp i
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff f).mp
      simpa only [f, ← MonoidHom.comap_ker, QuotientGroup.ker_mk'] using hK
    have hd := card_dvd_of_injective f hf
    rw [hRcard, hquot] at hd
    norm_num at hd
  have hKt : K ≠ ⊤ := by
    intro hK
    let f : R →* C := i.codRestrict C (fun r =>
      show r ∈ K from hK.symm ▸ mem_top r)
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : C => (z.val : G)) he)
    have hd := card_dvd_of_injective f hf
    change Nat.card R ∣ Nat.card (localCenter N) at hd
    rw [hRcard, hCcard] at hd
    norm_num at hd
  have hKcard : Nat.card K = 3 := by
    have hd : Nat.card K ∣ 3 ^ 2 := by
      simpa only [hRcard, Nat.reducePow] using K.card_subgroup_dvd_card
    obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases k
    · exact (hKb (card_eq_one.mp hc)).elim
    · exact hc
    · exact (hKt ((K.card_eq_iff_eq_top).mp (hc.trans hRcard.symm))).elim
  let q := QuotientGroup.mk' (frattini R)
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk', hPhi])
  refine ⟨K.map q, (card_map_of_injective hqi).trans hKcard, ?_, ?_, ?_⟩
  · intro hK
    apply hKb
    have hh := (map_eq_bot_iff K).mp hK
    simpa only [q, QuotientGroup.ker_mk', hPhi, le_bot_iff] using hh
  · intro hK
    apply hKt
    have hh := congrArg (Subgroup.comap q) hK
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', hPhi, sup_bot_eq,
      comap_top] using hh
  · intro a ha v hv
    obtain ⟨b, hb, hab⟩ := ha
    obtain ⟨r, hr, rfl⟩ := hv
    refine ⟨a r, ?_, (quotientAut_apply_mk _ _ _).symm⟩
    have hmem : (r : G) ∈ C.map N.subtype := ⟨i r, hr, rfl⟩
    have himage := localCenter_image_preserved N b (hN b hb) hmem
    obtain ⟨y, hy, he⟩ := himage
    have he' : y = i (a r) := Subtype.ext (he.trans (hab r).symm)
    change i (a r) ∈ C
    exact he' ▸ hy


/-- A common line excludes irreducibility for every two-subgroup of the pair automizer. -/
theorem pairReducible_of_local_center {S : Sylow 2 G} {R N : Subgroup G}
    (h : PairInput S R) (hRN : R ≤ N)
    (hN : ∀ b : MulAut G, (∀ x, b x ∈ S ↔ x ∈ S) →
      ∀ x, b x ∈ N ↔ x ∈ N)
    (hNcard : Nat.card N = 1152) (hCcard : Nat.card (localCenter N) = 192) :
    PairReducible (S : Subgroup G) R := by
  obtain ⟨A, _, hAb, hAt, hA⟩ := invariant_line_of_local_center h hRN hN hNcard hCcard
  exact pairReducible_of_invariant _ _ ⟨A, hAb, hAt, hA⟩

/-- The geometric input is an isomorphism of the actual local quotient. -/
theorem pairReducible_of_local_quotient {S : Sylow 2 G} {R N : Subgroup G}
    (h : PairInput S R) (hRN : R ≤ N)
    (hN : ∀ b : MulAut G, (∀ x, b x ∈ S ↔ x ∈ S) →
      ∀ x, b x ∈ N ↔ x ∈ N)
    (hcore : Nat.card (pCore 2 N) = 64)
    (e : (N ⧸ pCore 2 N) ≃* LocalQuotient) :
    PairReducible (S : Subgroup G) R := by
  obtain ⟨hNcard, hCcard⟩ := local_center_orders N hcore e
  exact pairReducible_of_local_center h hRN hN hNcard hCcard

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2
