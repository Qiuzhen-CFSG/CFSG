module

public import BenderSuzuki.ZD.Recognition.NativeSource
public import BenderSuzuki.ZD.ProductClosedCentralFactor
public import BenderSuzuki.ZD.RankOne

/-!
# Recognition for product-closed disconnected involutions

For a product-disconnected invariant set of involutions closed under products
of distinct commuting members, the central involution factor in Theorem ZD
vanishes. The generated subgroup modulo its odd core is therefore a simple
Bender group, with the image of the original distinguished subgroup as Borel.
The other alternative is the full rank-one odd-core factorization.

The central-factor obstruction uses the proved commuting-conjugate geometry
of the Bender models and product closure through an odd kernel.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Theorem
I.8.2, printed pp. 429--430; GLS IV, Chapter 2, Theorem ZD.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Product closure eliminates the extra central factor in the structural
alternative of Theorem ZD. The quotient and Borel use the original closure,
odd core and distinguished subgroup maps. -/
public theorem StructureConclusion.product_closed
    (h : IsProductDisconnected Z M) (hs : StructureConclusion Z M)
    (hprod : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b → a ≠ b → a * b ∈ Z) :
    let L := Subgroup.closure Z
    let O := pPrimeCore 2 L
    commutator L = ⊤ ∧ IsSimpleBenderGroup (L ⧸ O) ∧
      O ≤ M.comap L.subtype ∧
      IsBorelSubgroup ((M.comap L.subtype).map (QuotientGroup.mk' O)) := by
  let L := Subgroup.closure Z
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let q : L →* Q := QuotientGroup.mk' O
  let X := commutator Q
  obtain ⟨u, _huM, hu2, hgenL, hgenQ, hdis, hcomm, hmodel, hO, hBorel, hcoset⟩ := hs
  change X ⊔ Subgroup.zpowers (q u) = ⊤ at hgenQ
  have huc : q u ∈ Subgroup.center Q := by
    have hle : X ⊔ Subgroup.zpowers (q u) ≤ Subgroup.centralizer ({q u} : Set Q) := by
      apply sup_le
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (hcomm x hx (q u) (Subgroup.mem_zpowers _)).eq
      · apply Subgroup.zpowers_le.mpr
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rw [hgenQ] at hle
    exact Subgroup.mem_center_iff.mpr (fun x =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top x)))
  have hqu2 : q u ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hquX : q u ∈ X := by
    by_contra hn
    apply central_coset_false_of_odd_kernel q (QuotientGroup.mk'_surjective O)
      (by
        change Odd (Nat.card (QuotientGroup.mk' O).ker)
        rw [QuotientGroup.ker_mk']
        exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := L) (p := 2)))
      (L.subtype ⁻¹' Z) ?_ ?_ ?_ ?_ X hmodel (q u) huc hqu2 hn ?_
    · obtain ⟨z, hz, _hzM⟩ := h.nonempty
      exact ⟨⟨z, Subgroup.subset_closure hz⟩, hz⟩
    · intro z hz
      exact IsInvolution.subtype (h.involutions z hz) z.property
    · intro g z hz
      exact h.invariant g z hz
    · intro a ha b hb hc hne
      exact hprod a ha b hb (hc.map L.subtype) (fun he => hne (Subtype.ext he))
    · intro z hz
      obtain ⟨hzX, hzne⟩ := hcoset z hz
      refine ⟨⟨(q u)⁻¹ * q z, hzX⟩, ?_, ?_⟩
      · intro he
        apply hzne
        have he' : (q u)⁻¹ * q z = 1 := congrArg Subtype.val he
        exact (inv_mul_eq_one.mp he').symm
      · simp
  have hqu : q u = 1 :=
    (Subgroup.disjoint_def.mp hdis hquX (Subgroup.mem_zpowers _))
  have huO : u ∈ O := (QuotientGroup.eq_one_iff u).mp hqu
  have hderivedL : commutator L = ⊤ := by
    apply top_unique
    rw [← hgenL]
    exact sup_le le_rfl (Subgroup.zpowers_le.mpr (hO huO).2)
  have hderivedQ : X = ⊤ := by
    have hz : Subgroup.zpowers (q u) = ⊥ := by rw [hqu, Subgroup.zpowers_one_eq_bot]
    simpa only [hz, sup_bot_eq] using hgenQ
  let e : X ≃* Q := (MulEquiv.subgroupCongr hderivedQ).trans Subgroup.topEquiv
  have hBmap :
      (((M.comap L.subtype ⊓ commutator L).map q).subgroupOf X).map e.toMonoidHom =
        (M.comap L.subtype).map q := by
    rw [hderivedL, inf_top_eq]
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      change (x : Q) = y at hxy
      exact hxy ▸ hx
    · intro hy
      exact ⟨⟨y, hderivedQ ▸ Subgroup.mem_top y⟩, hy, rfl⟩
  exact ⟨hderivedL, hmodel.map_mulEquiv e, hO.trans inf_le_left,
    hBmap ▸ hBorel.map_mulEquiv e⟩

/-- The full recognition alternative for a product-closed disconnected
involution set. No recognition or model-geometry premise remains. -/
public theorem product_closed_recognition
    (h : IsProductDisconnected Z M)
    (hprod : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b → a ≠ b → a * b ∈ Z) :
    let L := Subgroup.closure Z
    let O := pPrimeCore 2 L
    (primeRank 2 L = 1 ∧ ∀ z : L, (z : G) ∈ Z → O ⊔ Subgroup.zpowers z = ⊤) ∨
      (commutator L = ⊤ ∧ IsSimpleBenderGroup (L ⧸ O) ∧
        O ≤ M.comap L.subtype ∧
        IsBorelSubgroup ((M.comap L.subtype).map (QuotientGroup.mk' O))) := by
  rcases theorem_ZD Z M h with hr | hs
  · left
    apply rank_one_involution_generated hr ((Subgroup.closure Z).subtype ⁻¹' Z)
    · intro z hz
      exact IsInvolution.subtype (h.involutions z hz) z.property
    · obtain ⟨z, hz, _⟩ := h.nonempty
      exact ⟨⟨z, Subgroup.subset_closure hz⟩, hz⟩
    · exact Subgroup.closure_preimage_eq_top Z
  · exact Or.inr (hs.product_closed h hprod)

end BenderSuzuki.ZD
