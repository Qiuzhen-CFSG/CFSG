module

public import Theory.Character.ModularBlock.NormalizerRestriction

/-!
# Vanishing of nonidentity fixed normalizer transfer terms

Suppose the embedded centralizer-algebra element has exact maximal
2-coefficient support at the canonical copy of Q in its normalizer. Then a
nonidentity Q-fixed coset of the normalizer contributes zero Q-Brauer
restriction under conjugation. The coefficient ring is arbitrary commutative;
no characteristic, centrality, or idempotence assumption is needed.

A surviving coefficient centralizes both Q and its conjugate in the
normalizer. Since Q is normal there, their join is a 2-group with nonzero
coefficient support. Maximal support bounds its order by that of Q; equal
orders of Q and its conjugate force equality. The coset representative then
normalizes Q, contradicting its nonidentity coset.

Ported from `fixedTerm_zero_of_exact_normalizer_support` in
`c3503435:glauberman_zStar/Submission/ZStar/BrauerThirdMain.lean`.
This is the generic support input to the specialized Third Main transfer
contradiction; it uses only the normalizer coefficient-restriction bridge.
-/

public section
noncomputable section
namespace ModularBlock.BrauerThirdMain
open Subgroup
universe u v
attribute [local instance] Fintype.ofFinite

/-- If the embedded normalizer orbit sum has exact maximal support `Q`, every
nonidentity `Q`-fixed transfer coset has zero `Q`-Brauer restriction. -/
theorem fixedTerm_zero_of_exact_normalizer_support
    [Fact (Nat.Prime 2)]
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a)
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))))
    (c : G ⧸ Subgroup.normalizer (Q : Set G))
    (hcFixed : c ∈ MulAction.fixedPoints Q
      (G ⧸ Subgroup.normalizer (Q : Set G)))
    (hcNe : c ≠
      (QuotientGroup.mk (1 : G) :
        G ⧸ Subgroup.normalizer (Q : Set G))) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R
          (Subgroup.normalizer (Q : Set G)) c.out
          (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a)) = 0 := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let P : Subgroup N := Q.subgroupOf N
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding R Q
  let B : MonoidAlgebra R N := E a
  let g : G := c.out
  by_contra hRestrNe
  have hfixed : ∀ q : Q, (q : G) • c = c := by
    intro q
    change q • c = c
    exact (MulAction.mem_fixedPoints.mp hcFixed) q
  have hconjMem : ∀ q : Q, g⁻¹ * (q : G) * g ∈ N := by
    intro q
    have hmk :
        (QuotientGroup.mk g : G ⧸ N) =
          (QuotientGroup.mk ((q : G) * g) : G ⧸ N) := by
      calc
        (QuotientGroup.mk g : G ⧸ N) = c := by
          exact QuotientGroup.out_eq' c
        _ = (q : G) • c := (hfixed q).symm
        _ = (QuotientGroup.mk ((q : G) * g) : G ⧸ N) := by
          simpa [g, N, smul_eq_mul] using
            (MulAction.Quotient.mk_smul_out N (q : G) c).symm
    rw [QuotientGroup.eq] at hmk
    simpa only [mul_assoc] using hmk
  let φ : Q →* N :=
    { toFun := fun q ↦ ⟨g⁻¹ * (q : G) * g, hconjMem q⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro q r
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hφinj : Function.Injective φ := by
    intro q r hqr
    apply Subtype.ext
    have hqrG := congrArg (fun n : N ↦ (n : G)) hqr
    change g⁻¹ * (q : G) * g = g⁻¹ * (r : G) * g at hqrG
    have hcancel := congrArg (fun x : G ↦ g * x * g⁻¹) hqrG
    simpa [mul_assoc] using hcancel
  let Qg : Subgroup N := MonoidHom.range φ
  have hQg : IsPGroup 2 Qg :=
    hQ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hP : IsPGroup 2 P := by
    simpa [P, N] using subgroupOf_normalizer_isPGroup Q hQ
  have hcardQgQ : Nat.card Qg = Nat.card Q := by
    let e : Q ≃ Qg := Equiv.ofBijective φ.rangeRestrict
      ⟨(fun q r h ↦ hφinj (congrArg Subtype.val h)),
        φ.rangeRestrict_surjective⟩
    exact (Nat.card_congr e).symm
  have hcardPQ : Nat.card P = Nat.card Q := by
    simpa [P, N] using
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv)
  rcases (DefectSupport.subgroupCentralizerRestriction_ne_zero_iff
      (RelativeTransferBrauer.conjugationMap R N g B) Q).mp hRestrNe with
    ⟨x, hxCentral, hxCoeff⟩
  let ψ : N →* G := (MulAut.conj g).toMonoidHom.comp N.subtype
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp N.subtype_injective
  have hxRange : x ∈ Set.range ψ := by
    by_contra hxNot
    apply hxCoeff
    change Finsupp.mapDomain ψ B.coeff x = 0
    exact Finsupp.mapDomain_of_notMem_range B.coeff x hxNot
  rcases hxRange with ⟨n, rfl⟩
  have hnCoeff : B.coeff n ≠ 0 := by
    change Finsupp.mapDomain ψ B.coeff (ψ n) ≠ 0 at hxCoeff
    rw [Finsupp.mapDomain_apply hψinj] at hxCoeff
    exact hxCoeff
  have hnP : n ∈ Subgroup.centralizer (P : Set N) := by
    simpa [B, E, P, N] using
      normalizerAlgebraEmbedding_coeff_centralizes Q a n hnCoeff
  have hnQg : n ∈ Subgroup.centralizer (Qg : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    rcases hr with ⟨q, rfl⟩
    apply Subtype.ext
    change (g⁻¹ * (q : G) * g) * (n : G) =
      (n : G) * (g⁻¹ * (q : G) * g)
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hxCentral (q : G) q.property
    change (q : G) * (g * (n : G) * g⁻¹) =
      (g * (n : G) * g⁻¹) * (q : G) at hcomm
    calc
      (g⁻¹ * (q : G) * g) * (n : G) =
          g⁻¹ * ((q : G) * (g * (n : G) * g⁻¹)) * g := by
            group
      _ = g⁻¹ * ((g * (n : G) * g⁻¹) * (q : G)) * g := by
            rw [hcomm]
      _ = (n : G) * (g⁻¹ * (q : G) * g) := by
            group
  let : P.Normal := inferInstance
  have hSupP : IsPGroup 2 (P ⊔ Qg : Subgroup N) :=
    IsPGroup.to_sup_of_normal_left hP hQg
  have hnSup : n ∈ Subgroup.centralizer ((P ⊔ Qg : Subgroup N) : Set N) := by
    have hPcn : P ≤ Subgroup.centralizer ({n} : Set N) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hnP p hp
    have hQgcn : Qg ≤ Subgroup.centralizer ({n} : Set N) := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hnQg q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (sup_le hPcn hQgcn hr)
  have hSupSupport : DefectSupport.HasTwoCoefficientSupport B (P ⊔ Qg) :=
    ⟨hSupP, n, hnSup, hnCoeff⟩
  have hcardSup : Nat.card (P ⊔ Qg : Subgroup N) ≤ Nat.card P :=
    hMax.2 (P ⊔ Qg) hSupSupport
  have hPSup : P = P ⊔ Qg :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcardSup
  have hQgLeP : Qg ≤ P := by
    rw [hPSup]
    exact le_sup_right
  have hcardP_le_Qg : Nat.card P ≤ Nat.card Qg := by
    rw [hcardPQ, hcardQgQ]
  have hQgEqP : Qg = P :=
    Subgroup.eq_of_le_of_card_ge hQgLeP hcardP_le_Qg
  have hgInvN : g⁻¹ ∈ N := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.ext
    intro y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨q, hq, rfl⟩
      let qQ : Q := ⟨q, hq⟩
      have hqQg : φ qQ ∈ Qg := ⟨qQ, rfl⟩
      have hqP : φ qQ ∈ P := by
        rw [← hQgEqP]
        exact hqQg
      change (((φ qQ : N) : G)) ∈ Q at hqP
      simpa [φ, qQ] using hqP
    · intro hy
      let yN : N := ⟨y, Q.le_normalizer hy⟩
      have hyP : yN ∈ P := hy
      have hyQg : yN ∈ Qg := by
        rw [hQgEqP]
        exact hyP
      rcases hyQg with ⟨q, hqy⟩
      apply Subgroup.mem_map.mpr
      refine ⟨(q : G), q.property, ?_⟩
      have hqyG := congrArg (fun m : N ↦ (m : G)) hqy
      simpa [φ, yN] using hqyG
  have hgN : g ∈ N := by
    simpa using N.inv_mem hgInvN
  apply hcNe
  calc
    c = (QuotientGroup.mk g : G ⧸ N) := by
      exact (QuotientGroup.out_eq' c).symm
    _ = (QuotientGroup.mk (1 : G) : G ⧸ N) := by
      rw [QuotientGroup.eq]
      simpa using N.inv_mem hgN

end ModularBlock.BrauerThirdMain
