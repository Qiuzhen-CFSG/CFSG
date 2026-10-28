module

public import Theory.GroupTheory.PStar.Supplement
public import Theory.GroupAction.CentralKernelFixedResidual.Family
public import Theory.GroupAction.PrimeGroupFixedImage
public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# The coprime and central kernel cases of p-star extension

An odd kernel lifts Sylow centralizers. Its elements lie in the product of
any normal subgroup M and the centralizer of a Sylow subgroup of M: apply
the same lifting theorem modulo the intersection with M. For a central
p-kernel, lift only the residual of the quotient centralizer and use
centrality to absorb the kernel.

Source: GLS II, Chapter B, Lemma 5.3, first assertion and the central
p-kernel case of its proof. All residuals here are O^p.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {p : ℕ} {G H : Type*} [Group G] [Group H] [Finite G] [Fact p.Prime]

/-- The defining supplement in a surjective image, retaining the original
normal subgroup and its original Sylow subgroup. -/
theorem IsPStar.sup_image_centralizer_eq_top (hH : IsPStar p H)
    (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup G) [M.Normal] (P : Sylow p M) :
    M.map f ⊔ centralizer (((P : Subgroup M).map M.subtype).map f : Set H) = ⊤ := by
  let : (M.map f).Normal := Normal.map inferInstance f hf
  let P' := P.mapSurjective (f.subgroupMap_surjective M)
  have he : (P' : Subgroup (M.map f)).map (M.map f).subtype =
      ((P : Subgroup M).map M.subtype).map f := by
    simp only [P', Sylow.coe_mapSurjective, map_map]
    rfl
  simpa only [he] using hH.2 (M.map f) P'

/-- The residual form of the image supplement. -/
theorem IsPStar.sup_image_centralizer_pResidual_eq_top (hH : IsPStar p H)
    (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup G) [M.Normal] (P : Sylow p M) :
    M.map f ⊔ (pResidual p (centralizer
      (((P : Subgroup M).map M.subtype).map f : Set H))).map
        (centralizer (((P : Subgroup M).map M.subtype).map f : Set H)).subtype = ⊤ := by
  let : Finite H := Finite.of_surjective f hf
  let : (M.map f).Normal := Normal.map inferInstance f hf
  exact sup_embedded_pResidual_eq_top ((pResidual_eq_top_iff p H).mp hH.1)
    (M.map f) _ (hH.sup_image_centralizer_eq_top f hf M P)

/-- A normal prime-to-p subgroup is absorbed by every normal Sylow-centralizer
supplement. -/
theorem coprime_normal_le_sup_centralizer (N M : Subgroup G) [N.Normal] [M.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQM : Q ≤ M) : N ≤ M ⊔ centralizer (Q : Set G) := by
  let K := M ⊓ N
  let q := QuotientGroup.mk' K
  have hker : ¬ p ∣ Nat.card q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (hN.of_dvd_right (card_dvd_of_le (show K ≤ N from inf_le_right)))
  have hcomm : ⁅N.map q, M.map q⁆ = ⊥ := by
    rw [← map_commutator]
    apply bot_unique
    have hc : ⁅N, M⁆ ≤ K := le_inf (commutator_le_right N M) (commutator_le_left N M)
    exact (map_mono hc).trans_eq (QuotientGroup.map_mk'_self K)
  have hcent : N.map q ≤ centralizer (Q.map q : Set (G ⧸ K)) :=
    (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (centralizer_le (map_mono hQM))
  have hlift := centralizer_map_of_prime_free_kernel q
    (QuotientGroup.mk'_surjective K) hker Q hQ
  intro n hn
  have hnq := hcent (mem_map_of_mem q hn)
  rw [← hlift] at hnq
  obtain ⟨c, hc, hcn⟩ := hnq
  have hdiff : c⁻¹ * n ∈ M := (QuotientGroup.eq.mp hcn).1
  have hmem := (M ⊔ centralizer (Q : Set G)).mul_mem
    (mem_sup_right hc) (mem_sup_left hdiff)
  simpa only [mul_inv_cancel_left] using hmem

/-- Prime-to-p kernels lift the p-star condition. -/
theorem isPStar_of_surjective_coprime_kernel (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker)) (hH : IsPStar p H) : IsPStar p G := by
  have hkR : f.ker ≤ pResidual p G := le_pResidual_of_isPPerfect f.ker
    ((pResidual_eq_top_iff p f.ker).mp (isPStar_of_coprime_card hker).1)
  have hR : pResidual p G = ⊤ := by
    have hr := congrArg (comap f) ((map_pResidual_of_surjective p f hf).trans hH.1)
    simpa only [comap_map_eq, sup_eq_left.mpr hkR, comap_top] using hr
  refine ⟨hR, ?_⟩
  intro M _ P
  let Q := (P : Subgroup M).map M.subtype
  have hQ : IsPGroup p Q := P.isPGroup'.map M.subtype
  have hlift := centralizer_map_of_prime_free_kernel f hf
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hker) Q hQ
  have hgen := hH.sup_image_centralizer_eq_top f hf M P
  change M.map f ⊔ centralizer (Q.map f : Set H) = ⊤ at hgen
  rw [← hlift, ← Subgroup.map_sup] at hgen
  have h := congrArg (comap f) hgen
  have hk : f.ker ≤ M ⊔ centralizer (Q : Set G) :=
    coprime_normal_le_sup_centralizer f.ker M hker Q hQ (map_subtype_le _)
  simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using h

/-- The first assertion of GLS II 5.3, for every prime and thus for p = 2. -/
theorem isPStar_of_quotient_pPrimeCore (h : IsPStar p (G ⧸ pPrimeCore p G)) :
    IsPStar p G :=
  isPStar_of_surjective_coprime_kernel (QuotientGroup.mk' (pPrimeCore p G))
    (QuotientGroup.mk'_surjective _) (by
      simpa only [QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := p) (G := G))) h

/-- A p-perfect central extension by a p-group of a p-star group is p-star.
The residual lifting theorem is applied to the whole Sylow subgroup. -/
theorem isPStar_of_surjective_central_pgroup_kernel (hG : IsPPerfect p G)
    (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker) (hH : IsPStar p H) :
    IsPStar p G := by
  refine ⟨(pResidual_eq_top_iff p G).mpr hG, ?_⟩
  intro M _ P
  let Q := (P : Subgroup M).map M.subtype
  let C := centralizer (Q : Set G)
  have hgen := hH.sup_image_centralizer_pResidual_eq_top f hf M P
  change M.map f ⊔ (pResidual p (centralizer (Q.map f : Set H))).map
    (centralizer (Q.map f : Set H)).subtype = ⊤ at hgen
  rw [← map_embedded_centralizer_pResidual_of_central_pgroup_ker p f hf hc hp Q,
    ← Subgroup.map_sup] at hgen
  have hcover : (M ⊔ C).map f = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact map_mono (sup_le_sup_left (map_subtype_le _) M)
  have hk : f.ker ≤ M ⊔ C := hc.trans ((center_le_centralizer _).trans le_sup_right)
  have h := congrArg (comap f) hcover
  simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using h

end Theory.GroupTheory
