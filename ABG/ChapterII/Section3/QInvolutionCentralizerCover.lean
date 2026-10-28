module
public import ABG.ChapterII.Section3.QSylowGeometry
public import ABG.ChapterII.Section3.SylowCenter
public import Theory.GroupTheory.PPrimeCoreSupplement

/-!
# The Q-group odd-core quotient inside an involution centralizer

For an arbitrary Q-subgroup K of a finite group H, there is an involution
x of H and a subgroup M of K which surjects onto K/O(K) and embeds in
C_H(x). No ambient QD hypothesis or stronger Sylow shape is required.

Choose x in the nontrivial center of a Sylow two-subgroup R of K, using
the proved enlarged-Q geometry. Proposition 1 says that M=C_K(Z(R))
supplements the odd core. The supplement quotient equivalence gives the
surjection, and centralizing Z(R) gives the actual centralizer embedding.
Together with the generic section-lifting theorem, this transports every
section of any quotient of K/O(K) into an involution centralizer of H.
This is the reduction in ABG II.3 Lemma 2, article page 24.
-/

namespace ABG
universe u

public theorem qGroup_oddCore_quotient_centralizer_cover
    {H : Type u} [Group H] [Finite H] (K : Subgroup H) (hK : IsQGroup K) :
    ∃ x : H, orderOf x = 2 ∧ ∃ M : Subgroup K,
      ∃ q : M →* (K ⧸ pPrimeCore 2 K), Function.Surjective q ∧
      ∃ i : M →* Subgroup.centralizer {x}, Function.Injective i := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Sylow 2 K := Classical.choice inferInstance
  have hgeo := qGroup_sylow_center_quotient_geometry hK R
  let : Nontrivial (Subgroup.center R) := hgeo.2.1
  have htwo := R.isPGroup'.to_subgroup (Subgroup.center R)
  have hdvd : 2 ∣ Nat.card (Subgroup.center R) := by
    rcases htwo.card_eq_or_dvd with h | h
    · exact (Finite.one_lt_card.not_ge h.le).elim
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2 hdvd
  let x : H := ((z : R) : K)
  have hx : orderOf x = 2 := by
    simpa only [x, Subgroup.orderOf_coe] using hz
  let Z := subgroupCenter (R : Subgroup K)
  let M := Subgroup.centralizer (Z : Set K)
  have hM : pPrimeCore 2 K ⊔ M = ⊤ :=
    qGroup_eq_oddCore_mul_sylowCenterCentralizer hK R
  obtain ⟨_, ⟨e⟩⟩ := M.quotient_pPrimeCore_equiv_of_sup_eq_top 2 hM
  let q : M →* (K ⧸ pPrimeCore 2 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 M))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hzZ : ((z : R) : K) ∈ Z := ⟨(z : R), z.property, rfl⟩
  let f : M →* H := K.subtype.comp M.subtype
  have hf : Function.Injective f := K.subtype_injective.comp M.subtype_injective
  have hfc : ∀ m : M, f m ∈ Subgroup.centralizer {x} := by
    intro m
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp m.property _ hzZ)).symm
  exact ⟨x, hx, M, q, hq, f.codRestrict _ hfc,
    fun a b h => hf (congrArg (fun c : Subgroup.centralizer {x} => (c : H)) h)⟩

end ABG
