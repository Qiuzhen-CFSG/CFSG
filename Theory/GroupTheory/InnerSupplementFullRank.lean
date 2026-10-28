module
public import Theory.GroupTheory.RankOneInnerSplitting
/-!
# Inner supplements at full prime rank

Suppose a centerless normal subgroup B already has the ambient p-rank.
An inner-acting supplement A with elementary A/O_q(A) lies in B when
O_q of the ambient group vanishes and a subgroup normalizing A completes
the generation. Indeed the centralizing factor of BA is normal, has
trivial q-core, and is an elementary image of A. Independence from B
forces its p-rank to vanish.

Source application: Aschbacher--Smith 12.6.31, printed p.836,
refs/quasithin.pdf, for the normal symplectic and G₂ components.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {J : Type*} [Group J] [Finite J]

/-- The centralizing coordinate of the inner supplement vanishes by rank. -/
theorem inner_supplement_le_of_full_prime_rank (A B T : Subgroup J) [B.Normal]
    {p q r : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p (A ⧸ pCore q A)]
    (hzero : pCore q J = ⊥) (hz : center B = ⊥)
    (hr : r ≤ primeRank p B) (hJ : primeRank p J ≤ r)
    (hinner : A ≤ B ⊔ centralizer (B : Set J))
    (hnA : T ≤ normalizer (A : Set J)) (hgen : B ⊔ A ⊔ T = ⊤) : A ≤ B := by
  let N := B ⊔ A
  let D := N ⊓ centralizer (B : Set J)
  have hnN : N.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hgen]
    exact sup_le N.le_normalizer
      ((le_inf (le_normalizer_of_normal : T ≤ normalizer (B : Set J)) hnA).trans
        (normalizer_inf_normalizer_le_normalizer_sup B A))
  let _ := hnN
  let : D.Normal := inferInstance
  have hDzero : pCore q D = ⊥ := by
    rw [pCore_eq_comap_of_normal,hzero,MonoidHom.comap_bot]
    exact D.subtype.ker_eq_bot D.subtype_injective
  have hBD : Disjoint B D := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hc : (⟨x,hx.1⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext (hx.2.2 b b.property)
    exact mem_bot.mpr (congrArg (fun b : B => b.val) (show (⟨x,hx.1⟩ : B) = 1 from mem_bot.mp (hz ▸ hc)))
  have hBC : B ≤ centralizer (D : Set J) := le_centralizer_iff.mp inf_le_right
  have hND : B ⊔ D = N := by
    apply le_antisymm (sup_le le_sup_left inf_le_left)
    apply sup_le le_sup_left
    intro x hx
    obtain ⟨b,hb,c,hc,hbc⟩ := mem_sup_of_normal_left.mp (hinner hx)
    have hcN : c ∈ N := by
      have hh := N.mul_mem (N.inv_mem (mem_sup_left hb)) (mem_sup_right hx)
      rwa [←hbc,inv_mul_cancel_left] at hh
    rw [←hbc]
    exact mul_mem_sup hb ⟨hcN,hc⟩
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B D hBD hBC
  let eN : B × D ≃* N := e.trans (MulEquiv.subgroupCongr hND)
  have heN (b : B) (d : D) : (eN (b,d) : J) = (b : J) * d := he b d
  let π : N →* D := (MonoidHom.snd B D).comp eN.symm.toMonoidHom
  have hπ (b : B) (d : D) : π (eN (b,d)) = d := by
    change (eN.symm (eN (b,d))).2 = d
    rw [eN.symm_apply_apply]
  let f : A →* D := π.comp (inclusion (le_sup_right : A ≤ N))
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨b,hb,a,ha,hba⟩ := mem_sup_of_normal_left.mp d.property.1
    let b' : B := ⟨b,hb⟩
    let a' : A := ⟨a,ha⟩
    have hmul : eN (b',1) * inclusion (le_sup_right : A ≤ N) a' = eN (1,d) := by
      apply Subtype.ext
      change (eN (b',1) : J) * a = (eN (1,d) : J)
      rw [heN,heN]
      simpa only [OneMemClass.coe_one,mul_one,one_mul] using hba
    have hh := congrArg π hmul
    rw [map_mul,hπ,hπ,one_mul] at hh
    exact ⟨a',hh⟩
  have hk : pCore q A ≤ f.ker := by
    have hm : (pCore q A).map f ≤ pCore q D :=
      le_sSup ⟨(inferInstance : (pCore q A).Normal).map f hf,pCore_isPGroup.map f⟩
    intro a ha
    exact mem_bot.mp (hDzero ▸ hm (mem_map_of_mem f ha))
  let : IsElementaryAbelian p D := IsElementaryAbelian.of_surjective
    (QuotientGroup.lift (pCore q A) f hk)
    (QuotientGroup.lift_surjective_of_surjective _ f hf hk)
  have hbound := primeRank_subgroup_le p (B ⊔ D)
  rw [B.primeRank_sup_eq_add_of_disjoint_commuting D hBD hBC] at hbound
  have hD : primeRank p D ≤ 0 := by omega
  have hc := (primeRank_le_iff_elementary_card_le D).mp hD ⊤
    (IsElementaryAbelian.of_injective (⊤ : Subgroup D).subtype Subtype.val_injective)
  rw [card_top,pow_zero] at hc
  have hbot : D = ⊥ := (eq_bot_iff_card D).mpr (Nat.le_antisymm hc Nat.card_pos)
  rw [hbot,sup_bot_eq] at hND
  exact hND.symm ▸ (le_sup_right : A ≤ N)
end Theory.GroupTheory
