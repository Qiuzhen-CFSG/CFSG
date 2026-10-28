module
public import Theory.GroupTheory.RankOneCentralizingCubic
public import Theory.ElementaryAbelian.Quotient
/-!
# Splitting an inner supplement over a rank-one subgroup

Let B be centerless of p-rank one in a finite group J of p-rank at most
two. Suppose A acts on B by inner automorphisms, A/O_q(A) is elementary
abelian of characteristic p, and O_q(J)=1. If a normalizing supplement T
generates J with B and A, a nontrivial C_A(B) forces
A=(A intersect B) times C_A(B).

Indeed D=(BA) intersect C_J(B) is normal in J. The inner-action product
projection maps A onto D. Its q-core vanishes, so D is elementary; the
rank bound makes both D and its nontrivial subgroup C_A(B) have order p.
Thus D=C_A(B), and both coordinates of every element of A belong to A.

Source application: Aschbacher--Smith 12.6.31, printed p.836,
refs/quasithin.pdf, the original normal rank-one component splitting.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {J : Type*} [Group J] [Finite J]

/-- The actual inner supplement is the product of its two original intersections. -/
theorem split_inner_supplement_of_elementary_core_quotient (A B T : Subgroup J) [B.Normal]
    {p q : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p (A ⧸ pCore q A)]
    (hzero : pCore q J = ⊥) (hz : center B = ⊥)
    (hr : primeRank p B = 1) (hJ : primeRank p J ≤ 2)
    (hinner : A ≤ B ⊔ centralizer (B : Set J))
    (hnA : T ≤ normalizer (A : Set J)) (hgen : B ⊔ A ⊔ T = ⊤)
    (hne : A ⊓ centralizer (B : Set J) ≠ ⊥) :
    A = (A ⊓ B) ⊔ (A ⊓ centralizer (B : Set J)) := by
  let N := B ⊔ A
  let C := A ⊓ centralizer (B : Set J)
  let D := N ⊓ centralizer (B : Set J)
  have hCD : C ≤ D := inf_le_inf_right _ le_sup_right
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
  let : IsElementaryAbelian p C := IsElementaryAbelian.of_injective
    (inclusion hCD) (inclusion_injective hCD)
  have hDne : D ≠ ⊥ := fun h => hne (bot_unique (hCD.trans h.le))
  have hDc : Nat.card D = p := centralizing_elementary_card_prime B D hz hr hJ inf_le_right hDne
  have hCc : Nat.card C = p := centralizing_elementary_card_prime B C hz hr hJ inf_le_right hne
  have hDC : D = C := (eq_of_le_of_card_ge hCD (by rw [hCc,hDc])).symm
  apply le_antisymm
  · intro a ha
    have han : a ∈ B ⊔ D := hND.symm ▸ (mem_sup_right ha : a ∈ N)
    obtain ⟨b,hb,c,hc,hbc⟩ := mem_sup_of_normal_left.mp han
    have hcC : c ∈ C := hDC ▸ hc
    have hbA : b ∈ A := by
      have hh := A.mul_mem ha (A.inv_mem hcC.1)
      rwa [←hbc,mul_inv_cancel_right] at hh
    rw [←hbc]
    exact mul_mem_sup ⟨hbA,hb⟩ hcC
  · exact sup_le inf_le_left inf_le_left
end Theory.GroupTheory
