module
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer
public import Theory.ElementaryAbelian.Join

/-!
# Small two-subgroups and two-perfect actors

Adjoining a central natural subgroup makes the small subgroup invariant.
Its kernel commutator has order at most two, so it vanishes when the kernel
has no fixed points. A two-perfect actor on a subgroup of order at most four
has either trivial commutator or the whole subgroup as commutator.

The enlargement proofs adapt CyclicLocalization/Layer.lean; all normality
is inside the finite local group. Source: MS93 (4.3.2)(3), printed p.884.
-/
public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant

private theorem small_commutator {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) (hP : IsPGroup 2 P)
    (hAP : A ≤ P) (hn : P ≤ normalizer A) (hA : Nat.card A ≤ 4) :
    Nat.card (⁅A,P⁆ : Subgroup G) ≤ 2 := by
  have hKA : ⁅A,P⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hn
  by_cases hbot : A = ⊥
  · simp [hbot]
  have hne : ⁅A,P⁆ ≠ A := by
    intro heq
    let A₀ := A.subgroupOf P
    have hcomm : ⁅A₀, (⊤ : Subgroup P)⁆ = A₀ := by
      apply map_injective P.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map,
        range_subtype, heq]
    have hz : A₀ ≤ ⊥ := le_normal_of_quotient_isPGroup_of_eq_commutator
      A₀ ⊤ ⊥ (hP.to_quotient ⊥) hcomm
    have hh := congrArg (Subgroup.map P.subtype) (le_bot_iff.mp hz)
    rw [map_subgroupOf_eq_of_le hAP, Subgroup.map_bot] at hh
    exact hbot hh
  have hlt : Nat.card (⁅A,P⁆ : Subgroup G) < Nat.card A := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hKA h)
  rcases (hP.to_le (hKA.trans hAP)).card_eq_or_dvd with h | h <;> omega

private theorem normalizer_centralizes_small {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) (hD : Nat.card D ≤ 2) :
    normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  by_cases hsmall : Nat.card D ≤ 1
  · rw [eq_bot_of_card_le D hsmall]
    intro g _ x hx
    have hxone : x = 1 := hx
    simp [hxone]
  · have htwo : Nat.card D = 2 := by omega
    obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    intro g hg x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xD : D := ⟨x, hx⟩
    let yD : D := ⟨g * x * g⁻¹, (hg x).mp hx⟩
    have hyne : yD ≠ 1 := by
      intro hy
      apply hxone
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using hh
    have heq : yD = xD := (hzuniq yD hyne).trans (hzuniq xD (by
      intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have hh := congrArg (fun a : G => a * g) heq'
    simpa [mul_assoc] using hh.symm

/-- A commutator bound into Z makes AZ invariant under the component. -/
theorem sup_normal {G : Type*} [Group G] (A Z Q E : Subgroup G) [Z.Normal]
    (hgen : E ⊔ Q = ⊤) (hQE : Q ≤ normalizer A) (hAE : ⁅A,E⁆ ≤ Z) :
    (Z ⊔ A).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  refine sup_le ?_ ((le_inf le_normalizer_of_normal hQE).trans
    (normalizer_inf_normalizer_le_normalizer_sup Z A))
  rw [le_normalizer_iff]
  intro e he x hx
  have hm : (Z ⊔ A).map (MulAut.conj e).toMonoidHom ≤ Z ⊔ A := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨z,hz,rfl⟩
      exact (show Z ≤ Z ⊔ A from le_sup_left)
        ((mem_normalizer_iff.mp (show e ∈ normalizer Z from le_normalizer_of_normal (mem_top e)) z).mp hz)
    · rintro _ ⟨y,hy,rfl⟩
      change e * y * e⁻¹ ∈ Z ⊔ A
      have hc : ⁅e,y⁆ ∈ Z := hAE (by
        rw [commutator_comm]; exact commutator_mem_commutator he hy)
      rw [show e * y * e⁻¹ = ⁅e,y⁆ * y by simp [commutatorElement_def, mul_assoc]]
      exact (Z ⊔ A).mul_mem ((show Z ≤ Z ⊔ A from le_sup_left) hc) ((show A ≤ Z ⊔ A from le_sup_right) hy)
  exact hm (mem_map_of_mem _ hx)

/-- The small pairing's natural enlargement is centralized by Q. -/
theorem sup_centralizes_kernel {G : Type*} [Group G] [Finite G]
    (A Z Q E : Subgroup G) [Q.Normal] [Z.Normal] [(Z ⊔ A).Normal]
    (hAQ : A ≤ Q) (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer A) (hcard : Nat.card A ≤ 4)
    (hZcentral : Z ≤ centralizer (Q : Set G))
    (hfixed : Q ⊓ centralizer (E : Set G) = ⊥) :
    ⁅Z ⊔ A,Q⁆ = ⊥ := by
  have hcomm : ⁅Z ⊔ A,Q⁆ = ⁅A,Q⁆ := by
    rw [commutator_comm (Z ⊔ A), commutator_comm A]
    exact (commutator_eq_of_centralizing_sup rfl hZcentral
      (hAQ.trans Q.le_normalizer)).symm
  have hsmall : Nat.card (⁅Z ⊔ A,Q⁆ : Subgroup G) ≤ 2 := by
    rw [hcomm]
    exact small_commutator Q A hQ hAQ hQA hcard
  have hn : (⊤ : Subgroup G) ≤ normalizer (⁅Z ⊔ A,Q⁆ : Subgroup G) :=
    le_normalizer_of_normal
  have hc : ⁅Z ⊔ A,Q⁆ ≤ centralizer (E : Set G) :=
    (le_centralizer_iff.mp (hn.trans (normalizer_centralizes_small _ hsmall))).trans
      (centralizer_le le_top)
  apply le_bot_iff.mp
  rw [← hfixed]
  exact le_inf (commutator_le_right _ _) hc


/-- The nontrivial action of a two-perfect group on a small two-group is perfect. -/
theorem small_perfect_commutator_eq_or_bot {G : Type*} [Group G] [Finite G]
    (K T : Subgroup G) (hK : IsPGroup 2 K) (hT : IsPPerfect 2 T)
    (hn : T ≤ normalizer (K : Set G)) (hc : Nat.card K ≤ 4) :
    ⁅K,T⁆ = K ∨ ⁅K,T⁆ = ⊥ := by
  by_cases he : ⁅K,T⁆ = K
  · exact Or.inl he
  right
  have hle : ⁅K,T⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hn
  have hlt : Nat.card (⁅K,T⁆ : Subgroup G) < Nat.card K := by
    by_contra! h
    exact he (eq_of_le_of_card_ge hle h)
  have hsmall : Nat.card (⁅K,T⁆ : Subgroup G) ≤ 2 := by
    rcases (hK.to_le hle).card_eq_or_dvd with h | h <;> omega
  have hfix : ⁅⁅K,T⁆,T⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      ((normalizer_commutator_ge_right K T).trans
        (normalizer_centralizes_small _ hsmall))
  rw [← commutator_isPPerfect_idempotent T K hT hK hn]
  exact hfix

/-- Lift containment modulo a fixed kernel once the small action is nontrivial. -/
theorem small_le_of_image_le {G H : Type*} [Group G] [Finite G] [Group H]
    (q : G →* H) (K U T : Subgroup G) [U.Normal]
    (hK : IsPGroup 2 K) (hT : IsPPerfect 2 T)
    (hn : T ≤ normalizer (K : Set G)) (hc : Nat.card K ≤ 4)
    (himage : K.map q ≤ U.map q)
    (hfixed : q.ker ≤ centralizer (T : Set G))
    (hnoncentral : ¬ K.map q ≤ centralizer (T.map q : Set H)) : K ≤ U := by
  have hKU : K ≤ U ⊔ q.ker := by
    rw [← comap_map_eq]
    exact (le_comap_map q K).trans (comap_mono himage)
  have hcomm : ⁅K,T⁆ ≤ U := by
    let N := commutatorPreimage ⊤ T U
    have hUN : U ≤ N := le_commutatorPreimage le_top (commutator_le_left _ _)
    have hDN : q.ker ≤ N := le_commutatorPreimage le_top
      ((commutator_eq_bot_iff_le_centralizer.mpr hfixed).le.trans bot_le)
    exact (commutator_mono (hKU.trans (sup_le hUN hDN)) le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ T U le_normalizer_of_normal)
  rcases small_perfect_commutator_eq_or_bot K T hK hT hn hc with he | he
  · rwa [he] at hcomm
  · exfalso
    apply hnoncentral
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, he, Subgroup.map_bot]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant
