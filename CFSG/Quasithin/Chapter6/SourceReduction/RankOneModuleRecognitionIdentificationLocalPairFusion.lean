module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairAction

/-!
# Internal conjugacy of the non-two pair

The two nonidentity involution images are conjugate in the actual symmetric
three action. Transporting their exact fixed planes conjugates the two
order-eight normalizer intersections inside the generated group. Pulling a
common hyperplane back to the original natural layer and applying 6.2.5(6)
then conjugates the whole layers inside that same group. This retains the
internal conjugator needed to remove the central action kernel in 6.2.6.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem symmetricThree_involution_conjugate (a b : Equiv.Perm (Fin 3))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ k, k * a * k⁻¹ = b := by
  have hh : ∀ a b : Equiv.Perm (Fin 3), a ^ 2 = 1 → b ^ 2 = 1 →
      a ≠ 1 → b ≠ 1 → ∃ k, k * a * k⁻¹ = b := by decide +kernel
  exact hh a b ha hb ha1 hb1

omit [Finite G] in
private theorem image_involution_conjugate
    {F : Type*} [Group F] (f : G →* F) (e : f.range ≃* Equiv.Perm (Fin 3))
    (x y : G) (hx : (f x)^2=1) (hy : (f y)^2=1)
    (hx1 : f x ≠ 1) (hy1 : f y ≠ 1) :
    ∃ k : G, f (k * x * k⁻¹) = f y := by
  let a : f.range := ⟨f x, ⟨x,rfl⟩⟩
  let b : f.range := ⟨f y, ⟨y,rfl⟩⟩
  obtain ⟨k, hk⟩ := symmetricThree_involution_conjugate (e a) (e b)
    (by rw [← map_pow, show a^2=1 from Subtype.ext hx, map_one])
    (by rw [← map_pow, show b^2=1 from Subtype.ext hy, map_one])
    (by intro he; exact hx1 (congrArg Subtype.val (e.injective (he.trans e.map_one.symm))))
    (by intro he; exact hy1 (congrArg Subtype.val (e.injective (he.trans e.map_one.symm))))
  obtain ⟨k', hk'⟩ := (e.symm k).property
  refine ⟨k', ?_⟩
  have he : (e.symm k) * a * (e.symm k)⁻¹ = b := by
    apply e.injective
    simpa only [map_mul, map_inv, e.apply_symm_apply] using hk
  have hev := congrArg Subtype.val he
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk', map_mul, map_inv] using hev

private theorem quotientAut_eq_of_wreath_eq
    {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)
    (a b : MulAut Q) (he : d.quotientWreathAction a = d.quotientWreathAction b) :
    quotientAut (center Q) a = quotientAut (center Q) b := by
  apply inv_mul_eq_one.mp
  rw [← map_inv, ← map_mul]
  apply (d.quotientWreathAction_eq_one_iff _).mp
  rw [map_mul, map_inv, he, inv_mul_cancel]

private theorem fixed_plane_transport
    (J Q U F : Subgroup G) (hn : J ≤ normalizer (Q : Set G))
    (d : QuaternionCentralProductData Q) (hUQ : U ≤ Q)
    (x y k : J)
    (hconj : seedOrthogonalAction J Q hn d (k*x*k⁻¹) =
      seedOrthogonalAction J Q hn d y)
    (hfixU : ∀ q : Q, quotientAut (center Q) (seedConjugation J Q hn x)
      (QuotientGroup.mk' (center Q) q) = QuotientGroup.mk' (center Q) q ↔ (q : G) ∈ U)
    (hfixF : ∀ q : Q, quotientAut (center Q) (seedConjugation J Q hn y)
      (QuotientGroup.mk' (center Q) q) = QuotientGroup.mk' (center Q) q ↔ (q : G) ∈ F) :
    U.map (MulAut.conj (k : G)).toMonoidHom ≤ F := by
  let α := seedConjugation J Q hn
  let β := (quotientAut (center Q)).comp α
  have he : β (k*x*k⁻¹) = β y := quotientAut_eq_of_wreath_eq d _ _ hconj
  rintro u ⟨q, hq, rfl⟩
  let qQ : Q := ⟨q,hUQ hq⟩
  have hqfix : β x (QuotientGroup.mk' (center Q) qQ) =
      QuotientGroup.mk' (center Q) qQ := (hfixU qQ).mpr hq
  change (α k qQ : G) ∈ F
  apply (hfixF (α k qQ)).mp
  change β y (QuotientGroup.mk' (center Q) (α k qQ)) = _
  rw [← quotientAut_apply_mk]
  change β y (β k (QuotientGroup.mk' (center Q) qQ)) =
    β k (QuotientGroup.mk' (center Q) qQ)
  rw [← he, map_mul, map_mul, map_inv]
  change β k (β x ((β k)⁻¹ (β k (QuotientGroup.mk' (center Q) qQ)))) = _
  rw [show (β k)⁻¹ (β k (QuotientGroup.mk' (center Q) qQ)) = QuotientGroup.mk' (center Q) qQ from (β k).symm_apply_apply _, hqfix]

variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The two layer hyperplanes, and hence the layers, are conjugate inside their join. -/
theorem local_non_two_pair_internal_conjugacy
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    ∃ k ∈ B ⊔ A,
      (B ⊓ normalizer (A : Set G)).map (MulAut.conj k).toMonoidHom =
        A ⊓ normalizer (B : Set G) ∧
      B.map (MulAut.conj k).toMonoidHom = A := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let J := B ⊔ A
  let Q := localPairCore B A
  let U := B ⊓ normalizer (A : Set G)
  let F := A ⊓ normalizer (B : Set G)
  obtain ⟨hn, d, hK, hB, hA, hsing, hfixB, hfixA⟩ :=
    local_non_two_pair_outer_action h hnatural hE g hleft hright hnon
  obtain ⟨hn', d', hK', ⟨e'⟩⟩ :=
    local_non_two_pair_outer_symmetricThree h hnatural hE g hleft hright hnon
  let f := seedOrthogonalAction J Q hn d
  let f' := seedOrthogonalAction J Q hn' d'
  have heK : f.ker = f'.ker :=
    map_injective J.subtype_injective (hK.trans hK'.symm)
  let e : f.range ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq heK).trans
        ((QuotientGroup.quotientKerEquivRange f').trans e'))
  obtain ⟨b, hb1, _⟩ := (Nat.card_eq_two_iff' (1 : (B.subgroupOf J).map f)).mp hB
  obtain ⟨a, ha1, _⟩ := (Nat.card_eq_two_iff' (1 : (A.subgroupOf J).map f)).mp hA
  obtain ⟨x, hx, hxb⟩ := b.property
  obtain ⟨y, hy, hya⟩ := a.property
  have hx1 : f x ≠ 1 := fun he => hb1 (Subtype.ext (hxb.symm.trans he))
  have hy1 : f y ≠ 1 := fun he => ha1 (Subtype.ext (hya.symm.trans he))
  obtain ⟨k, hk⟩ := image_involution_conjugate f e x y
    (hsing x (Or.inl hx)).1 (hsing y (Or.inr hy)).1 hx1 hy1
  have hUF : U.map (MulAut.conj (k : G)).toMonoidHom ≤ F :=
    fixed_plane_transport J Q U F hn d le_sup_left x y k hk
      (hfixB x hx hx1).2 (hfixA y hy hy1).2
  have hUcard : Nat.card U = 8 := by
    have hh := (U.subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show U ≤ B from inf_le_left)).toEquiv] at hh
    change Nat.card U * U.relIndex B = Nat.card B at hh
    rw [hleft, hnatural.2.1.card] at hh
    omega
  have hFcard : Nat.card F = 8 := by
    have hh := (F.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show F ≤ A from inf_le_left)).toEquiv] at hh
    change Nat.card F * F.relIndex A = Nat.card A at hh
    have hAc : Nat.card A = 16 := (card_map_of_injective (MulAut.conj g).injective).trans hnatural.2.1.card
    rw [hright, hAc] at hh
    omega
  have heUF : U.map (MulAut.conj (k : G)).toMonoidHom = F :=
    eq_of_le_of_card_ge hUF (by rw [card_map_of_injective (MulAut.conj (k : G)).injective, hUcard, hFcard])
  refine ⟨(k : G), k.property, heUF, ?_⟩
  have hFBk : F ≤ B.map (MulAut.conj (k : G)).toMonoidHom :=
    heUF ▸ map_mono (show U ≤ B from inf_le_left)
  have hback : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ B := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (show F ≤ A from inf_le_left)
    rwa [fusion_map_conj_inverse] at hh
  have hbackk : F.map (MulAut.conj g⁻¹).toMonoidHom ≤
      B.map (MulAut.conj (g⁻¹ * (k : G))).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hFBk
    rwa [fusion_map_conj_mul] at hh
  have hcard := card_le_of_le (le_inf hback hbackk)
  rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hFcard] at hcard
  have he := local_hyperplane_unique h hnatural hE (g⁻¹ * (k : G)) hcard
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [fusion_map_conj_mul] at hh
  simpa only [mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
