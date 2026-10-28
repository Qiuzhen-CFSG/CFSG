module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model

/-!
# The invariant line from the symmetric-linear quotient

An odd complement injects across a two-core. If its image lies in
S₅ × SL₃(2), the product order excludes the extraspecial alternative of
order 27, so it is elementary abelian of order nine. The kernel of its
first projection is nonzero because nine does not divide 120, and proper
because nine does not divide 168.

Every automorphism of the product preserves the second factor: simplicity
of SL₃(2) and its order 168 force every homomorphism SL₃(2) → S₅ to be
trivial. Thus the projection kernel is invariant. We map it through the
actual Frattini quotient and verify the action on representatives.

An ambient automorphism preserving the chosen local overgroup restricts
to that subgroup and descends through its characteristic two-core. The
last theorem constructs these maps and their compatibility. It remains
conditional on a local quotient isomorphism and preservation of that
local overgroup; neither is supplied by the existing max1 theorem.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). The intrinsic SL₃(2) facts and its
actual PSL₃(2) comparison are proved in the imported `Order168Models`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
private abbrev Sym5 := Equiv.Perm (Fin 5)
private abbrev Lin3 := SL(3, ZMod 2)
open Janko4.LocalStructure.SymmetricLinear
private theorem card_sym5 : Nat.card Sym5 = 120 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
private theorem card_lin3 : Nat.card Lin3 = 168 :=
  Atlas.Comparisons.Exceptional.sl3Two_card
private theorem hom_lin3_sym5 (f : Lin3 →* Sym5) : f = 1 := by
  let _ := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · have hd := card_dvd_of_injective f (f.ker_eq_bot_iff.mp h)
    rw [card_lin3, card_sym5] at hd
    norm_num at hd
  · exact MonoidHom.ker_eq_top_iff.mp h
private theorem preserves_second (c : MulAut QuotientModel) (x : QuotientModel)
    (hx : x.1 = 1) : (c x).1 = 1 := by
  have hf := hom_lin3_sym5
    ((MonoidHom.fst Sym5 Lin3).comp (c.toMonoidHom.comp (MonoidHom.inr Sym5 Lin3)))
  have he := DFunLike.congr_fun hf x.2
  change (c (1, x.2)).1 = 1 at he
  simpa only [← hx] using he

variable {G : Type*} [Group G] [Finite G]
/-- A compatible embedding supplies a proper nonzero Frattini subgroup for
the specified actor. No action of other pair automorphisms is required. -/
theorem invariantFrattiniSubgroup_of_embedding {R : Subgroup G}
    (D : Subgroup (MulAut R)) (hR : XiOddQuotient 3 R)
    (f : R →* QuotientModel) (hf : Function.Injective f)
    (ha : ∀ a ∈ D, ∃ c : MulAut QuotientModel,
      ∀ r : R, f (a r) = c (f r)) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ a ∈ D, ∀ x ∈ A, quotientAut (frattini R) a x ∈ A := by
  have hcard : Nat.card R = 9 := by
    have hd := card_dvd_of_injective f hf
    rw [Nat.card_prod, card_sym5, card_lin3] at hd
    rcases hR with ⟨_, he⟩ | ⟨_, he, _⟩
    · simpa using he
    · rw [he] at hd
      norm_num at hd
  have hE : IsElementaryAbelian 3 R := by
    rcases hR with ⟨hE, _⟩ | ⟨_, he, _⟩
    · exact hE
    · rw [hcard] at he
      norm_num at he
  let _ := hE
  let _ : Fact (IsPGroup 3 R) := ⟨hR.isPGroup⟩
  have hphi : frattini R = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := 3)
  let p : R →* Sym5 := (MonoidHom.fst Sym5 Lin3).comp f
  have hKb : p.ker ≠ ⊥ := by
    intro h
    have hd := card_dvd_of_injective p (p.ker_eq_bot_iff.mp h)
    rw [hcard, card_sym5] at hd
    norm_num at hd
  have hKt : p.ker ≠ ⊤ := by
    intro h
    have hp : ∀ r, (f r).1 = 1 := by
      intro r
      exact show r ∈ p.ker from h ▸ mem_top r
    let q : R →* Lin3 := (MonoidHom.snd Sym5 Lin3).comp f
    have hq : Function.Injective q := by
      intro x y hxy
      apply hf
      apply Prod.ext
      · rw [hp, hp]
      · exact hxy
    have hd := card_dvd_of_injective q hq
    rw [hcard, card_lin3] at hd
    norm_num at hd
  let q := QuotientGroup.mk' (frattini R)
  have hq : Function.Injective q := q.ker_eq_bot_iff.mp (by
    rw [QuotientGroup.ker_mk', hphi])
  refine ⟨p.ker.map q, ?_, ?_, ?_⟩
  · intro h
    apply hKb
    apply (map_injective hq)
    simpa using h
  · intro h
    apply hKt
    apply (map_injective hq)
    simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using h
  · rintro a ha' _ ⟨r, hr, rfl⟩
    rw [quotientAut_apply_mk]
    obtain ⟨c, hc⟩ := ha a ha'
    apply mem_map.mpr
    refine ⟨a r, ?_, rfl⟩
    change (f (a r)).1 = 1
    rw [hc]
    exact preserves_second c (f r) hr

/-- A common compatible embedding excludes every two-group in the pair automizer. -/
theorem pairReducible_of_embedding {S R : Subgroup G} (hR : XiOddQuotient 3 R)
    (f : R →* QuotientModel) (hf : Function.Injective f)
    (ha : ∀ a ∈ pairAutomizer S R, ∃ c : MulAut QuotientModel,
      ∀ r : R, f (a r) = c (f r)) : PairReducible S R := by
  intro D hD _
  exact invariantFrattiniSubgroup_of_embedding D hR f hf (fun a ha' => ha a (hD ha'))

omit [Finite G] in
private def restrictAut (M : Subgroup G) (b : MulAut G)
    (hb : ∀ x, b x ∈ M ↔ x ∈ M) : MulAut M where
  toFun x := ⟨b x, (hb x).mpr x.property⟩
  invFun x := ⟨b.symm x, (hb (b.symm x)).mp (by rw [b.apply_symm_apply]; exact x.property)⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x)
  right_inv x := Subtype.ext (b.apply_symm_apply x)
  map_mul' x y := Subtype.ext (b.map_mul x y)

omit [Finite G] in
private theorem preserves_right {R : Subgroup G} (a : MulAut R) (b : MulAut G)
    (he : ∀ r : R, (a r : G) = b r) (x : G) : b x ∈ R ↔ x ∈ R := by
  constructor
  · intro hx
    have hh := he (a.symm ⟨b x, hx⟩)
    have hy : b ((a.symm ⟨b x, hx⟩ : R) : G) = b x := by
      rw [← hh]
      exact congrArg Subtype.val (a.apply_symm_apply ⟨b x, hx⟩)
    exact b.injective hy ▸ (a.symm ⟨b x, hx⟩).property
  · intro hx
    rw [← he ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property

/-- Local lifts of the specified actor descend through the characteristic
two-core and preserve the constructed Frattini subgroup. -/
theorem invariantFrattiniSubgroup_of_localQuotient {R M : Subgroup G}
    (D : Subgroup (MulAut R))
    (hR : XiOddQuotient 3 R) (hRM : R ≤ M)
    (e : (M ⧸ pCore 2 M) ≃* QuotientModel)
    (ha : ∀ a ∈ D, ∃ c : MulAut M,
      ∀ r : R, inclusion hRM (a r) = c (inclusion hRM r)) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ a ∈ D, ∀ x ∈ A, quotientAut (frattini R) a x ∈ A := by
  let i := inclusion hRM
  let q := QuotientGroup.mk' (pCore 2 M)
  let f := e.toMonoidHom.comp (q.comp i)
  have hd : Disjoint (R.subgroupOf M) (pCore 2 M) :=
    IsPGroup.disjoint_of_coprime
      (hR.isPGroup.of_equiv (subgroupOfEquivOfLe hRM).symm)
      pCore_isPGroup (by decide : Nat.Coprime 3 2)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro r hr
    have hfr : e (q (i r)) = 1 := hr
    have hqr : q (i r) = 1 := e.injective (by simpa only [map_one] using hfr)
    have hi : i r ∈ pCore 2 M := (QuotientGroup.eq_one_iff (i r)).mp hqr
    have hir : i r ∈ R.subgroupOf M := r.property
    have hr1 := disjoint_def.mp hd hir hi
    exact mem_bot.mpr ((inclusion_injective hRM) (by simpa only [map_one] using hr1))
  apply invariantFrattiniSubgroup_of_embedding D hR f hf
  intro a ha'
  obtain ⟨c, hc⟩ := ha a ha'
  refine ⟨(e.symm.trans (quotientAut (pCore 2 M) c)).trans e, fun r => ?_⟩
  change e (q (i (a r))) = e (quotientAut (pCore 2 M) c (e.symm (e (q (i r)))))
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  congr 1
  congr 1
  exact hc r

/-- An invariant local overgroup with the specified two-core quotient gives
the required Frattini subgroup. The local existence and invariance hypotheses
are explicit; this theorem does not construct a J₄ local overgroup. -/
theorem pairReducible_of_localQuotient {S R M : Subgroup G}
    (hR : XiOddQuotient 3 R) (hRM : R ≤ M)
    (e : (M ⧸ pCore 2 M) ≃* QuotientModel)
    (hM : ∀ b : MulAut G, (∀ x, b x ∈ S ↔ x ∈ S) →
      (∀ x, b x ∈ R ↔ x ∈ R) → ∀ x, b x ∈ M ↔ x ∈ M) :
    PairReducible S R := by
  intro D hD _
  apply invariantFrattiniSubgroup_of_localQuotient D hR hRM e
  intro a ha
  obtain ⟨b, hb, he⟩ := hD ha
  exact ⟨restrictAut M b (hM b hb (preserves_right a b he)),
    fun r => Subtype.ext (he r)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
