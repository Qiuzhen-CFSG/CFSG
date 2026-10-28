module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Automizer

/-!
# Transporting a Sylow pair through a central model map

Projection to Q/Z(Q), followed by an actual model isomorphism, is injective
on a subgroup disjoint from the center. The same map transports the genuine
Sylow subgroup and every extendible pair automorphism. Finally the induced
Frattini-quotient isomorphism transports an involution and its two power orbits.
No injectivity on the Sylow subgroup is required.

This is the transport step in the binary PSL₃ case of Aschbacher–Smith,
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
universe u v
variable {Q : Type u} [Group Q] {H : Type v} [Group H]

/-- The actual projection followed by a chosen model isomorphism. -/
def centralModelMap (e : (Q ⧸ center Q) ≃* H) : Q →* H :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center Q))

theorem centralModelMap_surjective (e : (Q ⧸ center Q) ≃* H) :
    Function.Surjective (centralModelMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem centralModelMap_ker (e : (Q ⧸ center Q) ≃* H) :
    (centralModelMap e).ker = center Q := by
  ext x
  change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff x

/-- Disjointness from the center makes the projection injective on R. -/
theorem centralModelMap_injective_on (e : (Q ⧸ center Q) ≃* H)
    (R : Subgroup Q) (hd : Disjoint R (center Q)) :
    Function.Injective ((centralModelMap e).subgroupMap R) := by
  intro x y hxy
  apply Subtype.ext
  apply inv_mul_eq_one.mp
  apply hd.le_bot
  refine ⟨R.mul_mem (R.inv_mem x.property) y.property, ?_⟩
  rw [← centralModelMap_ker e]
  change centralModelMap e ((x : Q)⁻¹ * y) = 1
  have he := congrArg Subtype.val hxy
  change centralModelMap e (x : Q) = centralModelMap e (y : Q) at he
  rw [map_mul, map_inv, he, inv_mul_cancel]

/-- A genuine multiplicative equivalence with the projected complement. -/
noncomputable def centralImageEquiv (e : (Q ⧸ center Q) ≃* H)
    (R : Subgroup Q) (hd : Disjoint R (center Q)) :
    R ≃* R.map (centralModelMap e) :=
  MulEquiv.ofBijective ((centralModelMap e).subgroupMap R)
    ⟨centralModelMap_injective_on e R hd, (centralModelMap e).subgroupMap_surjective R⟩

@[simp] theorem centralImageEquiv_apply (e : (Q ⧸ center Q) ≃* H)
    (R : Subgroup Q) (hd : Disjoint R (center Q)) (r : R) :
    (centralImageEquiv e R hd r : H) = centralModelMap e r := rfl

/-- The image remains Sylow, even if the central projection has a kernel on S. -/
noncomputable def centralImageSylow [Finite Q] (e : (Q ⧸ center Q) ≃* H) (S : Sylow 2 Q) :
    Sylow 2 H := S.mapSurjective (centralModelMap_surjective e)

@[simp] theorem coe_centralImageSylow [Finite Q] (e : (Q ⧸ center Q) ≃* H) (S : Sylow 2 Q) :
    (centralImageSylow e S : Subgroup H) = (S : Subgroup Q).map (centralModelMap e) := rfl

/-- Normalization descends through the same projection. -/
theorem centralImage_normalizes [Finite Q] (e : (Q ⧸ center Q) ≃* H)
    (S : Sylow 2 Q) (R : Subgroup Q) (hn : R ≤ normalizer (S : Subgroup Q)) :
    R.map (centralModelMap e) ≤ normalizer (centralImageSylow e S : Subgroup H) :=
  (map_mono hn).trans ((S : Subgroup Q).le_normalizer_map (centralModelMap e))

private theorem preserves_image (f : Q →* H) (b : MulAut Q) (c : MulAut H)
    (hf : ∀ x, f (b x) = c (f x)) (S : Subgroup Q)
    (hb : ∀ x, b x ∈ S ↔ x ∈ S) (y : H) :
    c y ∈ S.map f ↔ y ∈ S.map f := by
  constructor
  · rintro ⟨x,hx,hxy⟩
    refine ⟨b.symm x, (hb _).mp (by simpa using hx), ?_⟩
    apply c.injective
    rw [← hf, b.apply_symm_apply, hxy]
  · rintro ⟨x,hx,rfl⟩
    exact ⟨b x, (hb x).mpr hx, hf x⟩

/-- Every extendible pair automorphism descends through the central quotient.
The extension is transported on the ambient group, not merely on a family tag. -/
theorem centralImage_pairAutomizer (e : (Q ⧸ center Q) ≃* H)
    (S R : Subgroup Q) (hd : Disjoint R (center Q))
    {a : MulAut R} (ha : a ∈ pairAutomizer S R) :
    MulAut.congr (centralImageEquiv e R hd) a ∈
      pairAutomizer (S.map (centralModelMap e)) (R.map (centralModelMap e)) := by
  obtain ⟨b,hb,hab⟩ := ha
  let c := MulAut.congr e (quotientAut (center Q) b)
  have hf (x : Q) : centralModelMap e (b x) = c (centralModelMap e x) := by
    simp only [centralModelMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      c, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, quotientAut_apply_mk]
  refine ⟨c, preserves_image (centralModelMap e) b c hf S hb, ?_⟩
  intro r
  obtain ⟨x,rfl⟩ := (centralImageEquiv e R hd).surjective r
  change (centralImageEquiv e R hd (a ((centralImageEquiv e R hd).symm
    (centralImageEquiv e R hd x))) : H) = _
  rw [MulEquiv.symm_apply_apply, centralImageEquiv_apply, hab, hf, centralImageEquiv_apply]

/-- A two-group of pair automorphisms transports to the actual projected pair. -/
theorem centralImage_twoGroup [Finite Q] (e : (Q ⧸ center Q) ≃* H)
    (S : Sylow 2 Q) (R : Subgroup Q) (hd : Disjoint R (center Q))
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer (S : Subgroup Q) R)
    (h2 : IsPGroup 2 D) :
    let D' := D.map (MulAut.congr (centralImageEquiv e R hd)).toMonoidHom
    D' ≤ pairAutomizer (centralImageSylow e S : Subgroup H) (R.map (centralModelMap e)) ∧
      IsPGroup 2 D' := by
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    exact centralImage_pairAutomizer e _ R hd (hD ha)
  · exact h2.map _

private theorem map_frattini {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map (e : A →* B) = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective (φ := (e : A →* B)) e.surjective)
  · intro b hb
    exact ⟨e.symm b, frattini_le_comap_frattini_of_surjective (φ := (e.symm : B →* A)) e.symm.surjective hb,
      e.apply_symm_apply b⟩

/-- Pull an involution and its two power orbits back across a group isomorphism,
including the induced isomorphism of the genuine Frattini quotients. -/
theorem power_involution_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup (MulAut A))
    (h : ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ a ∈ D.map (MulAut.congr e).toMonoidHom, ∀ v,
        quotientAut (frattini B) a v ∈ zpowers v ∨
        quotientAut (frattini B) a v ∈ zpowers (g v)) :
    ∃ g : MulAut (A ⧸ frattini A), g ^ 2 = 1 ∧
      ∀ a ∈ D, ∀ v, quotientAut (frattini A) a v ∈ zpowers v ∨
        quotientAut (frattini A) a v ∈ zpowers (g v) := by
  obtain ⟨g,hg,ha⟩ := h
  let q := QuotientGroup.congr (frattini A) (frattini B) e (map_frattini e)
  have hq (a : MulAut A) (v : A ⧸ frattini A) :
      q (quotientAut (frattini A) a v) =
        quotientAut (frattini B) (MulAut.congr e a) (q v) := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (frattini A) v
    dsimp only [q]
    rw [quotientAut_apply_mk, QuotientGroup.congr_mk', QuotientGroup.congr_mk',
      quotientAut_apply_mk]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  refine ⟨MulAut.congr q.symm g, ?_, ?_⟩
  · rw [← map_pow, hg, map_one]
  · intro a had v
    rcases ha _ (mem_map_of_mem _ had) (q v) with h | h
    · left
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp h
      exact mem_zpowers_iff.mpr ⟨k, q.injective (by rw [map_zpow, hq]; exact hk)⟩
    · right
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp h
      apply mem_zpowers_iff.mpr
      refine ⟨k,q.injective ?_⟩
      simpa [map_zpow, MulAut.congr_apply, hq] using hk

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
