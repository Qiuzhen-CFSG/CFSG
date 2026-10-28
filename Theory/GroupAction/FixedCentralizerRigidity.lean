module

public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupAction.TwoGroupFixedImage

/-!
# Rigidity of the centralizer of an automorphism's fixed subgroup

The pointwise fixer is intersected with the centralizer of the specified
automorphism. This property transports under group isomorphisms. For an
involution it also lifts through a perfect central cover with odd kernel:
fixed points lift by the odd-fiber theorem, and automorphism descent is
faithful. Innerness is detected by that same descent.

Source: the central-cover passage in GLS4, Chapter 2, Lemma 13.3, applying
Chapter 4, Lemma 3.4(d1). The commutation condition is essential.
-/

public section
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- The centralizer of `a` in the pointwise fixer of its fixed subgroup
consists of the identity and `a`. -/
@[expose] def FixedCentralizerRigid (a : MulAut G) : Prop :=
  ∀ b : MulAut G, Commute b a → (∀ x : G, a x = x → b x = x) → b = 1 ∨ b = a

private theorem transfer (e : G ≃* H) (a : MulAut G)
  (hr : FixedCentralizerRigid (MulAut.congr e a)) : FixedCentralizerRigid a := by
  intro b hcomm hfix
  have hc := hcomm.map (MulAut.congr e).toMonoidHom
  have hf : ∀ y, (MulAut.congr e a) y = y → (MulAut.congr e b) y = y := by
    intro y hy
    change e (b (e.symm y)) = y
    have hx : a (e.symm y) = e.symm y := by
      apply e.injective
      exact hy.trans (e.apply_symm_apply y).symm
    rw [hfix _ hx, e.apply_symm_apply]
  rcases hr _ hc hf with h | h
  · exact Or.inl ((MulAut.congr e).injective (h.trans (map_one _).symm))
  · exact Or.inr ((MulAut.congr e).injective h)

/-- Rigidity is invariant under an actual isomorphism of the ambient groups. -/
theorem fixedCentralizerRigid_congr_iff (e : G ≃* H) (a : MulAut G) :
    FixedCentralizerRigid (MulAut.congr e a) ↔ FixedCentralizerRigid a := by
  constructor
  · exact transfer e a
  · intro hr
    apply transfer e.symm (MulAut.congr e a)
    have h : MulAut.congr e.symm (MulAut.congr e a) = a := by
      ext x
      change e.symm (e (a (e.symm (e x)))) = a x
      simp only [e.symm_apply_apply]
    rwa [h]
end MulAut

namespace PerfectCentralCovering
variable {G H : Type*} [Group G] [Group H]

/-- The descended automorphism is inner exactly when the original is inner. -/
theorem Cover.autMap_inner_iff (f : Cover G H)
    (hk : f.toMonoidHom.ker = Subgroup.center G) (a : MulAut G) :
    (∃ y, f.autMap hk a = MulAut.conj y) ↔ ∃ x, a = MulAut.conj x := by
  have hc (x : G) : f.autMap hk (MulAut.conj x) = MulAut.conj (f.toMonoidHom x) := by
    ext y
    obtain ⟨z, rfl⟩ := f.surjective y
    rw [f.autMap_apply]
    simp only [MulAut.conj_apply, map_mul, map_inv]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x, f.autMap_injective hk (hy.trans (hc x).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨f.toMonoidHom x, hc x⟩

/-- Fixed elements of an involution lift through the actual odd central cover. -/
theorem Cover.map_fixedSubgroup_of_odd [Finite G] (f : Cover G H)
    (hk : f.toMonoidHom.ker = Subgroup.center G)
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) (a : MulAut G) (ha : a ^ 2 = 1) :
    a.fixedSubgroup.map f.toMonoidHom = (f.autMap hk a).fixedSubgroup := by
  let A := Subgroup.zpowers a
  let rho := (f.autMap hk).comp A.subtype
  let : MulDistribMulAction A H := MulDistribMulAction.compHom _ rho
  have hp : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have hG : FixedPoints.subgroup A G = a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx ⟨a, Subgroup.mem_zpowers a⟩)
    · intro hx
      have hle : A ≤ MulAction.stabilizer (MulAut G) x :=
        Subgroup.zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mp hx)
      intro b
      exact hle b.property
  have hH : FixedPoints.subgroup A H = (f.autMap hk a).fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx ⟨a, Subgroup.mem_zpowers a⟩)
    · intro hx
      have hle : A ≤ (MulAction.stabilizer (MulAut H) x).comap (f.autMap hk) :=
        Subgroup.zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mp hx)
      intro b
      exact hle b.property
  have hh := f.toMonoidHom.map_fixedPoints_eq_of_odd_kernel hp hodd
    (fun b x => (f.autMap_apply hk b.val x).symm)
  rwa [hG, hH, f.toMonoidHom.range_eq_top_of_surjective f.surjective, top_inf_eq] at hh

/-- Rigidity lifts through an odd perfect central cover, with no loss of the
centralization requirement or of fixed points in the quotient. -/
theorem Cover.fixedCentralizerRigid_of_odd [Finite G] (f : Cover G H)
    (hk : f.toMonoidHom.ker = Subgroup.center G)
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) (a : MulAut G) (ha : a ^ 2 = 1)
    (hr : MulAut.FixedCentralizerRigid (f.autMap hk a)) : MulAut.FixedCentralizerRigid a := by
  intro b hcomm hfix
  have hfixed : ∀ y, f.autMap hk a y = y → f.autMap hk b y = y := by
    intro y hy
    have hm : y ∈ a.fixedSubgroup.map f.toMonoidHom := by
      rw [f.map_fixedSubgroup_of_odd hk hodd a ha]
      exact (MulAut.mem_fixedSubgroup _ _).mpr hy
    obtain ⟨x, hx, rfl⟩ := hm
    rw [f.autMap_apply, hfix x ((MulAut.mem_fixedSubgroup _ _).mp hx)]
  rcases hr _ (hcomm.map (f.autMap hk)) hfixed with hb | hb
  · exact Or.inl (f.autMap_injective hk (hb.trans (map_one _).symm))
  · exact Or.inr (f.autMap_injective hk hb)
end PerfectCentralCovering
