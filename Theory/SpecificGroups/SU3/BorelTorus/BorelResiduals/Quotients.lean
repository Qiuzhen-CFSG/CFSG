module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A Borel quotient from its actual complement

If B = R T, with R its embedded two-core and R ∩ T = 1, the inclusion
of T followed by the quotient map is bijective. Its inverse is the quotient
coordinate map. We retain its value on every torus element, so it can be
used to compute induced automorphisms, rather than only quotient orders.

Source application: the full unitary Borel in Aschbacher–Smith 13.8.20.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {G H : Type*} [Group G] [Group H]

/-- Restrict an ambient equivalence to a specified image subgroup. -/
@[expose] noncomputable def subgroupEquiv (e : G ≃* H) {B : Subgroup G}
    {A : Subgroup H} (h : B.map e.toMonoidHom = A) : B ≃* A :=
  (e.subgroupMap B).trans (MulEquiv.subgroupCongr h)

@[simp] theorem subgroupEquiv_apply (e : G ≃* H) {B : Subgroup G}
    {A : Subgroup H} (h : B.map e.toMonoidHom = A) (b : B) :
    (subgroupEquiv e h b : H) = e b := rfl

@[simp] theorem subgroupEquiv_symm_apply (e : G ≃* H) {B : Subgroup G}
    {A : Subgroup H} (h : B.map e.toMonoidHom = A) (a : A) :
    ((subgroupEquiv e h).symm a : G) = e.symm a := rfl

/-- The actual torus inclusion followed by projection modulo the two-core. -/
@[expose] def torusToQuotient (B T : Subgroup G) (hT : T ≤ B) :
    T →* B ⧸ pCore 2 B :=
  (QuotientGroup.mk' (pCore 2 B)).comp (inclusion hT)

private theorem torusToQuotient_bijective (B R T : Subgroup G)
    (hT : T ≤ B) (hcore : B.pCoreIn 2 = R)
    (hdis : Disjoint R T) (hgen : R ⊔ T = B) :
    Function.Bijective (torusToQuotient B T hT) := by
  have hR : R ≤ B := hcore ▸ pCoreIn_le 2 B
  have hcore' : R.subgroupOf B = pCore 2 B := by
    rw [← hcore]
    exact comap_map_eq_self_of_injective B.subtype_injective _
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro t ht
    have htcore : inclusion hT t ∈ pCore 2 B :=
      (QuotientGroup.eq_one_iff _).mp ht
    have htR : (t : G) ∈ R := by
      rw [← hcore'] at htcore
      exact htcore
    apply Subtype.ext
    exact (mem_bot.mp ((disjoint_iff.mp hdis).le ⟨htR, t.property⟩))
  · intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
    have hsup : pCore 2 B ⊔ T.subgroupOf B = ⊤ := by
      rw [← hcore', ← subgroupOf_sup hR hT, hgen, subgroupOf_self]
    obtain ⟨r, hr, t, ht, he⟩ := mem_sup_of_normal_left.mp (hsup ▸ mem_top b)
    refine ⟨⟨t.val, ht⟩, ?_⟩
    change QuotientGroup.mk' (pCore 2 B) t = QuotientGroup.mk' (pCore 2 B) b
    rw [← he, map_mul]
    have hr1 : QuotientGroup.mk' (pCore 2 B) r = 1 :=
      (QuotientGroup.eq_one_iff r).mpr hr
    rw [hr1, one_mul]

/-- The full quotient, identified by the inverse of the actual torus inclusion. -/
noncomputable def quotientTorusEquiv (B R T : Subgroup G)
    (hT : T ≤ B) (hcore : B.pCoreIn 2 = R)
    (hdis : Disjoint R T) (hgen : R ⊔ T = B) :
    B ⧸ pCore 2 B ≃* T :=
  (MulEquiv.ofBijective (torusToQuotient B T hT)
    (torusToQuotient_bijective B R T hT hcore hdis hgen)).symm

@[simp] theorem quotientTorusEquiv_torus (B R T : Subgroup G)
    (hT : T ≤ B) (hcore : B.pCoreIn 2 = R)
    (hdis : Disjoint R T) (hgen : R ⊔ T = B) (t : T) :
    quotientTorusEquiv B R T hT hcore hdis hgen
      (QuotientGroup.mk' (pCore 2 B) (inclusion hT t)) = t :=
  (MulEquiv.ofBijective (torusToQuotient B T hT)
    (torusToQuotient_bijective B R T hT hcore hdis hgen)).symm_apply_apply t

/-- A Borel isomorphism induces the genuine quotient isomorphism. -/
@[expose] noncomputable def twoCoreQuotientEquiv (e : G ≃* H) :
    G ⧸ pCore 2 G ≃* H ⧸ pCore 2 H :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

@[simp] theorem twoCoreQuotientEquiv_mk (e : G ≃* H) (g : G) :
    twoCoreQuotientEquiv e (QuotientGroup.mk' (pCore 2 G) g) =
      QuotientGroup.mk' (pCore 2 H) (e g) := rfl

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
