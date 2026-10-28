module

public import Theory.GroupTheory.ConjugationFamily

/-!
# Weak closure from a conjugation family

If a subgroup is normalized by the normalizers of all members of a conjugation
family containing it, every step of a fusion decomposition fixes the subgroup.
Thus it is weakly closed. In particular, a family whose normalizers reverse
inclusions consists of weakly closed subgroups.

The family interface only requests the same final conjugate subgroup, rather
than equality of conjugating elements: centralizer corrections are immaterial.
Huppert's extremal family supplies a concrete instance. The general interface
also permits the smaller Alperin–Goldschmidt family.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma I.2.4, pp. 413–414. The Lie-type application
requires separate identification of the family with parabolic radicals.
-/

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

namespace SubgroupFusion

variable {G : Type*} [Group G]

/-- Every subgroup conjugacy inside `P` is realized by successive normalizer
steps in members of `family`. Only the resulting subgroup is prescribed. -/
@[expose] public def ControlsFusion (P : Subgroup G)
    (family : Subgroup G → Prop) : Prop :=
  ∀ (A : Subgroup G), A ≤ P → ∀ g : G, rightConjugate A g ≤ P →
    ∃ h : G, HuppertConjugationDecomposition P family A h ∧
      rightConjugate A h = rightConjugate A g

/-- Each normalizer step fixes `Q` if the normalizers of family members
containing `Q` normalize `Q`. -/
public theorem fixed_of_decomposition {P Q : Subgroup G}
    {family : Subgroup G → Prop} {g : G}
    (hd : HuppertConjugationDecomposition P family Q g)
    (hnorm : ∀ D, family D → Q ≤ D →
      Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    rightConjugate Q g = Q := by
  induction hd with
  | one => simp [rightConjugate, Subgroup.conjBy_one]
  | @tail g h D hd hD _ hQD hh ih =>
    have hhQ := hnorm D hD (by simpa only [ih] using hQD) hh
    have hfix := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (Q : Set G)).inv_mem hhQ)
    have hcomp : rightConjugate Q (g * h) =
        rightConjugate (rightConjugate Q g) h := by
      simp only [rightConjugate, mul_inv_rev, Subgroup.conjBy_conjBy]
    rw [hcomp, ih]
    exact hfix

/-- The normalizer criterion for weak closure, for any conjugation family. -/
public theorem ControlsFusion.weakly_closed {P Q : Subgroup G}
    {family : Subgroup G → Prop} (hfamily : ControlsFusion P family)
    (hQP : Q ≤ P)
    (hnorm : ∀ D, family D → Q ≤ D →
      Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (g : G) (hg : Q.map (MulAut.conj g).toMonoidHom ≤ P) :
    Q.map (MulAut.conj g).toMonoidHom = Q := by
  have hg' : rightConjugate Q g⁻¹ ≤ P := by
    simpa only [rightConjugate, inv_inv, Subgroup.conjBy] using hg
  obtain ⟨h, hd, heq⟩ := hfamily Q hQP g⁻¹ hg'
  have hfix := heq.symm.trans (fixed_of_decomposition hd hnorm)
  simpa only [rightConjugate, inv_inv, Subgroup.conjBy] using hfix

/-- Normalizers reversing inclusions force every family member to be weakly
closed in `P`. -/
public theorem ControlsFusion.member_weakly_closed {P Q : Subgroup G}
    {family : Subgroup G → Prop} (hfamily : ControlsFusion P family)
    (hQP : Q ≤ P) (hQ : family Q)
    (hnorm : ∀ D E, family D → family E → D ≤ E →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G))
    (g : G) (hg : Q.map (MulAut.conj g).toMonoidHom ≤ P) :
    Q.map (MulAut.conj g).toMonoidHom = Q :=
  hfamily.weakly_closed hQP (fun E hE hQE => hnorm Q E hQ hE hQE) g hg

/-- The existing extremal-family fusion theorem realizes the interface without
additional fusion hypotheses. -/
public theorem extremal_controlsFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : ControlsFusion (P : Subgroup G) (HuppertExtremal P) := by
  intro A hAP g hg
  exact ⟨g, HuppertExtremal.conjugation_decomposition P hAP hg, rfl⟩

/-- Weak closure forces the normalizer of any intermediate subgroup to
normalize `Q`. This is the form used in local subgroup arguments. -/
public theorem normalizer_le_of_weakly_closed {P Q R : Subgroup G}
    (hQR : Q ≤ R) (hRP : R ≤ P)
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ P →
      Q.map (MulAut.conj g).toMonoidHom = Q) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply hweak
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hQR
  have heq : R.map (MulAut.conj g).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [heq] at hmap
  exact hmap.trans hRP

/-- To obtain weak closure in every `p`-overgroup, it suffices to find a
suitable family in each Sylow subgroup containing `Q`. -/
public theorem weakly_closed_in_p_overgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (Q R : Subgroup G) (hQR : Q ≤ R) (hR : IsPGroup p R)
    (hfamilies : ∀ P : Sylow p G, Q ≤ (P : Subgroup G) →
      ∃ family : Subgroup G → Prop, ControlsFusion (P : Subgroup G) family ∧
        family Q ∧ ∀ D E, family D → family E → D ≤ E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G))
    (g : G) (hg : Q.map (MulAut.conj g).toMonoidHom ≤ R) :
    Q.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨family, hf, hQ, hn⟩ := hfamilies P (hQR.trans hRP)
  exact hf.member_weakly_closed (hQR.trans hRP) hQ hn g (hg.trans hRP)

end SubgroupFusion
