module
public import Theory.GroupTheory.CoprimeSylowGeneration
public import Theory.GroupTheory.Commutator.CentralizingComplement
/-!
# Commutator comparison for conjugate odd tori

A coprime actor whose fixed subgroup is central and derived generates the
whole group by commutators. Apply this to P≤R and a conjugate torus Dˣ.
If C_R(D) is central and the center of R inside P is derived in P, then
[P,Dˣ]=P. Comparing P with its equal-order conjugate identifies [R,Dˣ]
with [R,D]=P, so the joint torus has all its R-commutators in P.

Source: Aschbacher–Smith, Lemma 2.4.8(5), printed p.530. The argument uses
normalization by both torus factors, without requiring their joint
abelianity in advance.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_of_coprime_fixed_le_center_derived (P D : Subgroup G)
    (hn : D ≤ normalizer (P : Set G)) (hsolv : Group.IsSolvable P)
    (hc : Nat.Coprime (Nat.card D) (Nat.card P))
    (hfix : P ⊓ centralizer (D : Set G) ≤ centralizer (P : Set G) ⊓ ⁅P,P⁆) :
    ⁅P,D⁆ = P := by
  let C := P ⊓ centralizer (D : Set G)
  let K := ⁅P,D⁆
  have hdec : P = K ⊔ C := eq_commutator_sup_centralizer_of_solvable_coprime P D hn hsolv hc
  have hCK : C ≤ normalizer (K : Set G) := inf_le_left.trans (normalizer_commutator_ge_left _ _)
  have hCC : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((hfix.trans inf_le_left).trans (centralizer_le inf_le_left))
  have hPP : ⁅P,P⁆ ≤ K := by
    rw [hdec]
    exact commutator_sup_le_of_normalized_derived K C hCK (by rw [hCC];exact bot_le)
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
  change P ≤ K
  exact hdec.le.trans (sup_le le_rfl ((hfix.trans inf_le_right).trans hPP))

omit [Finite G] in
theorem conjugate_fixed_central (R D : Subgroup G) (a : MulAut G)
    (hR : R.map a.toMonoidHom = R)
    (hfixed : R ⊓ centralizer (D : Set G) ≤ centralizer (R : Set G)) :
    R ⊓ centralizer (D.map a.toMonoidHom : Set G) ≤ centralizer (R : Set G) := by
  rintro z ⟨hzR,hzD⟩
  have hz' : a.symm z ∈ R := by
    have hh : z ∈ R.map a.toMonoidHom := hR.symm ▸ hzR
    obtain ⟨y,hy,he⟩ := hh
    have hz : a.symm z = y := by rw [←he];exact a.symm_apply_apply y
    exact hz ▸ hy
  have hc : a.symm z ∈ centralizer (D : Set G) := by
    apply mem_centralizer_iff.mpr
    intro d hd
    apply a.injective
    simpa only [map_mul,a.apply_symm_apply] using
      (mem_centralizer_iff.mp hzD) (a d) (mem_map_of_mem a.toMonoidHom hd)
  apply mem_centralizer_iff.mpr
  intro r hr
  have hr' : a.symm r ∈ R := by
    obtain ⟨y,hy,he⟩ := (show r ∈ R.map a.toMonoidHom from hR.symm ▸ hr)
    have he' : a.symm r = y := by rw [←he];exact a.symm_apply_apply y
    exact he' ▸ hy
  simpa only [map_mul,a.apply_symm_apply] using
    congrArg a ((mem_centralizer_iff.mp (hfixed ⟨hz',hc⟩)) (a.symm r) hr')

theorem conjugate_torus_commutator_le
    (R P D : Subgroup G) (a : MulAut G)
    (hR : R.map a.toMonoidHom = R) (hP : P ≤ R)
    (hRP : R ⊓ centralizer (R : Set G) ⊓ P ≤ ⁅P,P⁆)
    (hD : ⁅R,D⁆ = P)
    (hfixed : R ⊓ centralizer (D : Set G) ≤ centralizer (R : Set G))
    (hEP : D.map a.toMonoidHom ≤ normalizer (P : Set G))
    (hDP : D ≤ normalizer (P : Set G))
    (hsolv : Group.IsSolvable P)
    (hc : Nat.Coprime (Nat.card (D.map a.toMonoidHom)) (Nat.card P)) :
    ⁅R,D ⊔ D.map a.toMonoidHom⁆ ≤ P := by
  let E := D.map a.toMonoidHom
  have hEF : R ⊓ centralizer (E : Set G) ≤ centralizer (R : Set G) :=
    conjugate_fixed_central R D a hR hfixed
  have hPF : P ⊓ centralizer (E : Set G) ≤ centralizer (P : Set G) ⊓ ⁅P,P⁆ := by
    rintro z ⟨hzP,hzE⟩
    have hzR := hP hzP
    have hzC := hEF ⟨hzR,hzE⟩
    exact ⟨centralizer_le hP hzC,hRP ⟨⟨hzR,hzC⟩,hzP⟩⟩
  have hPE : ⁅P,E⁆ = P := commutator_eq_of_coprime_fixed_le_center_derived
    P E hEP hsolv hc hPF
  have hRE : ⁅R,E⁆ = P.map a.toMonoidHom := by
    rw [←hD,map_commutator,hR]
  have hPP : P ≤ P.map a.toMonoidHom := hPE.ge.trans
    ((commutator_mono hP le_rfl).trans_eq hRE)
  have hPa : P = P.map a.toMonoidHom := eq_of_le_of_card_ge hPP
    (Nat.card_congr (a.subgroupMap P).toEquiv).symm.le
  have hRE' : ⁅R,E⁆ ≤ P := by rw [hRE,←hPa]
  have hn : D ⊔ E ≤ normalizer (P : Set G) := sup_le hDP hEP
  rw [commutator_comm]
  exact (commutator_mono (sup_le
    (le_commutatorPreimage le_sup_left (by rw [commutator_comm];exact hD.le))
    (le_commutatorPreimage le_sup_right (by rw [commutator_comm];exact hRE'))) le_rfl).trans
    (commutator_commutatorPreimage_le (D ⊔ E) R P hn)
end Subgroup

