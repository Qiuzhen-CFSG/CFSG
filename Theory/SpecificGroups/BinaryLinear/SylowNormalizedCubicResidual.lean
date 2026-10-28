module

public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.GroupTheory.CubicSylowJoin
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# A Sylow-normalized cubic residual is an actual minimal parabolic residual

A two-perfect subgroup with cubic quotient by its two-core has index three
when joined to a normalizing full Sylow two-subgroup. The literal join is
therefore a cover, hence one minimal parabolic of the same full flag.
Two-perfectness identifies the original subgroup with that parabolic's
embedded two-residual; no conjugate replacement of the actor is made.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions
variable {m : ℕ}

/-- The original normalized cubic residual is marked inside the same
binary Sylow flag, in every dimension. -/
theorem sylow_normalized_cubic_residual
    (J : Subgroup (LinearGroup (m+1))) (S : Sylow 2 (LinearGroup (m+1)))
    (hJ : IsPPerfect 2 J) (hc : Nat.card (J ⧸ pCore 2 J)=3)
    (hn : (S : Subgroup (LinearGroup (m+1)))≤normalizer (J : Set (LinearGroup (m+1)))) :
    ∃ b : Basis m, (S : Subgroup (LinearGroup (m+1)))=cutStabilizer b Set.univ ∧
      ∃ i : Fin m, J ⊔ (S : Subgroup (LinearGroup (m+1)))=minimalParabolic b i ∧
        J=(pResidual 2 (minimalParabolic b i)).map (minimalParabolic b i).subtype := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  have hd : 3∣Nat.card J := by
    rw [←hc,←index_eq_card]
    exact (pCore 2 J).index_dvd_card
  have hcard : ∃ n, Nat.card J∣3*2^n := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=J)).exists_card_eq
    refine ⟨n,?_⟩
    have hh := (pCore 2 J).index_mul_card
    rw [index_eq_card,hc,hn] at hh
    exact hh ▸ dvd_refl _
  have hnot : ¬IsPGroup 2 J := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn] at hd
    exact (by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow hd)
  let P := J ⊔ (S : Subgroup (LinearGroup (m+1)))
  have hi : (S : Subgroup (LinearGroup (m+1))).relIndex P=3 :=
    normalized_cubic_join_index_of_card_dvd S J hn hcard hnot
  have hSP : (S : Subgroup (LinearGroup (m+1))) ⋖ P := by
    apply covBy_of_eq_or_eq
    · refine lt_of_le_of_ne le_sup_right ?_
      intro he
      have hz : (S : Subgroup (LinearGroup (m+1))).relIndex P=1 := relIndex_eq_one.mpr he.ge
      omega
    · intro X hSX hXP
      have hh := relIndex_mul_relIndex (S : Subgroup (LinearGroup (m+1))) X P hSX hXP
      rw [hi] at hh
      have hd := (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hh)
      rcases hd with h | h
      · exact Or.inl (le_antisymm (relIndex_eq_one.mp h) hSX)
      · have he : X.relIndex P=1 := by rw [h] at hh; omega
        exact Or.inr (le_antisymm hXP (relIndex_eq_one.mp he))
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨i,hP⟩ := (fullFlag_covBy_iff S b hb P).mp hSP
  refine ⟨b,hb,i,hP,?_⟩
  have hPJ : P≤normalizer (J : Set (LinearGroup (m+1))) := sup_le J.le_normalizer hn
  let L := J.subgroupOf P
  let : L.Normal := normal_subgroupOf_of_le_normalizer hPJ
  have hpL : IsPPerfect 2 L := hJ.of_surjective
    (subgroupOfEquivOfLe (show J≤P from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show J≤P from le_sup_left)).symm.surjective
  have hgen : L ⊔ (S : Subgroup (LinearGroup (m+1))).subgroupOf P=⊤ := by
    rw [←subgroupOf_sup (show J≤P from le_sup_left) (show (S : Subgroup _)≤P from le_sup_right),subgroupOf_self]
  have hres := pResidual_eq_of_isPPerfect_sup L
    ((S : Subgroup (LinearGroup (m+1))).subgroupOf P) hpL S.isPGroup'.comap_subtype hgen
  have he : (pResidual 2 P).map P.subtype=J := by
    rw [hres]
    exact map_subgroupOf_eq_of_le le_sup_left
  rw [←hP]
  exact he.symm

end BinaryLinear.SylowFlagOvergroups
