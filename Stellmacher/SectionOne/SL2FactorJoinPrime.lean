module
public import Stellmacher.SectionOne.SL2FamilySylowCoordinates
public import Theory.GroupTheory.SubgroupConjugation

/-!
# SL₂ factor containment in joins of intermediate subgroups

Suppose E is normal in a finite group and normalizes an SL₂(2) subgroup D.
Let Q = S ∩ D have order two, and let Q ≤ U ≤ S. Among subgroups between
U and E ∨ U, containment of D is prime with respect to binary joins:
if their join contains D, one of them already contains D. Neither E
containing D nor S being Sylow is required by the proof, and U may move D.

Set R to be the join of the U-conjugates of Q, so R ≤ S. A subgroup K
in the stated interval which omits D omits all U-conjugates of D. Factor
x ∈ K as e*u. The conjugates Q^x and Q^u belong to K and the same
conjugate SL₂ subgroup. Distinct order-two subgroups generate a group of
order six, so these two lines agree. Thus K normalizes R. If two such
subgroups generated D, then D would normalize R ∩ D = Q. An order-two
normal subgroup is central, contradicting the trivial center of SL₂(2).

For the application, E is the global one-seven product, S is the quotient
Sylow subgroup, and U is its vector centralizer containing S ∩ E. This
allows a minimal selected-factor lift to have a unique maximal overgroup
of U even when U permutes the raw factors. Source: the choice of F₁ in
Stellmacher (6.4), refs/latex/stellmacher-n-group.tex, journal p.32.
-/

namespace Stellmacher.SectionOne
universe u

private theorem card_six_two_subgroups_generate
    {G : Type u} [Group G] [Finite G]
    (D Q R : Subgroup G) (hD : Nat.card D = 6)
    (hQ : Nat.card Q = 2) (hR : Nat.card R = 2)
    (hQD : Q ≤ D) (hRD : R ≤ D) (hne : Q ≠ R) : D ≤ Q ⊔ R := by
  have hle : Q ⊔ R ≤ D := sup_le hQD hRD
  have hdvd : Nat.card (↥(Q ⊔ R)) ∣ 6 := hD ▸ Subgroup.card_dvd_of_le hle
  have htwo : 2 ∣ Nat.card (↥(Q ⊔ R)) := hQ ▸ Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ R)
  have hbound : Nat.card (↥(Q ⊔ R)) ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  have hneq : Nat.card (↥(Q ⊔ R)) ≠ 2 := by
    intro hh
    have hQeq := Subgroup.eq_of_le_of_card_ge (le_sup_left : Q ≤ Q ⊔ R) (by omega)
    have hReq := Subgroup.eq_of_le_of_card_ge (le_sup_right : R ≤ Q ⊔ R) (by omega)
    exact hne (hQeq.trans hReq.symm)
  have hcard : Nat.card (↥(Q ⊔ R)) = 6 := by
    interval_cases hn : Nat.card (↥(Q ⊔ R)) <;> norm_num at *
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm.le

private theorem normalizer_centralizes_card_two
    {G : Type u} [Group G] [Finite G] (Q : Subgroup G) (hQ : Nat.card Q = 2) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer (Q : Set G) := by
  obtain ⟨t, ht, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  by_cases hone : q = 1
  · simp [hone]
  have hqt := huniq ⟨q, hq⟩ (fun he => hone (congrArg Subtype.val he))
  have hconj : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg q).mp hq
  have hcne : g * q * g⁻¹ ≠ 1 := by
    intro he
    have hh := congrArg (fun z : G => g⁻¹ * z * g) he
    exact hone (by simpa [mul_assoc] using hh)
  have hct := huniq ⟨g * q * g⁻¹, hconj⟩ (fun he => hcne (congrArg Subtype.val he))
  have he := congrArg (fun z : Q => (z : G) * g) (hct.trans hqt.symm)
  simpa [mul_assoc] using he.symm

/-- An SL2(2) subgroup cannot normalize an order-two subgroup it contains. -/
public theorem sl2_not_normalizes_order_two
    {G : Type u} [Group G] [Finite G] (D Q : Subgroup G)
    (hD : IsSL2Two D) (hQ : Nat.card Q = 2) (hQD : Q ≤ D) :
    ¬ D ≤ Subgroup.normalizer (Q : Set G) := by
  intro hnorm
  have hc := hnorm.trans (normalizer_centralizes_card_two Q hQ)
  have hbot : Q = ⊥ := by
    apply bot_unique
    intro q hq
    have hcent : (⟨q, hQD hq⟩ : D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro d
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hc d.property) q hq).symm
    rw [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hD] at hcent
    exact congrArg Subtype.val hcent
  have hone := Subgroup.card_eq_one.mpr hbot
  omega

private theorem missing_sl2_normalizes_line_orbit
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (E D U : Subgroup G) [E.Normal]
    (hDcard : Nat.card D = 6) (hED : E ≤ Subgroup.normalizer (D : Set G))
    (hQ : Nat.card (↥(S ⊓ D)) = 2)
    (hQU : S ⊓ D ≤ U)
    (K : Subgroup G) (hUK : U ≤ K) (hKE : K ≤ E ⊔ U) (hmiss : ¬ D ≤ K) :
    K ≤ Subgroup.normalizer ((⨆ u : U, (S ⊓ D).conjBy (u : G) : Subgroup G) : Set G) := by
  let Q := S ⊓ D
  let R := ⨆ u : U, Q.conjBy (u : G)
  have hQvU (u : U) : Q.conjBy (u : G) ≤ U := by
    rintro x ⟨q, hq, rfl⟩
    exact U.mul_mem (U.mul_mem u.property (hQU hq)) (U.inv_mem u.property)
  have hDvnorm (u : U) : E ≤ Subgroup.normalizer (D.conjBy (u : G) : Set G) := by
    have hm := Subgroup.map_mono (f := (MulAut.conj (u : G)).toMonoidHom) hED
    rw [Subgroup.map_equiv_normalizer_eq] at hm
    have hEm : E.map (MulAut.conj (u : G)).toMonoidHom = E :=
      Subgroup.Normal.map_conj_eq E (u : G)
    rw [hEm] at hm
    exact hm
  have hDvmiss (u : U) : ¬ D.conjBy (u : G) ≤ K := by
    intro hh
    apply hmiss
    intro d hd
    have hconj := hh (Subgroup.mem_map_of_mem (MulAut.conj (u : G)).toMonoidHom hd)
    have hback := K.mul_mem (K.mul_mem (K.inv_mem (hUK u.property)) hconj) (hUK u.property)
    simpa [MulAut.conj_apply, mul_assoc] using hback
  apply Subgroup.le_normalizer_iff.mpr
  intro x hx r hr
  have hmap : R.conjBy x ≤ R := by
    change (⨆ u : U, Q.conjBy (u : G)).map (MulAut.conj x).toMonoidHom ≤ R
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro v
    obtain ⟨e, he, u, hu, heu⟩ := Subgroup.mem_sup_of_normal_left.mp (hKE hx)
    let uv : U := ⟨u * (v : G), U.mul_mem hu v.property⟩
    have hxeq : x = e * u := heu.symm
    have hQx : (Q.conjBy (v : G)).conjBy x = (Q.conjBy (uv : G)).conjBy e := by
      rw [Subgroup.conjBy_conjBy, Subgroup.conjBy_conjBy]
      congr 1
      dsimp only [uv]
      rw [hxeq, mul_assoc]
    have hQDv : Q.conjBy (uv : G) ≤ D.conjBy (uv : G) := Subgroup.map_mono inf_le_right
    have hQeDv : (Q.conjBy (uv : G)).conjBy e ≤ D.conjBy (uv : G) := by
      have hh := Subgroup.map_mono (f := (MulAut.conj e).toMonoidHom) hQDv
      have hDm : (D.conjBy (uv : G)).map (MulAut.conj e).toMonoidHom = D.conjBy (uv : G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDvnorm uv he)
      rw [hDm] at hh
      exact hh
    have hsame : (Q.conjBy (uv : G)).conjBy e = Q.conjBy (uv : G) := by
      by_contra hne
      have hDle := card_six_two_subgroups_generate (D.conjBy (uv : G))
        ((Q.conjBy (uv : G)).conjBy e) (Q.conjBy (uv : G))
        (by unfold Subgroup.conjBy; rw [Subgroup.card_map_of_injective (MulAut.conj (uv : G)).injective]; exact hDcard)
        (by unfold Subgroup.conjBy; rw [Subgroup.card_map_of_injective (MulAut.conj e).injective,
          Subgroup.card_map_of_injective (MulAut.conj (uv : G)).injective]; exact hQ)
        (by unfold Subgroup.conjBy; rw [Subgroup.card_map_of_injective (MulAut.conj (uv : G)).injective]; exact hQ)
        hQeDv hQDv hne
      apply hDvmiss uv
      apply hDle.trans
      apply sup_le
      · rw [← hQx]
        rintro a ⟨b, hb, rfl⟩
        exact K.mul_mem (K.mul_mem hx (hUK (hQvU v hb))) (K.inv_mem hx)
      · exact (hQvU uv).trans hUK
    change (Q.conjBy (v : G)).conjBy x ≤ R
    rw [hQx, hsame]
    exact le_iSup (fun u : U => Q.conjBy (u : G)) uv
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hr)

public theorem sl2_factor_le_sup_iff
    {G : Type u} [Group G] [Finite G]
    (S E D U : Subgroup G) [E.Normal]
    (hD : IsSL2Two D) (hED : E ≤ Subgroup.normalizer (D : Set G))
    (hQ : Nat.card (↥(S ⊓ D)) = 2)
    (hQU : S ⊓ D ≤ U) (hUS : U ≤ S)
    (K1 K2 : Subgroup G) (hUK1 : U ≤ K1) (hUK2 : U ≤ K2)
    (hK1 : K1 ≤ E ⊔ U) (hK2 : K2 ≤ E ⊔ U) :
    D ≤ K1 ⊔ K2 ↔ D ≤ K1 ∨ D ≤ K2 := by
  constructor
  · intro hjoin
    by_contra hn
    push Not at hn
    let R := ⨆ u : U, (S ⊓ D).conjBy (u : G)
    have hnorm : D ≤ Subgroup.normalizer (R : Set G) := hjoin.trans (sup_le
      (missing_sl2_normalizes_line_orbit S E D U (RankOneThreeGroupAssembly.isSL2Two_card hD)
        hED hQ hQU K1 hUK1 hK1 hn.1)
      (missing_sl2_normalizes_line_orbit S E D U (RankOneThreeGroupAssembly.isSL2Two_card hD)
        hED hQ hQU K2 hUK2 hK2 hn.2))
    have hRS : R ≤ S := by
      apply iSup_le
      intro u
      rintro x ⟨q, hq, rfl⟩
      exact S.mul_mem (S.mul_mem (hUS u.property) hq.1) (S.inv_mem (hUS u.property))
    have hQR : S ⊓ D ≤ R := by
      have hh := le_iSup (fun u : U => (S ⊓ D).conjBy (u : G)) (1 : U)
      simpa only [OneMemClass.coe_one, Subgroup.conjBy_one] using hh
    have hinf : R ⊓ D = S ⊓ D :=
      le_antisymm (inf_le_inf_right _ hRS) (le_inf hQR inf_le_right)
    apply sl2_not_normalizes_order_two D (S ⊓ D) hD hQ inf_le_right
    rw [← hinf]
    exact (le_inf hnorm D.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  · rintro (h1 | h2)
    · exact h1.trans le_sup_left
    · exact h2.trans le_sup_right

end Stellmacher.SectionOne
