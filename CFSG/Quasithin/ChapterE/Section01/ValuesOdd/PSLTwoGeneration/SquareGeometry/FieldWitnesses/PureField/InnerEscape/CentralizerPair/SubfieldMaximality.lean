module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair.Orders
public import Glauberman.DicksonClassification
import Mathlib.Tactic

/-!
# Maximality of the quadratic pure-field centralizer

Dickson's classification shows that every subgroup of order p(p²−1) in
PSL₂(p²) is maximal. The small case p=3 is retained: 24 does not divide 60,
so an A₅ overgroup is impossible. This order criterion applies to the actual
fixed-field PGL₂ embedding, factored through the faithful PSL₂-to-PGL₂ map.
Every element of the inner model is a PSL₂ element times a power of the pure
field involution. Since that involution already lies in its centralizer,
maximality lifts from the linear layer to the literal centralizer.

This supplies the remaining premise of the subfield-centralizer pair used
in E.1.14(6), including q=9. Sources: Huppert II.8.27 (Dickson), and
Aschbacher--Smith, E.1.8 and E.1.14(6), printed pp.210–211 and 214,
the latter citing Aschbacher (1982), Lemma 4.10.
-/

noncomputable section
open Subgroup GorensteinWalter Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair

private theorem square_sub_one_coprime {p : ℕ} (hp : 1 ≤ p) :
    (p ^ 2 - 1).Coprime p := by
  have hs : 1 ≤ p ^ 2 := by nlinarith
  have hc : (p ^ 2 - 1).Coprime (p ^ 2) :=
    (Nat.coprime_self_sub_left hs).mpr (Nat.coprime_one_left _)
  exact hc.of_dvd_right (dvd_pow_self p (by decide))

private theorem subfieldOrder_isCoatom {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (D : Subgroup (PSL2MatrixGroup F)) (hD : Nat.card D = p * (p ^ 2 - 1)) :
    IsCoatom D := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := Nat.odd_iff.mp ho
    omega
  have hs : 8 ≤ p ^ 2 - 1 := by
    have hh : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hsub := Nat.sub_add_cancel (by nlinarith : 1 ≤ p ^ 2)
  have hDlow : 24 ≤ p * (p ^ 2 - 1) := by nlinarith
  have hDtorus : p ^ 2 + 1 < p * (p ^ 2 - 1) := by nlinarith
  have hqodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) hqodd
  rw [hF] at hcard
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  have hcop : (p ^ 2 - 1).Coprime p := square_sub_one_coprime (by omega)
  have hDne : D ≠ ⊤ := by
    intro ht
    have hc : Nat.card (PSL2MatrixGroup F) = p * (p ^ 2 - 1) := by
      simpa [ht] using hD
    rw [hc] at hcard
    have h4 : 1 ≤ (p ^ 2) ^ 2 := by nlinarith
    have hs4 := Nat.sub_add_cancel h4
    nlinarith
  refine ⟨hDne, ?_⟩
  intro H hDH
  have hlt : p * (p ^ 2 - 1) < Nat.card H := by
    rw [← hD]
    by_contra! hge
    exact hDH.ne (eq_of_le_of_card_ge hDH.le hge)
  have hdvd : p * (p ^ 2 - 1) ∣ Nat.card H := hD ▸ card_dvd_of_le hDH.le
  have hdvd' : p ^ 2 - 1 ∣ Nat.card H := (dvd_mul_left _ _).trans hdvd
  have heq (hc : Nat.card H = Nat.card (PSL2MatrixGroup F)) : H = ⊤ :=
    eq_top_of_card_eq H hc
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · let : IsElementaryAbelian p H := hElem
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hm] at hdvd'
    have hh := (hcop.pow_right m).eq_one_of_dvd hdvd'
    omega
  · obtain ⟨z, hz, hc, _⟩ := hCyc
    rw [hgcd, hF] at hz
    rcases hz with hz | hz
    all_goals
      have hbound := Nat.le_of_dvd (by omega) hz
      omega
  · obtain ⟨z, hz, hc, _⟩ := hDih
    rw [hgcd, hF] at hz
    rcases hz with hz | hz
    all_goals
      have hbound := Nat.le_of_dvd (by omega) hz
      omega
  · obtain ⟨_, ⟨f⟩⟩ := hA4
    have hc := Nat.card_congr f.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
    omega
  · obtain ⟨_, ⟨f⟩⟩ := hS4
    have hc := Nat.card_congr f.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at hc
    norm_num at hc
    omega
  · obtain ⟨_, ⟨f⟩⟩ := hA5
    have hc : Nat.card H = 60 := by
      have hh := Nat.card_congr f.toEquiv
      rw [nat_card_alternatingGroup, Nat.card_fin] at hh
      norm_num at hh
      exact hh
    by_cases hp3' : p = 3
    · norm_num [hc, hp3'] at hdvd
    · have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      have hb : 120 ≤ p * (p ^ 2 - 1) := by nlinarith
      omega
  · obtain ⟨m, t, _, ht, N, C, hN, _, hcN, _, hcC, hdisj, hsup⟩ := hBorel
    let : N.Normal := hN
    have hc : Nat.card H = p ^ m * t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top]; exact le_top) hdisj
      simpa [hsup, hcN, hcC] using hh
    rw [hc] at hdvd'
    have hd := (hcop.pow_right m).dvd_of_dvd_mul_left hdvd'
    have htpos : 0 < t := hcC ▸ Nat.card_pos (α := C)
    have hlow := Nat.le_of_dvd htpos hd
    have hgcd' : Nat.gcd (p ^ 2 - 1) 2 = 2 := by rwa [hF] at hgcd
    rw [hgcd'] at ht
    have hhigh := Nat.le_of_dvd (by omega : 0 < (p ^ 2 - 1) / 2) ht
    omega
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPSL
    have hmcard := GaloisField.card p m hm0
    have hmOdd : Odd (Nat.card (GaloisField p m)) := hmcard ▸ ho.pow
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField p m) hmOdd
    rw [hmcard, ← Nat.card_congr f.toEquiv] at hc
    rcases (Nat.dvd_prime Nat.prime_two).mp hmdiv with hm1 | hm2
    · rw [hm1, pow_one] at hc
      omega
    · apply heq
      rw [hm2] at hc
      exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (hc.trans hcard.symm)
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPGL
    have hbound := Nat.le_of_dvd (by decide : 0 < 2) hmdiv
    have hm1 : m = 1 := by omega
    have hc := GorensteinWalter.pgl2_card_formula (GaloisField p m)
    rw [GaloisField.card p m hm0, ← Nat.card_congr f.toEquiv, hm1, pow_one] at hc
    omega

variable {F : Type*} [Field F] [Finite F]

/-- The literal pure-field centralizer is maximal in the canonical quadratic
inner model, uniformly for every odd prime (including 3 and 5). This discharges
the maximality premise of `hasPair_of_pureCentralizer_isCoatom`. -/
public theorem pureCentralizer_isCoatom {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)] :
    IsCoatom (centralizer ({pure σ} : Set (innerModel F σ))) := by
  classical
  let K := FixedPoints.subfield (zpowers σ) F
  let t : PSL2 F →* PGL2 F := ProjectiveSpecialLinearGroup.toPGL
  let e : PSL2 F ≃* t.range := MonoidHom.ofInjective ProjectiveSpecialLinearGroup.toPGL_injective
  let f : PGL2 K →* PSL2 F := e.symm.toMonoidHom.comp
    ((fixedProjectiveMap σ).codRestrict t.range (fixed_image_mem_psl hodd hF σ hσ))
  have hf (x : PGL2 K) : t (f x) = fixedProjectiveMap σ x :=
    MonoidHom.apply_ofInjective_symm ProjectiveSpecialLinearGroup.toPGL_injective _
  have hfinj : Function.Injective f := by
    intro x y h
    apply fixedProjectiveMap_injective σ
    simpa only [hf] using congrArg t h
  let j : PSL2 F →* innerModel F σ :=
    (((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp t).codRestrict
      (innerModel F σ) (fun x => (le_sup_left : pGammaL2PSLRange F ≤ innerModel F σ) ⟨x, rfl⟩))
  let C := centralizer ({pure σ} : Set (innerModel F σ))
  have hne := ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  have hDj : f.range ≤ C.comap j := by
    rintro _ ⟨x, rfl⟩
    apply (mem_pureCentralizer_iff hp hF σ hne (j (f x))).mpr
    refine ⟨(x, 1), ?_⟩
    apply SemidirectProduct.ext
    · exact (hf x).symm
    · rfl
  have hDcard : Nat.card f.range = p * (p ^ 2 - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, pgl2_card_formula]
    rw [fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1 hne]
  have hDmax := subfieldOrder_isCoatom hp hodd hF f.range hDcard
  have hCne : C ≠ ⊤ := by
    intro heq
    have hi := pureCentralizer_index_twice hp hodd hF σ hσ
    change C.index * 2 = _ at hi
    rw [heq, index_top] at hi
    have := hp.two_le
    nlinarith
  have hpure : pure σ ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hlarge : 3 < Nat.card F := by rw [hF]; have := hp.two_le; nlinarith
  let : (pGammaL2PSLRange F).Normal :=
    pGammaL2PSLRange_normal F ⟨p, 2, hp, hodd, by decide, hF⟩ hlarge
  have hdecomp (x : innerModel F σ) : ∃ y : PSL2 F, ∃ n : ℤ,
      j y * pure σ ^ n = x := by
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp x.property
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff F a).mp ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    exact ⟨y, n, Subtype.ext hab⟩
  refine ⟨hCne, ?_⟩
  intro H hCH
  have hDH : f.range ≤ H.comap j := hDj.trans (comap_mono hCH.le)
  rcases hDmax.le_iff.mp hDH with htop | heq
  · apply eq_top_iff.mpr
    intro x _
    obtain ⟨y, n, rfl⟩ := hdecomp x
    exact H.mul_mem (show j y ∈ H from (htop ▸ mem_top y : y ∈ H.comap j))
      (H.zpow_mem (hCH.le hpure) n)
  · exfalso
    apply hCH.not_ge
    intro x hx
    obtain ⟨y, n, rfl⟩ := hdecomp x
    have hyH : j y ∈ H := by
      have hh := H.mul_mem hx (H.inv_mem (H.zpow_mem (hCH.le hpure) n))
      simpa using hh
    have hyD : y ∈ f.range := heq ▸ hyH
    exact C.mul_mem (hDj hyD) (C.zpow_mem hpure n)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
