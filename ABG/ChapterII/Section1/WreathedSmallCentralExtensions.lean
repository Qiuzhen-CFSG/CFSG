module
public import ABG.ChapterII.Section1.WreathedExceptionalBase
public import ABG.ChapterII.Section1.WreathedCentralProductCoordinates
public import ABG.ChapterII.Section1.WreathedBaseProduct
public import Theory.GroupTheory.CyclicTwoSubgroups
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The two small central extensions in a wreathed group

If an actual subgroup `X` contains the ambient center, has order `2^(n+2)`,
and is not contained in the abelian base, then it is conjugate to either
`V` or `modularOvergroup`. This elementary classification supplies the small
central-extension case of ABG Chapter II §1 Lemma 3(i), article p.10.
All hypotheses use the chosen presentation and its height bound `n≥2`.

The index-two base gives `|X∩U|=2^(n+1)`. Every subgroup of `U` containing
the center splits as the join of the center with its intersection with `⟨s⟩`;
unique normal coordinates make these factors disjoint. The latter factor
therefore has order two, and the cyclic-two-subgroup calculation identifies
it as `⟨x₂⟩`. Thus `X∩U` is the common subgroup `exceptionalBase`.
An outer generator has the form `s^a*z` after removing a central factor.
Conjugation by `s^k` changes `a` to `a+2k`, up to another central factor,
so the parity of `a` gives the two asserted representatives. The existing
coordinate theorem identifies `exceptionalBase ⊔ ⟨z⟩` with `V`.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : ABG.Wreathed.Presentation S n)

private theorem center_le_base : Subgroup.center S ≤ P.U := by
  rw [P.center_eq_zpowers]
  exact Subgroup.zpowers_le.mpr (P.U.mul_mem
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))

private theorem base_split_form (i j : ℤ) :
    P.u ^ j * P.s ^ (i-j) = P.s ^ i * P.t ^ j := by
  have hc : Commute P.s P.t := P.commute
  rw [u, hc.mul_zpow, mul_assoc, ← (hc.zpow_zpow (i-j) j).eq, ← mul_assoc, ← zpow_add]
  congr 2
  omega

private theorem central_base_split (H : Subgroup S)
    (hHU : H ≤ P.U) (hCH : Subgroup.center S ≤ H) :
    H = Subgroup.center S ⊔ (H ⊓ Subgroup.zpowers P.s) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i,j,rfl⟩ := (P.mem_U_iff g).mp (hHU hg)
    rw [← P.base_split_form]
    have hu : P.u ^ j ∈ Subgroup.center S := (Subgroup.center S).zpow_mem P.u_mem_center j
    apply Subgroup.mul_mem_sup hu
    refine ⟨?_, ⟨i-j,rfl⟩⟩
    have hh := H.mul_mem (H.inv_mem (hCH hu)) hg
    rwa [← P.base_split_form, inv_mul_cancel_left] at hh
  · exact sup_le hCH inf_le_left

private theorem base_intersection_card (X : Subgroup S)
    (hcardX : Nat.card X = 2 ^ (n + 2)) (hnot : ¬X ≤ P.U) :
    Nat.card ↥(X ⊓ P.U) = 2 ^ (n + 1) := by
  let : Finite X := Nat.finite_of_card_ne_zero (by rw [hcardX]; positivity)
  have hidxle := Subgroup.relIndex_le_of_le_right (show X ≤ ⊤ from le_top)
    (show P.U.relIndex ⊤ ≠ 0 by rw [Subgroup.relIndex_top_right, P.index_U]; decide)
  rw [Subgroup.relIndex_top_right, P.index_U] at hidxle
  have hidxne : P.U.relIndex X ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h)
  have hidx0 : P.U.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : P.U.relIndex X = 2 := by omega
  have hcard := ((X ⊓ P.U).subgroupOf X).card_mul_index
  have he := Subgroup.subgroupOfEquivOfLe (show X ⊓ P.U ≤ X from inf_le_left)
  rw [Nat.card_congr he.toEquiv, hcardX] at hcard
  change Nat.card ↥(X ⊓ P.U) * (X ⊓ P.U).relIndex X = 2 ^ (n+2) at hcard
  rw [Subgroup.inf_relIndex_left, hidx, show n+2=(n+1)+1 by omega, pow_succ] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hcard

private theorem central_base_of_card
    (hs : orderOf P.s = 2 ^ n)
    (hd : Disjoint (Subgroup.center S) (Subgroup.zpowers P.s))
    (H : Subgroup S) (hHU : H ≤ P.U) (hCH : Subgroup.center S ≤ H)
    (hcardH : Nat.card H = 2 ^ (n+1)) :
    H = Subgroup.center S ⊔ Subgroup.zpowers P.x₂ := by
  have hsplit := P.central_base_split H hHU hCH
  have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint
    (Subgroup.center S) (H ⊓ Subgroup.zpowers P.s)
    (Subgroup.le_normalizer_of_normal) (hd.mono_right inf_le_right)
  rw [← hsplit, hcardH, P.card_center, pow_succ] at hprod
  have hcardA : Nat.card ↥(H ⊓ Subgroup.zpowers P.s) = 2 :=
    (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n) hprod).symm
  obtain ⟨k,hkn,he⟩ := Subgroup.eq_zpowers_two_pow_of_le P.s_pow
    (H ⊓ Subgroup.zpowers P.s) inf_le_right
  rw [he, Nat.card_zpowers, orderOf_pow_of_dvd (by positivity)
    (by rw [hs]; exact Nat.pow_dvd_pow 2 hkn), hs, Nat.pow_div hkn (by decide)] at hcardA
  have hk : n-k=1 := Nat.pow_right_injective (a:=2) (by decide) (by simpa using hcardA)
  have hk' : k=n-1 := by omega
  rw [he,hk'] at hsplit
  exact hsplit


private theorem s_order : orderOf P.s = 2 ^ n := by
  apply (orderOf_eq_iff (by positivity)).mpr
  refine ⟨P.s_pow, ?_⟩
  intro k hkn hk h
  have he := (P.normal_form_zpow_eq_iff k 0 0 0 0 0).mp (by simpa using h)
  have he' : (k : ℤ) % (2 ^ n : ℕ) = 0 := by simpa using he.1
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hkn)] at he'
  omega

private theorem center_disjoint_s :
    Disjoint (Subgroup.center S) (Subgroup.zpowers P.s) := by
  apply Subgroup.disjoint_def.mpr
  intro g hg hs
  rw [P.center_eq_zpowers] at hg
  obtain ⟨j,hj⟩ := hg
  obtain ⟨i,hi⟩ := hs
  have hcoords := (P.normal_form_zpow_eq_iff i 0 0 j j 0).mp (by
    simpa only [zpow_zero, mul_one, u, (show Commute P.s P.t from P.commute).mul_zpow]
      using hi.trans hj.symm)
  have hzero : i % (2 ^ n : ℕ) = 0 := by
    simpa only [Int.zero_emod] using hcoords.1.trans hcoords.2.1.symm
  rw [← hi]
  change P.s ^ i = 1
  rw [zpow_eq_zpow_emod' i P.s_pow, hzero, zpow_zero]

private theorem subgroup_outer_generator (B X : Subgroup S)
    (hB : X ⊓ P.U = B) {g : S} (hgX : g ∈ X) (hgU : g ∉ P.U) :
    X = B ⊔ Subgroup.zpowers g := by
  have hBX : B ≤ X := hB ▸ (show X ⊓ P.U ≤ X from inf_le_left)
  apply le_antisymm
  · intro a ha
    by_cases haU : a ∈ P.U
    · exact Subgroup.mem_sup_left (hB ▸ ⟨ha,haU⟩)
    · have hdiff : a * g⁻¹ ∈ B := by
        rw [← hB]
        refine ⟨X.mul_mem ha (X.inv_mem hgX), ?_⟩
        apply (Subgroup.mul_mem_iff_of_index_two P.index_U).mpr
        simp only [haU, Subgroup.inv_mem_iff, hgU]
      have hh := Subgroup.mul_mem_sup hdiff (Subgroup.mem_zpowers g)
      simpa only [inv_mul_cancel_right] using hh
  · exact sup_le hBX (Subgroup.zpowers_le.mpr hgX)

private theorem sup_zpowers_mul (B : Subgroup S) {c g : S} (hc : c ∈ B) :
    B ⊔ Subgroup.zpowers (c*g) = B ⊔ Subgroup.zpowers g := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Subgroup.zpowers_le.mpr
    exact Subgroup.mul_mem_sup hc (Subgroup.mem_zpowers _)
  · apply sup_le le_sup_left
    apply Subgroup.zpowers_le.mpr
    have hh := (B ⊔ Subgroup.zpowers (c*g)).mul_mem
      (Subgroup.mem_sup_left (B.inv_mem hc)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    simpa only [inv_mul_cancel_left] using hh

private theorem outer_generator_conj (i a : ℤ) :
    (MulAut.conj (P.s ^ i)) (P.s ^ a * P.z) =
      P.u ^ (-i) * (P.s ^ (a+2*i) * P.z) := by
  have hswap : P.z * P.s ^ (-i) = P.t ^ (-i) * P.z :=
    (show SemiconjBy P.z P.s P.t from P.z_mul_s).zpow_right (-i)
  change P.s ^ i * (P.s ^ a * P.z) * (P.s ^ i)⁻¹ = _
  calc
    _ = (P.s ^ i * P.s ^ a) * (P.z * P.s ^ (-i)) := by simp only [zpow_neg]; group
    _ = (P.s ^ (i+a) * P.t ^ (-i)) * P.z := by rw [hswap, ← zpow_add]; group
    _ = (P.u ^ (-i) * P.s ^ ((i+a)-(-i))) * P.z := by rw [P.base_split_form]
    _ = _ := by rw [show (i+a)-(-i)=a+2*i by omega, mul_assoc]

private theorem map_outer_extension (B : Subgroup S) (hBN : B.Normal)
    (hCB : Subgroup.center S ≤ B) (i a : ℤ) :
    (B ⊔ Subgroup.zpowers (P.s ^ a * P.z)).map (MulAut.conj (P.s ^ i)).toMonoidHom =
      B ⊔ Subgroup.zpowers (P.s ^ (a+2*i) * P.z) := by
  let := hBN
  have hmap : B.map (MulAut.conj (P.s ^ i)).toMonoidHom = B :=
    Subgroup.Normal.map_conj_eq B _
  rw [Subgroup.map_sup, hmap, MonoidHom.map_zpowers]
  change B ⊔ Subgroup.zpowers ((MulAut.conj (P.s ^ i)) (P.s ^ a * P.z)) = _
  rw [P.outer_generator_conj]
  exact sup_zpowers_mul B (hCB ((Subgroup.center S).zpow_mem P.u_mem_center _))


private theorem extension_parity (B X : Subgroup S) (hBN : B.Normal)
    (hCB : Subgroup.center S ≤ B) (hB : X ⊓ P.U = B) (hnot : ¬X ≤ P.U) :
    (∃ g : S, (B ⊔ Subgroup.zpowers P.z).map (MulAut.conj g).toMonoidHom = X) ∨
    (∃ g : S, (B ⊔ Subgroup.zpowers (P.s * P.z)).map (MulAut.conj g).toMonoidHom = X) := by
  obtain ⟨g,hgX,hgU⟩ := Set.not_subset.mp hnot
  obtain ⟨i,j,hij⟩ := P.exists_outer_normal_form hgU
  let a : ℤ := (i:ℤ)-j
  have he : P.u ^ (j:ℤ) * (P.s ^ a * P.z) = g := by
    rw [← mul_assoc, P.base_split_form]
    simpa only [zpow_natCast] using hij
  have hBX : B ≤ X := hB ▸ (show X ⊓ P.U ≤ X from inf_le_left)
  have hu : P.u ^ (j:ℤ) ∈ Subgroup.center S := (Subgroup.center S).zpow_mem P.u_mem_center _
  have hvX : P.s ^ a * P.z ∈ X := by
    have hh := X.mul_mem (X.inv_mem (hBX (hCB hu))) hgX
    rwa [← he, inv_mul_cancel_left] at hh
  have hvU : P.s ^ a * P.z ∉ P.U := by
    intro hh
    apply hgU
    rw [← he]
    exact P.U.mul_mem (P.center_le_base hu) hh
  have hgen := P.subgroup_outer_generator B X hB hvX hvU
  rcases Int.even_or_odd a with ⟨k,hk⟩ | ⟨k,hk⟩
  · left
    refine ⟨P.s ^ k, ?_⟩
    have hh := P.map_outer_extension B hBN hCB k 0
    rw [show (0:ℤ)+2*k=a by omega] at hh
    simpa only [zpow_zero, one_mul] using hh.trans hgen.symm
  · right
    refine ⟨P.s ^ k, ?_⟩
    have hh := P.map_outer_extension B hBN hCB k 1
    rw [show (1:ℤ)+2*k=a by omega] at hh
    simpa only [zpow_one] using hh.trans hgen.symm


private theorem V_eq_exceptionalBase_sup :
    P.V = P.exceptionalBase ⊔ Subgroup.zpowers P.z := by
  rw [P.V_eq_generators_center, exceptionalBase]
  calc
    _ = (Subgroup.zpowers P.x₂ ⊔ Subgroup.zpowers P.z) ⊔ Subgroup.center S := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
      simp only [Set.singleton_union]
    _ = _ := by ac_rfl

private theorem small_extension_base (X : Subgroup S)
    (hCX : Subgroup.center S ≤ X) (hcardX : Nat.card X = 2 ^ (n+2))
    (hnot : ¬X ≤ P.U) : X ⊓ P.U = P.exceptionalBase := by
  exact P.central_base_of_card P.s_order P.center_disjoint_s (X ⊓ P.U)
    inf_le_right (le_inf hCX P.center_le_base) (P.base_intersection_card X hcardX hnot)

/-- Small non-base subgroups containing the center have one of two conjugacy types. -/
public theorem small_central_extension_conjugacy (X : Subgroup S)
    (hCX : Subgroup.center S ≤ X) (hcardX : Nat.card X = 2 ^ (n+2))
    (hnot : ¬X ≤ P.U) :
    ∃ g : S, P.V.map (MulAut.conj g).toMonoidHom = X ∨
      P.modularOvergroup.map (MulAut.conj g).toMonoidHom = X := by
  have hbase := P.small_extension_base X hCX hcardX hnot
  rcases P.extension_parity P.exceptionalBase X P.exceptionalBase_normal
    (show Subgroup.center S ≤ P.exceptionalBase from le_sup_left) hbase hnot with
    ⟨g,hg⟩ | ⟨g,hg⟩
  · exact ⟨g, Or.inl (by rw [P.V_eq_exceptionalBase_sup]; exact hg)⟩
  · exact ⟨g, Or.inr hg⟩

end ABG.Wreathed.Presentation
