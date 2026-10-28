module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter.PrimeTwoActors
public import Theory.GroupTheory.CyclicByFourOuterInvolutions
public import Theory.GroupTheory.SylowInnerAction
public import ABG.ChapterII.Section1.SemidihedralGenerators

/-!
# Retaining generators in the full unitary automorphism Sylow

Given the concrete hyperbolic generators and their order bound, their
semidihedral subgroup is an actual Sylow subgroup of PSU₃. Simplicity and
the noncommuting generators make conjugation faithful. Adjoin entrywise
Frobenius to its inner image and place this two-group in a Sylow subgroup
of the full automorphism group.

The proved semilinear coverage makes every actor inner or inner times
Frobenius; its cubic diagonal-outer argument applies to whole two-groups.
Inner Sylow maximality therefore gives the four required normal forms.
Frobenius cannot be inner: its exponent on the rotation differs from both
exponents realized by those inner normal forms. The half-power of the
rotation supplies the actual marked projective involution.

Source: Aschbacher–Smith E.1.14(7), printed p.214, citing Aschbacher (1982),
Lemma 4.11; A.3.21(b), printed p.55; ABG II.2 Lemma 1, article p.17.
This strengthens CyclicCoreSylow.Extension without altering its public interface.
The proof retains the very same rotation, swap, field actor and parameter.
The concrete generator and order premises are discharged in MarkedHyperbolicModel.
-/

public section

open Matrix Subgroup BenderSuzuki.External Theory.GroupTheory
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel

private theorem normalizes_of_square {G : Type*} [Group G] (H : Subgroup G)
    (c : G) (hc : c ^ 2 = 1) (hf : ∀ x ∈ H, c * x * c⁻¹ ∈ H) : c ∈ normalizer H := by
  have hi : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc)
  apply mem_normalizer_iff.mpr
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  have he : c * (c * x * c⁻¹) * c⁻¹ = x := by
    rw [hi]
    calc
      _ = (c * c) * x * (c * c) := by group
      _ = x := by rw [← pow_two, hc]; simp
  simpa only [he] using hf _ hx

private theorem involution_cases {G : Type*} [Group G] (c : G) (hc : c ^ 2 = 1)
    {t : G} (ht : t ∈ zpowers c) : t = 1 ∨ t = c := by
  classical
  have hf : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hc⟩
  rw [hf.mem_zpowers_iff_mem_range_orderOf] at ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  have hle : orderOf c ≤ 2 := Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hc)
  have hi' := Finset.mem_range.mp hi
  have he : i = 0 ∨ i = 1 := by omega
  rcases he with rfl | rfl <;> simp

private theorem normal_forms {G : Type*} [Group G] (H : Subgroup G)
    (c : G) (hc : c ^ 2 = 1) (hn : c ∈ normalizer H)
    {t : G} (ht : t ∈ H ⊔ zpowers c) : ∃ x ∈ H, t = x ∨ t = x * c := by
  have ht' : t ∈ (H : Set G) * (zpowers c : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left H (zpowers c) (zpowers_le.mpr hn)]
    exact ht
  obtain ⟨x, hx, y, hy, rfl⟩ := ht'
  refine ⟨x, hx, ?_⟩
  rcases involution_cases c hc hy with rfl | rfl <;> simp

private theorem conjugation_compatible {G : Type*} [Group G] (c : MulAut G) (x : G) :
    c * MulAut.conj x * c⁻¹ = MulAut.conj (c x) := by ext y; simp

/-- Adjoin the literal entrywise automorphism to an actual inner semidihedral
Sylow. Coverage and the cubic diagonal-outer calculation prove full Sylow
maximality, while the rotation action forces the adjoined automorphism to be outer. -/
theorem exists_marked_sylow_of_generators
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (n : ℕ) (x y : ProjectiveSpecialUnitaryMatrixGroup J)
    (hx : orderOf x = 2 ^ (n + 3)) (hy : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x ^ (2 ^ (n + 2) - 1))
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hγ : J.IsEntrywiseConjugation γ)
    (hγx : γ x = x ^ (2 ^ (n + 2) + 1)) (hγy : γ y = y)
    (hbound : ∀ R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsPGroup 2 R → Nat.card R ≤ 2 ^ (n + 4)) :
    ∃ (S : Sylow 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))),
      orderOf (x ^ (2 ^ (n + 2))) = 2 ∧
      ∃ q : CyclicByFourCoordinates
        (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
        (MulAut.conj (x ^ (2 ^ (n + 2)))),
        q.a = MulAut.conj x ∧ q.b = MulAut.conj y ∧ q.c = γ ∧ q.n = n := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let P := ProjectiveSpecialUnitaryMatrixGroup J
  have hm : 4 ≤ 2 ^ (n + 2) := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have horder : orderOf x = 2 ^ (n + 2) * 2 := by rw [hx]; ring
  have hne : x ^ (2 ^ (n + 2) - 1) ≠ x := by
    intro he
    have hh := pow_injOn_Iio_orderOf (x := x)
      (show 2 ^ (n + 2) - 1 < orderOf x by rw [horder]; omega)
      (show 1 < orderOf x by rw [horder]; omega) (by simpa using he)
    omega
  have hnotcomm : ¬ Commute y x := by
    intro hh
    apply hne
    rw [← hyx, hh.eq, mul_inv_cancel_right]
  have hyout : y ∉ zpowers x := by
    rintro ⟨i, rfl⟩
    exact hnotcomm (Commute.zpow_self _ _)
  have hz : center P = ⊥ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center P) inferInstance).resolve_right
    intro htop
    have hyc : y ∈ center P := htop ▸ mem_top y
    exact hnotcomm (show Commute y x from (mem_center_iff.mp hyc x).symm)
  have hinj := MulAut.conj_injective_of_center_eq_bot hz
  let H : Subgroup P := zpowers x ⊔ zpowers y
  obtain ⟨hHcard, _, _⟩ := ABG.semidihedral_generated_subgroup_data
    (show 2 ≤ n + 2 by omega) x y
    (by simpa only [Nat.add_assoc] using hx) hy hyout hyx
  change Nat.card H = 2 ^ (n + 4) at hHcard
  have hH2 : IsPGroup 2 H := IsPGroup.of_card hHcard
  let Q : Sylow 2 P :=
    { toSubgroup := H
      isPGroup' := hH2
      is_maximal' := fun {R} hR hHR =>
        (Subgroup.eq_of_le_of_card_ge hHR (by rw [hHcard]; exact hbound R hR)).symm }
  have hynorm : y ∈ normalizer (zpowers x) := by
    apply normalizes_of_square _ _ hy
    intro u hu
    have he : (zpowers x).map (MulAut.conj y).toMonoidHom ≤ zpowers x := by
      rw [MonoidHom.map_zpowers]
      apply zpowers_le.mpr
      change y * x * y⁻¹ ∈ zpowers x
      rw [hyx]
      exact (zpowers x).pow_mem (mem_zpowers x) _
    exact he (mem_map_of_mem _ hu)
  have hHforms (u : P) (hu : u ∈ H) : ∃ i : ℤ, u = x ^ i ∨ u = x ^ i * y := by
    obtain ⟨v, hv, he⟩ := normal_forms (zpowers x) y hy hynorm hu
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
    exact ⟨i, he⟩
  let K : Subgroup (MulAut P) := H.map MulAut.conj
  have hγ2 : γ ^ 2 = 1 := hγ.sq_eq_one
  have hγH : H.map γ.toMonoidHom ≤ H := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change zpowers (γ x) ⊔ zpowers (γ y) ≤ H
    rw [hγx, hγy]
    exact sup_le (zpowers_le.mpr (mem_sup_left ((zpowers x).pow_mem (mem_zpowers x) _))) le_sup_right
  have hγnorm : γ ∈ normalizer K := by
    apply normalizes_of_square K γ hγ2
    rintro a ⟨u, hu, rfl⟩
    rw [conjugation_compatible]
    exact mem_map_of_mem _ (hγH (mem_map_of_mem _ hu))
  let T : Subgroup (MulAut P) := K ⊔ zpowers γ
  have hγP : IsPGroup 2 (zpowers γ) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    exact ⟨1, by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one hγ2⟩
  have hT2 : IsPGroup 2 T := (hH2.map MulAut.conj).to_sup_of_normal_left' hγP (zpowers_le.mpr hγnorm)
  obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
  have hγS : γ ∈ S := hTS (mem_sup_right (mem_zpowers γ))
  have hKS : (Q : Subgroup P).map MulAut.conj ≤ (S : Subgroup (MulAut P)) :=
    le_sup_left.trans hTS
  have hSforms (t : MulAut P) (ht : t ∈ S) : ∃ u ∈ H, t = MulAut.conj u ∨ t = MulAut.conj u * γ := by
    obtain ⟨u, hu, he⟩ := PrimeTwoActors.actor_inner_or_inner_entrywise J hJ hp ho hcard hc
      (S : Subgroup (MulAut P)) S.isPGroup' γ hγ hγS t ht
    exact ⟨u, MulAut.inner_mem_image_sylow hz Q _ S.isPGroup' hKS hu, he⟩
  have hγout : γ ∉ MulAut.innerSubgroup P := by
    rintro ⟨u, hu⟩
    have huH : u ∈ H := MulAut.inner_mem_image_sylow hz Q _ S.isPGroup' hKS (hu ▸ hγS)
    obtain ⟨i, rfl | rfl⟩ := hHforms u huH
    · have hfix : γ x = x := by
        rw [← hu]
        change x ^ i * x * (x ^ i)⁻¹ = x
        rw [(Commute.zpow_self x i).eq, mul_inv_cancel_right]
      have he := pow_injOn_Iio_orderOf (x := x)
        (show 2 ^ (n + 2) + 1 < orderOf x by rw [horder]; omega)
        (show 1 < orderOf x by rw [horder]; omega) (by simpa only [pow_one] using hγx.symm.trans hfix)
      omega
    · have hact : γ x = x ^ (2 ^ (n + 2) - 1) := by
        rw [← hu]
        change (x ^ i * y) * x * (x ^ i * y)⁻¹ = _
        calc
          _ = x ^ i * (y * x * y⁻¹) * (x ^ i)⁻¹ := by group
          _ = x ^ i * x ^ (2 ^ (n + 2) - 1) * (x ^ i)⁻¹ := by rw [hyx]
          _ = x ^ (2 ^ (n + 2) - 1) := by
            rw [(Commute.zpow_self x i).pow_right (2 ^ (n + 2) - 1) |>.eq, mul_inv_cancel_right]
      have he := pow_injOn_Iio_orderOf (x := x)
        (show 2 ^ (n + 2) + 1 < orderOf x by rw [horder]; omega)
        (show 2 ^ (n + 2) - 1 < orderOf x by rw [horder]; omega) (hγx.symm.trans hact)
      omega
  let w := x ^ (2 ^ (n + 2))
  have hw : orderOf w = 2 := by
    have hd : 2 ^ (n + 2) ∣ orderOf x := by rw [horder]; exact dvd_mul_right _ _
    rw [orderOf_pow_of_dvd (by positivity) hd, horder, Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨S, hw, {
    a := MulAut.conj x
    b := MulAut.conj y
    c := γ
    n := n
    a_order := (orderOf_injective MulAut.conj hinj x).trans hx
    a_inner := ⟨x, rfl⟩
    a_mem := hKS (mem_map_of_mem _ (mem_sup_left (mem_zpowers x)))
    b_inner := ⟨y, rfl⟩
    b_mem := hKS (mem_map_of_mem _ (mem_sup_right (mem_zpowers y)))
    c_mem := hγS
    c_outer := hγout
    c_sq := hγ2
    b_action := ?_
    c_action := ?_
    marked := map_pow MulAut.conj x _
    cover := ?_ }, rfl, rfl, rfl, rfl⟩
  · rw [← map_inv, ← map_mul, ← map_mul, hyx, map_pow]
  · rw [conjugation_compatible, hγx, map_pow]
  · intro t ht
    obtain ⟨u, hu, he⟩ := hSforms t ht
    obtain ⟨i, rfl | rfl⟩ := hHforms u hu
    · refine ⟨i, ?_⟩
      rcases he with he | he
      · exact Or.inl (by simpa only [map_zpow] using he)
      · exact Or.inr (Or.inr (Or.inl (by simpa only [map_zpow] using he)))
    · refine ⟨i, ?_⟩
      rcases he with he | he
      · exact Or.inr (Or.inl (by simpa only [map_mul, map_zpow] using he))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [map_mul, map_zpow] using he)))
end BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
