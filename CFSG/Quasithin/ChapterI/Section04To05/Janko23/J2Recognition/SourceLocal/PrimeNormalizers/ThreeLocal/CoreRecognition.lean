module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.Inputs
public import Theory.SpecificGroups.AlternatingSix.IndexSixRecognition
public import Theory.Alternating.Aut
public import Theory.GroupTheory.InvariantMaximalGeneration

/-!
# Recognizing the first three-centralizer from its Sylow calculation

Let C = C_G(X) and K = E(C_G(t)), with precisely the earlier 47.1–47.2
inputs. The marking of X as Sylow in C_G(K) excludes nine from the order
of that centralizer. At order 1080, normality of K in C would contradict
this bound, since Aut(A₅) has order 120. Normality of KX/X would imply
normality of K by taking the derived subgroup of its inverse image.
Consequently the actual embedded A₅ has a faithful six-coset action in
C/X, identifying that literal quotient with A₆.

The nonabelian Sylow three-subgroup then forces C to be perfect. Its
center is exactly X, so it is quasisimple. The covering map below is the
original quotient map followed by the constructed A₆ coordinates.

`core_recognition_of_sylow_data` supplies this entire recognition from
`CoreSylowData` and [N_G(X):C] = 2. It derives the order alternatives and
uses `seven_normalizer_ratio` through the checked Frattini exclusion in
`Recognition.Preparation`. The independent local Sylow calculation and
index-two witness remain to be constructed from the earlier inputs; this
conditional result is not a completed proof of the source theorem.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262.
The incompatible printed 47.4 and the asserted semidihedral structure are
not used.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace EarlierConclusions
variable (E : EarlierConclusions D)
include E

/-- The selected X is Sylow in the centralizer of the literal component K. -/
theorem component_centralizer_not_nine :
    ¬ 9 ∣ Nat.card (centralizer (InvolutionGeometry.rootComponent E.geometry.t : Set G)) := by
  intro hd
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨P, hP⟩ := E.geometry.X_sylow
  have hc : Nat.card P = 3 := by
    have h := congrArg (fun S : Subgroup G => Nat.card S) hP
    rwa [card_map_of_injective (centralizer _).subtype_injective, D.card_X] at h
  have h := P.pow_dvd_card_of_pow_dvd_card (n := 2) hd
  rw [hc] at h
  norm_num at h

private theorem card_component_aut : Nat.card (MulAut E.componentInC.range) = 120 := by
  let e := MonoidHom.ofInjective E.componentInC_injective
  rw [← Nat.card_congr (MulAut.congr e).toEquiv]
  let a := MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  rw [← Nat.card_congr a.toEquiv, Nat.card_perm, Nat.card_fin]
  decide

/-- At the required order, normality of K would give nine in its centralizer. -/
theorem component_not_normal (hc : Nat.card (C D) = 1080) :
    ¬ E.componentInC.range.Normal := by
  intro hn
  let := hn
  let f : C D →* MulAut E.componentInC.range := MulAut.conjNormal
  have hr : Nat.card f.range ∣ 120 := by
    rw [← E.card_component_aut]
    exact f.range.card_subgroup_dvd_card
  have hm := f.ker.card_mul_index
  rw [index_ker, hc] at hm
  have hk9 : 9 ∣ Nat.card f.ker := by
    obtain ⟨n, hn⟩ := hr
    have he' : Nat.card f.ker * 120 = 1080 * n := by
      rw [hn, ← mul_assoc, hm]
    have he : Nat.card f.ker * 40 = 360 * n := by omega
    have hd : 9 ∣ Nat.card f.ker * 40 := by rw [he]; exact dvd_mul_of_dvd_left (by decide) n
    exact (show Nat.Coprime 9 40 from by decide).dvd_of_dvd_mul_right hd
  let B := centralizer (InvolutionGeometry.rootComponent E.geometry.t : Set G)
  let g : f.ker →* B := ((C D).subtype.comp f.ker.subtype).codRestrict B (by
    intro x k hk
    rw [← E.componentMap_range] at hk
    obtain ⟨a, rfl⟩ := hk
    have he := congrArg (fun α : MulAut E.componentInC.range =>
      (((α ⟨E.componentInC a, ⟨a, rfl⟩⟩ : E.componentInC.range) : C D) : G)) x.property
    change ((x : C D) : G) * E.componentMap a * ((x : C D) : G)⁻¹ =
      E.componentMap a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : B => (b : G)) h
  exact E.component_centralizer_not_nine (hk9.trans (card_dvd_of_injective g hg))

/-- Taking the derived subgroup of the preimage rules out a normal quotient A₅. -/
theorem quotientComponent_not_normal (hc : Nat.card (C D) = 1080) :
    ¬ E.quotientComponent.range.Normal := by
  intro hn
  let := hn
  have hp : E.componentProduct.Normal := by
    rw [E.componentProduct_eq_comap]
    infer_instance
  let := hp
  let : Group.IsPerfect InvolutionGeometry.A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect E.componentInC.range := Group.IsPerfect.range E.componentInC
  have hz : XC D ≤ centralizer (E.componentInC.range : Set (C D)) := by
    intro x hx k _
    exact mem_center_iff.mp (XC_le_center D hx) k
  let : IsMulCommutative (XC D) :=
    ⟨⟨fun a b => Subtype.ext (mem_center_iff.mp (XC_le_center D b.property) a)⟩⟩
  have hder : ⁅E.componentProduct, E.componentProduct⁆ = E.componentInC.range := by
    exact commutator_sup_eq_of_perfect_of_commutative
      (hz.trans (centralizer_le_normalizer _))
  apply E.component_not_normal hc
  rw [← hder]
  infer_instance

omit E in
private theorem centralizer_order_arithmetic (c : ℕ) (hdiv : c ∣ 604800)
    (h8 : 8 ∣ c) (h27 : 27 ∣ c) (h5 : 5 ∣ c)
    (h16 : ¬ 16 ∣ c) (h25 : ¬ 25 ∣ c) : c = 1080 ∨ c = 7560 := by
  have h1080 : 1080 ∣ c := by
    exact (show Nat.Coprime 8 135 from by decide).mul_dvd_of_dvd_of_dvd h8
      ((show Nat.Coprime 27 5 from by decide).mul_dvd_of_dvd_of_dvd h27 h5)
  obtain ⟨n, hn⟩ := h1080
  have hn560 : n ∣ 560 := by
    rw [hn] at hdiv
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 1080)).mp hdiv
  have hn2 : ¬ 2 ∣ n := by
    intro hn2
    apply h16
    rw [hn]
    exact Nat.mul_dvd_mul (by decide : 8 ∣ 1080) hn2
  have hn5 : ¬ 5 ∣ n := by
    intro hn5
    apply h25
    rw [hn]
    exact Nat.mul_dvd_mul (by decide : 5 ∣ 1080) hn5
  have hcop : n.Coprime 80 := by
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr hn2).symm.pow_right 4).mul_right
      (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hn5).symm)
  have hn7 : n ∣ 7 := hcop.dvd_of_dvd_mul_right hn560
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hn7 with h | h
  · exact Or.inl (by simpa only [h, mul_one] using hn)
  · exact Or.inr (by simpa only [h] using hn)

/-- The local Sylow facts leave only the possible extra factor seven. -/
theorem centralizer_card_alternatives (S : CoreSylowData D) :
    Nat.card (C D) = 1080 ∨ Nat.card (C D) = 7560 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨P, hPC, _⟩ := S.three
  have h27 : 27 ∣ Nat.card (C D) := by
    have hp : Nat.card P = 27 := by
      rw [P.card_eq_multiplicity, E.card]
      decide +kernel
    simpa only [hp] using card_dvd_of_le hPC
  let T : Sylow 2 (C D) := Classical.choice inferInstance
  have h8 : 8 ∣ Nat.card (C D) := by
    simpa only [S.two_card T] using (T : Subgroup (C D)).card_subgroup_dvd_card
  have h16 : ¬ 16 ∣ Nat.card (C D) := by
    intro hd
    have ht := T.pow_dvd_card_of_pow_dvd_card (n := 4) hd
    rw [S.two_card T] at ht
    norm_num at ht
  have h5 : 5 ∣ Nat.card (C D) := dvd_trans (by decide : 5 ∣ 60) E.component_card_dvd
  exact centralizer_order_arithmetic _ (E.card ▸ (C D).card_subgroup_dvd_card)
    h8 h27 h5 h16 E.not_twenty_five_dvd

/-- The literal quotient C_G(X)/X is A₆ by its faithful six-coset action. -/
theorem alternatingQuotient_of_card (hc : Nat.card (C D) = 1080) :
    Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6)) := by
  let : IsSimpleGroup InvolutionGeometry.A5 := alternatingGroup.isSimpleGroup (by simp)
  let e := MonoidHom.ofInjective E.quotientComponent_injective
  let : IsSimpleGroup E.quotientComponent.range :=
    (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  exact Theory.SpecificGroups.AlternatingSix.alternatingSix_of_nonnormal_simple_index_six
    E.quotientComponent.range E.quotientComponent_card
    (E.quotientComponent_index_of_card hc) (E.quotientComponent_not_normal hc)

/-- The original quotient projection followed by the constructed A₆ coordinates. -/
noncomputable def coreCoverMap (hc : Nat.card (C D) = 1080) :
    C D →* alternatingGroup (Fin 6) :=
  (E.alternatingQuotient_of_card hc).some.toMonoidHom.comp (QuotientGroup.mk' (XC D))

/-- Every element of A₆ has a preimage under the actual covering map. -/
theorem coreCoverMap_surjective (hc : Nat.card (C D) = 1080) :
    Function.Surjective (E.coreCoverMap hc) :=
  (E.alternatingQuotient_of_card hc).some.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The kernel is exactly the original X inside C_G(X). -/
theorem coreCoverMap_ker (hc : Nat.card (C D) = 1080) :
    (E.coreCoverMap hc).ker = XC D := by
  ext x
  change (E.alternatingQuotient_of_card hc).some (QuotientGroup.mk' (XC D) x) = 1 ↔
    x ∈ XC D
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

/-- A nonabelian Sylow three-subgroup excludes a proper derived subgroup. -/
theorem centralizer_perfect_of_card (hc : Nat.card (C D) = 1080)
    (P : Sylow 3 (C D)) (hP : ¬ IsMulCommutative P) : Group.IsPerfect (C D) := by
  apply Theory.SpecificGroups.AlternatingSix.perfect_of_three_kernel_alternating_six_quotient
    (E.coreCoverMap hc) (E.coreCoverMap_surjective hc) ?_ P hP
  rw [E.coreCoverMap_ker hc,
    Nat.card_congr (subgroupOfEquivOfLe (X_le_C D)).toEquiv, D.card_X]

/-- The center is the literal seed subgroup, using the centerless A₆ quotient. -/
theorem centralizer_center_of_card (hc : Nat.card (C D) = 1080) :
    center (C D) = XC D := by
  apply le_antisymm ?_ (XC_le_center D)
  intro x hx
  have he : E.coreCoverMap hc x ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨c, rfl⟩ := E.coreCoverMap_surjective hc y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx c]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  rw [← E.coreCoverMap_ker hc]
  exact he

/-- Perfectness and the actual central quotient establish quasisimplicity. -/
theorem centralizer_quasisimple_of_card (hc : Nat.card (C D) = 1080)
    (P : Sylow 3 (C D)) (hP : ¬ IsMulCommutative P) :
    Theory.GroupTheory.IsQuasisimple (C D) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let e := (QuotientGroup.quotientMulEquivOfEq (E.centralizer_center_of_card hc)).trans
    (E.alternatingQuotient_of_card hc).some
  exact { toIsPerfect := E.centralizer_perfect_of_card hc P hP
          simple := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance }

/-- The preliminary seven-normalizer ratio removes the final order ambiguity. -/
theorem centralizer_card_of_core_sylow (S : CoreSylowData D)
    (hi : (CM D).index = 2) : Nat.card (C D) = 1080 :=
  E.centralizer_card_of_sylow_bounds hi (E.centralizer_card_alternatives S)

/-- The source recognition, conditional only on the preceding Sylow calculation
and the independent normalizer index. Both must be discharged in final assembly. -/
theorem core_recognition_of_sylow_data (S : CoreSylowData D)
    (hi : (CM D).index = 2) :
    Theory.GroupTheory.IsQuasisimple (C D) ∧
    Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6)) ∧
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) = 6 := by
  have hc := E.centralizer_card_of_core_sylow S hi
  obtain ⟨P, hPC, hn⟩ := S.three
  let R := P.subtype hPC
  have hR : ¬ IsMulCommutative R := by
    intro h
    let := h
    have e : R ≃* P := subgroupOfEquivOfLe hPC
    apply hn
    exact IsMulCommutative.of_comm fun x y => by
      obtain ⟨a, rfl⟩ := e.surjective x
      obtain ⟨b, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm]
  refine ⟨E.centralizer_quasisimple_of_card hc R hR,
    E.alternatingQuotient_of_card hc, ?_⟩
  rw [E.component_relIndex]
  exact E.quotientComponent_index_of_card hc

end EarlierConclusions
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
