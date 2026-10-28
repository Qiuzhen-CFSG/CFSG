module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion
public import Theory.Representation.SLThreeCentralExtension.Orbits

/-!
# The L₃(2) fusion argument of 12.4.7

The original nonsplit four-space has one L-orbit outside C_V(L). The
distinguished fixed involution centralizes T, whereas the centralizer of
the original nonfixed v has the index-two subgroup R₁ as a Sylow subgroup.
Sylow cardinalities therefore separate these two orbits under G-conjugacy.
This proves full L-controlled fusion on V and weak closure of z in V.

The final theorem applies the actual 12.4.9 consumer with its fusion premise
discharged. The genuine 12.4.6 Sylow-centralizer assertion remains explicit;
no weak closure in T, or weak closure of V itself, is asserted.

Source: Aschbacher--Smith, 12.4.6--7, printed p.814, and 12.4.9, p.816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original L-action is transitive outside its original fixed line. -/
theorem SLThreeExtension.transitive_nonfixed (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (x y : G)
    (hxV : x ∈ V) (hyV : y ∈ V)
    (hx : x ∉ fixedSubgroup L V) (hy : y ∉ fixedSubgroup L V) :
    ∃ l ∈ L, MulAut.conj l x = y := by
  classical
  let _ := D.elementary
  obtain ⟨z, hz, hall⟩ := (Nat.card_eq_two_iff' (1 : fixedSubgroup L V)).mp
    (E.fixed_card_eq_two hne)
  let z' : Additive V := Additive.ofMul ⟨z, z.property.1⟩
  have hz' : z' ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    exact congrArg (fun w : Additive V => (w.toMul : G)) he
  have hker : ∀ w : Additive V, E.projection w = 0 ↔ w = 0 ∨ w = z' := by
    intro w
    constructor
    · intro hw
      have hcent := (E.mem_fixed_iff w).mp (E.kernel ▸ hw)
      let q : fixedSubgroup L V := ⟨w.toMul, w.toMul.property, hcent⟩
      have hq : q = 1 ∨ q = z := by
        by_cases hq : q = 1
        · exact Or.inl hq
        · exact Or.inr (hall q hq)
      rcases hq with hq | hq
      · left
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg (fun a : fixedSubgroup L V => (a : G)) hq
      · right
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg (fun a : fixedSubgroup L V => (a : G)) hq
    · rintro (rfl | rfl)
      · exact map_zero _
      · change z' ∈ E.projection.toLinearMap.ker
        rw [E.kernel]
        exact (E.mem_fixed_iff z').mpr z.property.2
  have hfix : ∀ g, E.action g z' = z' :=
    (E.mem_fixed_iff z').mpr z.property.2
  let x' : Additive V := Additive.ofMul ⟨x, hxV⟩
  let y' : Additive V := Additive.ofMul ⟨y, hyV⟩
  have hpx : E.projection x' ≠ 0 := by
    intro he
    exact hx ⟨hxV, (E.mem_fixed_iff x').mp (E.kernel ▸ he)⟩
  have hpy : E.projection y' ≠ 0 := by
    intro he
    exact hy ⟨hyV, (E.mem_fixed_iff y').mp (E.kernel ▸ he)⟩
  obtain ⟨g, hg⟩ := SLThreeCentralExtension.transitive_outside_kernel
    E.action E.projection z' hz' hker hfix E.indecomposable x' y' hpx hpy
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (E.quotientEquiv.symm g)
  have he : E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
    rw [hl, MulEquiv.apply_symm_apply]
  refine ⟨l, l.property, ?_⟩
  have hh := congrArg (fun w : Additive V => (w.toMul : G)) hg
  rw [← he, E.conjugation] at hh
  exact hh

private theorem mem_zpowers_two {z w : G} (hz : orderOf z = 2) :
    w ∈ zpowers z ↔ w = 1 ∨ w = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz]
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
    · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩

private theorem not_conjugate_of_index_two_sylow_centralizer
    (z v : G) (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hindex : R.relIndex (T : Subgroup G) = 2)
    (hR : Chapter1.IsSylowIn 2 R (centralizer ({v} : Set G))) :
    ¬ ∃ g : G, MulAut.conj g z = v := by
  rintro ⟨g, hg⟩
  let C := centralizer ({v} : Set G)
  let f : T →* C :=
    ((MulAut.conj g).toMonoidHom.comp (T : Subgroup G).subtype).codRestrict C (by
      intro t
      apply mem_centralizer_singleton_iff.mpr
      rw [← hg]
      exact (MulAut.conj g).map_mul (t : G) z |>.symm.trans
        ((congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hT t.property))).trans
          ((MulAut.conj g).map_mul z (t : G))))
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact (MulAut.conj g).injective (congrArg Subtype.val he)
  obtain ⟨P, hP⟩ := hR
  obtain ⟨Q, hQ⟩ := (T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hc : Nat.card T ≤ Nat.card R := by
    calc
      Nat.card T = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
      _ = Nat.card P := Nat.card_congr (Q.equiv P).toEquiv
      _ = Nat.card R := by
        rw [← hP]
        exact Nat.card_congr ((P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toEquiv
  have he : R = (T : Subgroup G) := Subgroup.eq_of_le_of_card_ge hRT hc
  simp [he] at hindex

/-- Source 12.4.7 in the L₃ case: weak closure of z in V, and full
L-control of G-fusion on V. R is precisely the Sylow witness of 12.4.6. -/
theorem slThree_fusion_of_sylow_centralizer
    (E : SLThreeExtension D) (z : G) (hz : orderOf z = 2)
    (hzgen : fixedSubgroup L V = zpowers z)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex (T : Subgroup G) = 2)
    (hR : Chapter1.IsSylowIn 2 R (centralizer ({v} : Set G))) :
    (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
    ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hzfixed : z ∈ fixedSubgroup L V := hzgen ▸ mem_zpowers z
  have hne : fixedSubgroup L V ≠ ⊥ := by
    intro he
    exact hz1 (show z ∈ (⊥ : Subgroup G) from he ▸ hzfixed)
  have hmem : ∀ w : G, w ∈ fixedSubgroup L V ↔ w = 1 ∨ w = z := by
    intro w
    rw [hzgen]
    exact mem_zpowers_two hz
  have hweak : ∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z := by
    intro g hgV
    by_cases hg : MulAut.conj g z ∈ fixedSubgroup L V
    · rcases (hmem _).mp hg with he | he
      · exact False.elim (hz1 ((MulAut.conj g).injective (he.trans (map_one _).symm)))
      · exact he
    · obtain ⟨l, hl, he⟩ := E.transitive_nonfixed hne _ v hgV hvV hg hv
      apply False.elim
      apply not_conjugate_of_index_two_sylow_centralizer z v hT R hRT hindex hR
      exact ⟨l*g, by simpa [MulAut.conj_apply, mul_assoc] using he⟩
  refine ⟨hweak, ?_⟩
  intro x hx y hy hxy
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  change MulAut.conj g x = y at hg
  by_cases hxfix : x ∈ fixedSubgroup L V
  · rcases (hmem x).mp hxfix with rfl | rfl
    · have hy1 : y = 1 := by simpa using hg.symm
      exact ⟨1, L.one_mem, by simp [hy1]⟩
    · have hyz : y = x := hg.symm.trans (hweak g (hg.symm ▸ hy))
      exact ⟨1, L.one_mem, by simp [hyz]⟩
  · have hynot : y ∉ fixedSubgroup L V := by
      intro hyfix
      rcases (hmem y).mp hyfix with hy1 | hyz
      · have hx1 : x = 1 := (MulAut.conj g).injective (hg.trans (hy1.trans (map_one _).symm))
        exact hxfix (hx1 ▸ (fixedSubgroup L V).one_mem)
      · have hback : MulAut.conj g⁻¹ z = x := by
          rw [← hyz, ← hg]
          simp [MulAut.conj_apply, mul_assoc]
        have hxz : x = z := hback.symm.trans (hweak g⁻¹ (hback.symm ▸ hx))
        exact hxfix (hxz ▸ hzfixed)
    exact E.transitive_nonfixed hne x y hx hy hxfix hynot

/-- Construct the distinguished involution and discharge all fusion claims
from the genuine earlier 12.2/1.2 setup and the original 12.4.6 witness. -/
theorem source_slThree_fusion
    {K : GroupClass.{u}} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (marked : SLThreeAlternative1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex (T : Subgroup G) = 2)
    (hR : Chapter1.IsSylowIn 2 R (centralizer ({v} : Set G))) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y := by
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  obtain ⟨z, hz, hzgen, hM, hMV, _, _⟩ :=
    exists_fixed_involution_setup_of_card_two h D structural earlier (E.fixed_card_eq_two hne)
  have hT : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    (structural G T L h).1.trans hM.le
  have hf := slThree_fusion_of_sylow_centralizer E z hz hzgen hT v hvV hv R hRT hindex hR
  exact ⟨z, hz, hzgen, hM.symm.le.trans hMV.le, hf.1, hf.2⟩

/-- The actual 12.4.9 application: only the source Sylow-centralizer and
commutator geometry remain; the global fusion premise is proved above. -/
theorem lemma_12_4_9_of_slThree_sylow_centralizer
    {K : GroupClass.{u}} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (marked : SLThreeAlternative1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex (T : Subgroup G) = 2)
    (hR : Chapter1.IsSylowIn 2 R (centralizer ({v} : Set G)))
    (g : G) (hA : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hfixed : fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hsymmetry : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom = ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let _ := D.elementary
  obtain ⟨z, _, hzgen, hcent, hweak, _⟩ := source_slThree_fusion
    h D structural marked earlier hmodel hne v hvV hv R hRT hindex hR
  have hzfixed : z ∈ fixedSubgroup L V := hzgen ▸ mem_zpowers z
  have hL : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hzfixed.2 l hl)
  apply lemma_12_4_9 hL hA _ hcent (hfixed hzfixed) hsymmetry hcomm
  intro a ha
  exact ⟨1, L.one_mem, by simpa using hweak a ha⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion
