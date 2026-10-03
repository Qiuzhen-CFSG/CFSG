module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionSupport
public import Stellmacher.Recognition.LyonsU3Four.CentralizerFiveActionCompatibility
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.Character.InvolutionClassSum

/-!
# The three involution classes in the actual local centralizer

Sylow conjugacy puts every involution of `C_G(z)` in the supplied Sylow center.
Their images in the local odd-core quotient are distinct central elements, so
its three nonidentity elements represent distinct local classes. The class of
`z` has size one. Either other representative together with `z` generates the
central four-group, so its centralizer in `C_G(z)` is `C_G(Z(S))`.

Orbit–stabilizer therefore expresses every local involution sum using these
three representatives, with weights `1`, `|C_G(z)| / |C_G(Z(S))|` and the same
ratio again. No triviality or uniform fibers of the odd core are assumed.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Lemma 4(b–c).
-/

public section
open scoped BigOperators
open Theory.Character
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}

private def centerRep {z : G} (hz : z ∈ centerImage S) (v : QuarticCentralIndex S) :
    centralizer ({z} : Set G) := inclusion (sylow_le_involutionCentralizer S hz) v.1.1

omit [Finite G] in
private theorem centerRep_order (h : SylowStructure S) {z : G} (hz : z ∈ centerImage S)
    (v : QuarticCentralIndex S) : orderOf (centerRep hz v) = 2 := by
  let _ := h.center_elementary
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (v.1.1 : G) ^ 2 = 1
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (p := 2) v.1.1 v.1.property)
  · intro he
    apply v.property
    apply Subtype.ext
    apply Subtype.ext
    change (v.1.1 : G) = 1
    exact congrArg (fun x : centralizer ({z} : Set G) => (x : G)) he

private theorem centerRep_cover (h : SylowStructure S) {z : G} (hz : z ∈ centerImage S)
    (u : centralizer ({z} : Set G)) (hu : orderOf u = 2) :
    ∃ v : QuarticCentralIndex S, IsConj (centerRep hz v) u := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hxy⟩ := (centralizerSylow S hz).exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using hu)
  let s : S := ⟨(y.val : G), y.property⟩
  have hs2 : (s : G) ^ 2 = 1 := by
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    have hy2 : y.val ^ 2 = 1 :=
      isConj_one_right.mp (by simpa only [hu2] using IsConj.pow 2 hxy)
    exact congrArg Subtype.val hy2
  have hsZ : s ∈ center S := by
    obtain ⟨s', hs', he⟩ := involution_mem_centerImage S h s.property hs2
    have he' : s' = s := Subtype.ext he
    exact he' ▸ hs'
  have hs1 : (⟨s, hsZ⟩ : center S) ≠ 1 := by
    intro he
    have hy1 : y.val = 1 := Subtype.ext (congrArg (fun x : center S => (x.val : G)) he)
    have hu1 : u = 1 := isConj_one_left.mp (hy1 ▸ hxy)
    simp [hu1] at hu
  exact ⟨⟨⟨s, hsZ⟩, hs1⟩, hxy.symm⟩

private theorem centerRep_separate (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15) {α : FiveComplement →* MulAut S}
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (v w : QuarticCentralIndex S) (hc : IsConj (centerRep hz v) (centerRep hz w)) : v = w := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G))))
  have hmap (v : QuarticCentralIndex S) : f (centerRep hz v) = SemidirectProduct.inl v.1.1 := he v.1.1
  have hc' : IsConj (SemidirectProduct.inl (φ := α) v.1.1)
      (SemidirectProduct.inl (φ := α) w.1.1) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    refine isConj_iff.mpr ⟨f g, ?_⟩
    rw [← hmap v, ← hmap w, ← map_inv, ← map_mul, ← map_mul, hg]
  have hvw := hc'.eq_of_left_mem_center (localFive_inl_mem_center h β hβ hα v)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg SemidirectProduct.left hvw

private theorem centerRep_centralizer (h : SylowStructure S)
    {z : G} (hz : z ∈ centerImage S) (w : QuarticCentralIndex S)
    (hw : (w.1.1 : G) = z) (v : QuarticCentralIndex S) (hvw : v ≠ w) :
    centralizer ({centerRep hz v} : Set (centralizer ({z} : Set G))) =
      (centralizer (centerImage S : Set G)).subgroupOf (centralizer ({z} : Set G)) := by
  let _ := h.center_elementary
  let : Nontrivial (center S) := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.center_card]; omega)
  let : IsKleinFour (center S) := ⟨h.center_card, IsElementaryAbelian.exponent_eq_prime⟩
  ext x
  constructor
  · intro hx
    have hxv : (v.1.1 : G) * (x : G) = (x : G) * (v.1.1 : G) :=
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)).symm
    have hxw : (w.1.1 : G) * (x : G) = (x : G) * (w.1.1 : G) := by
      rw [hw]
      exact (mem_centralizer_singleton_iff.mp x.property).symm
    apply mem_centralizer_iff.mpr
    rintro a ⟨s, hs, rfl⟩
    change (s : G) * (x : G) = (x : G) * (s : G)
    let q : center S := ⟨s, hs⟩
    by_cases hq1 : q = 1
    · have he : (s : G) = 1 := congrArg (fun q : center S => (q.val : G)) hq1
      simp [he]
    by_cases hqw : q = w.val
    · have he : (s : G) = (w.1.1 : G) := congrArg (fun q : center S => (q.val : G)) hqw
      simpa only [he] using hxw
    by_cases hqv : q = v.val
    · have he : (s : G) = (v.1.1 : G) := congrArg (fun q : center S => (q.val : G)) hqv
      simpa only [he] using hxv
    have he := IsKleinFour.eq_mul_of_ne_all w.property v.property
      (fun hh => hvw (Subtype.ext hh.symm)) hq1 hqw hqv
    have he' : (s : G) = (w.1.1 : G) * (v.1.1 : G) :=
      congrArg (fun q : center S => (q.val : G)) he
    rw [he', mul_assoc, hxv, ← mul_assoc, hxw, mul_assoc]
  · intro hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact (mem_centralizer_iff.mp hx v.1.1 ⟨v.1.1, v.1.property, rfl⟩).symm


/-- The class sizes in the actual centralizer are one and twice the index of
its Sylow-center centralizer. -/
theorem local_involutionSum (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15) {α : FiveComplement →* MulAut S}
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (f : ClassFunction (centralizer ({z} : Set G))) (hf : IsClassFunction f) :
    involutionSum f =
      f (inclusion (sylow_le_involutionCentralizer S hz) w.1.1) +
        ((Nat.card (centralizer ({z} : Set G)) : ℂ) /
          Nat.card (centralizer (centerImage S : Set G))) *
        ((∑ v : center S, f (inclusion (sylow_le_involutionCentralizer S hz) v.1)) -
          f 1 - f (inclusion (sylow_le_involutionCentralizer S hz) w.1.1)) := by
  classical
  let : Fintype (QuarticCentralIndex S) := Fintype.ofFinite _
  let C := centralizer ({z} : Set G)
  let D := centralizer (centerImage S : Set G)
  let r : ℂ := (Nat.card C : ℂ) / Nat.card D
  let F : center S → ℂ := fun v => f (inclusion (sylow_le_involutionCentralizer S hz) v.1)
  have hD : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe (centralizer_le (Set.singleton_subset_iff.mpr hz))).toEquiv
  have hwtop : centralizer ({centerRep hz w} : Set C) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (x : G) * (w.1.1 : G) = (w.1.1 : G) * (x : G)
    rw [hw]
    exact mem_centralizer_singleton_iff.mp x.property
  have hsize (v : QuarticCentralIndex S) :
      (Nat.card C : ℂ) / Nat.card (centralizer ({centerRep hz v} : Set C)) =
        if v = w then 1 else r := by
    by_cases hv : v = w
    · subst v
      rw [hwtop, Subgroup.card_top, if_pos rfl]
      exact div_self (by exact_mod_cast (Nat.card_pos (α := C)).ne')
    · rw [centerRep_centralizer h hz w hw v hv, if_neg hv, hD]
  rw [involutionSum_of_representatives (centerRep hz) (centerRep_order h hz)
    (fun u hu => centerRep_cover h hz u hu) (centerRep_separate h β hβ hα hz e he) f hf]
  change (∑ v : QuarticCentralIndex S, (Nat.card C : ℂ) /
    Nat.card (centralizer ({centerRep hz v} : Set C)) * F v.val) =
      F w.val + r * ((∑ v, F v) - f 1 - F w.val)
  simp_rw [hsize]
  have hterm (v : QuarticCentralIndex S) :
      (if v = w then (1 : ℂ) else r) * F v.val =
        (if v = w then (1 - r) * F w.val else 0) + r * F v.val := by
    by_cases hv : v = w
    · simp only [hv, if_true]; ring
    · simp only [hv, if_false, zero_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ w), ← Finset.mul_sum]
  have hsum : (∑ v : QuarticCentralIndex S, F v.val) = (∑ v : center S, F v) - F 1 := by
    have heq : (∑ v : QuarticCentralIndex S, F v.val) = ∑ v ∈ Finset.univ.erase (1 : center S), F v :=
      (Finset.sum_subtype _ (by simp) _).symm
    rw [heq]
    exact Finset.sum_erase_eq_sub (Finset.mem_univ _)
  rw [hsum]
  have hF1 : F 1 = f 1 := by dsimp [F]; rw [map_one]
  rw [hF1]
  ring

end Stellmacher.Recognition.LyonsU3Four
