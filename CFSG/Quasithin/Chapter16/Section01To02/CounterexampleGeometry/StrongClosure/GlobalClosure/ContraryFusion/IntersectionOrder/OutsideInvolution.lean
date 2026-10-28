module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionOrder.Structure
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Algebra

/-!
# An involution outside the other factor

In the contrary-fusion configuration of Aschbacher's Lemma 3.4, the left
factor has an involution outside the right factor. This needs only the
standing hypotheses and local control, so the minimal-counterexample
statement follows without using its induction or failure fields.

Write t = aᵍ and let z generate the fixed subgroup of the intersection,
as supplied by `IntersectionOrder.Structure`. Choose v in A₁ − A₂ with
v² in A₂ and put x = vvᵗ. The diagonal homomorphism gives x² in ⟨z⟩.
A Sylow conjugation inside H places the two-subgroup ⟨t,x,z⟩ into S
while keeping the image of t in the union of the factors. The image of z
exchanges the factors, whereas every square fixes them. Thus x² ≠ z.

If all left-factor involutions lie in the intersection, a four-subgroup
supplies w with w² = 1 and wwᵗ = z. An elementary norm calculation then
excludes order-four elements in the intersection, so its exponent is two.
This proves the part of the source's four-group reduction needed here
directly from the checked fixed subgroup, including the smallest case.
Consequently v² = z, both v and vw have order four, and their diagonal
products are x and xz. After the same Sylow placement, one of these products
normalizes the factors. Hypothesis (*) and local clause (c), applied to the
corresponding cyclic order-four subgroup, give the contradiction.

Right conjugation is used throughout. The original element a is allowed
in either factor, and no swapped minimal-counterexample record is assumed.

Source: M. Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, from the choice of v through excluding Ω₁(A₁) ≤ A₂.
DOI: 10.1215/ijm/1256050927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
namespace OutsideInvolution
variable {G : Type*} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
open DiagonalConstruction

private theorem mem_two_powers {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  classical
  have hfin : IsOfFinOrder z := orderOf_pos_iff.mp (by omega)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hz] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  interval_cases i <;> simp

private theorem exists_square_mem (hA : IsPGroup 2 A₁) (hn : ¬ A₁ ≤ A₂) :
    ∃ v : G, v ∈ A₁ ∧ v ∉ A₂ ∧ v ^ 2 ∈ A₂ := by
  classical
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨n, hn⟩ := hA.exists_pow_pow_eq_one (⟨u, hu⟩ : A₁)
  have hex : ∃ k : ℕ, u ^ (2 ^ k) ∈ A₂ := ⟨n, by
    have he : u ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    rw [he]; exact A₂.one_mem⟩
  let k := Nat.find hex
  have hk : u ^ (2 ^ k) ∈ A₂ := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra he
    have : k = 0 := by omega
    simp [this] at hk
    exact hun hk
  refine ⟨u ^ (2 ^ (k - 1)), A₁.pow_mem hu _, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hkpos]
    exact hk

private theorem exponent_two_of_no_order_four (P : Subgroup G) (hP : IsPGroup 2 P)
    (hf : ∀ x ∈ P, (x ^ 2) ^ 2 = 1 → x ^ 2 = 1) : ∀ x ∈ P, x ^ 2 = 1 := by
  have hind : ∀ n : ℕ, ∀ x ∈ P, x ^ (2 ^ n) = 1 → x ^ 2 = 1 := by
    intro n
    induction n with
    | zero =>
      intro x hx he
      have hx1 : x = 1 := by simpa only [pow_zero, pow_one] using he
      simp only [hx1, one_pow]
    | succ n ih =>
      intro x hx he
      apply hf x hx
      apply ih (x ^ 2) (P.pow_mem hx 2)
      simpa only [← pow_mul, Nat.mul_comm 2, ← pow_succ] using he
  intro x hx
  obtain ⟨n, hn⟩ := hP.exists_pow_pow_eq_one (⟨x, hx⟩ : P)
  exact hind n x hx (congrArg Subtype.val hn)

private theorem norm_mem_fixed (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁) (ht : orderOf t = 2)
    {v : G} (hv : v ∈ A₁ ⊓ A₂) :
    v * (t⁻¹ * v * t) ∈ (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) := by
  refine ⟨⟨A₁.mul_mem hv.1 (conjugate_mem hs.2 hv.2),
    A₂.mul_mem hv.2 (conjugate_mem hs.1 hv.1)⟩, ?_⟩
  exact diagonal_range_centralizes h hs.1 ht ⟨⟨v, hv.1⟩, rfl⟩

private theorem square_one_of_norm_eq_square (_h : Hypotheses S A₁ A₂) {t z v : G}
    (hz : orderOf z = 2)
    (hfix : (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) = zpowers z)
    (hv : v ∈ A₁ ⊓ A₂) (he : v * (t⁻¹ * v * t) = v ^ 2) : v ^ 2 = 1 := by
  have hconj : t⁻¹ * v * t = v := by
    apply mul_left_cancel (a := v)
    simpa only [pow_two] using he
  have hcomm : v ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (fun y => t * y) hconj
    simpa [mul_assoc] using he
  have hvz : v ∈ zpowers z := hfix ▸ And.intro hv hcomm
  rcases mem_two_powers hz hvz with rfl | rfl
  · simp
  · exact hz ▸ pow_orderOf_eq_one _

private theorem square_mem_fixed (h : Hypotheses S A₁ A₂) {t v : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁) (ht : orderOf t = 2)
    (hv : v ∈ A₁) (hv2 : v ^ 2 ∈ A₂) :
    (v * (t⁻¹ * v * t)) ^ 2 ∈ (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) := by
  have he := (diagonalHom h hs.1).map_pow (⟨v, hv⟩ : A₁) 2
  change v ^ 2 * (t⁻¹ * v ^ 2 * t) = (v * (t⁻¹ * v * t)) ^ 2 at he
  rw [← he]
  exact norm_mem_fixed h hs ht ⟨A₁.pow_mem hv 2, hv2⟩

private theorem four_group_step [Finite G] (h : Hypotheses S A₁ A₂) {t z : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁) (ht : orderOf t = 2)
    (hz : orderOf z = 2)
    (hfix : (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) = zpowers z)
    (hall : ∀ v ∈ A₁, orderOf v = 2 → v ∈ A₂) :
    (∃ w : G, w ∈ A₁ ⊓ A₂ ∧ w ^ 2 = 1 ∧ w * (t⁻¹ * w * t) = z) ∧
      ∀ c ∈ A₁ ⊓ A₂, c ^ 2 = 1 := by
  have hzsq : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hnorm (c : G) (hc : c ∈ A₁ ⊓ A₂) :
      c * (t⁻¹ * c * t) = 1 ∨ c * (t⁻¹ * c * t) = z :=
    mem_two_powers hz (hfix ▸ norm_mem_fixed h hs ht hc)
  obtain ⟨E, hE, hEsq⟩ := h.left_rank
  let X := E.map A₁.subtype
  have hXA : X ≤ A₁ := map_subtype_le E
  have hXsq (x : G) (hx : x ∈ X) : x ^ 2 = 1 := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact congrArg (fun y : E => ((y : A₁) : G)) (hEsq ⟨y, hy⟩)
  have hXC : X ≤ A₁ ⊓ A₂ := by
    intro x hx
    refine ⟨hXA hx, ?_⟩
    by_cases hx1 : x = 1
    · simp [hx1]
    · exact hall x (hXA hx) (orderOf_eq_prime (hXsq x hx) hx1)
  have hXcard : Nat.card X = 4 := (card_map_of_injective A₁.subtype_injective).trans hE
  have hnle : ¬ X ≤ (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) := by
    intro hh
    have hh := card_le_of_le hh
    rw [hXcard, hfix, Nat.card_zpowers, hz] at hh
    omega
  obtain ⟨w, hwX, hwf⟩ := SetLike.not_le_iff_exists.mp hnle
  have hwC := hXC hwX
  have hw2 := hXsq w hwX
  have hwz : w * (t⁻¹ * w * t) = z := by
    rcases hnorm w hwC with he | he
    · exfalso
      apply hwf
      refine ⟨hwC, mem_centralizer_singleton_iff.mpr ?_⟩
      have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hw2)
      have hconj : t⁻¹ * w * t = w := by
        rw [eq_inv_of_mul_eq_one_right he, hwi]
      have he' := congrArg (fun y => t * y) hconj
      simpa [mul_assoc] using he'
    · exact he
  refine ⟨⟨w, hwC, hw2, hwz⟩, ?_⟩
  apply exponent_two_of_no_order_four (A₁ ⊓ A₂)
    (S.isPGroup'.to_le (inf_le_left.trans h.left_le))
  intro c hc hc4
  have hnc2 : (c * (t⁻¹ * c * t)) ^ 2 = 1 := by
    rcases hnorm c hc with he | he <;> simp [he, hzsq]
  have hcsqfixed : c ^ 2 ∈ (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) := by
    refine ⟨(A₁ ⊓ A₂).pow_mem hc 2, mem_centralizer_singleton_iff.mpr ?_⟩
    have hncsq : c ^ 2 * (t⁻¹ * c ^ 2 * t) = 1 := by
      have he := (diagonalHom h hs.1).map_pow (⟨c, hc.1⟩ : A₁) 2
      exact he.trans hnc2
    have hci : (c ^ 2)⁻¹ = c ^ 2 :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hc4)
    have hconj : t⁻¹ * c ^ 2 * t = c ^ 2 := by
      rw [eq_inv_of_mul_eq_one_right hncsq, hci]
    have he := congrArg (fun y => t * y) hconj
    simpa [mul_assoc] using he
  rcases mem_two_powers hz (hfix ▸ hcsqfixed) with hc2 | hc2
  · exact hc2
  rcases hnorm c hc with hnc | hnc
  · have hcwC : c * w ∈ A₁ ⊓ A₂ := (A₁ ⊓ A₂).mul_mem hc hwC
    have hcw2 : (c * w) ^ 2 = z := by
      rw [(factors_commute h hc.1 hwC.2).mul_pow, hc2, hw2, mul_one]
    have hncw : (c * w) * (t⁻¹ * (c * w) * t) = z := by
      have he := (diagonalHom h hs.1).map_mul (⟨c, hc.1⟩ : A₁) ⟨w, hwC.1⟩
      change (c * w) * (t⁻¹ * (c * w) * t) =
        (c * (t⁻¹ * c * t)) * (w * (t⁻¹ * w * t)) at he
      simpa [hnc, hwz] using he
    have hh := square_one_of_norm_eq_square h hz hfix hcwC (hncw.trans hcw2.symm)
    rw [hcw2] at hh
    have : z ≠ 1 := by intro he; simp [he] at hz
    exact (this hh).elim
  · exact square_one_of_norm_eq_square h hz hfix hc (hnc.trans hc2.symm)
private theorem into_sylow [Finite G] {H E : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) (hE : IsPGroup 2 E) (hEH : E ≤ H) :
    ∃ k ∈ H, conjugate E k ≤ (S : Subgroup G) := by
  have hp : IsPGroup 2 (E.subgroupOf H) :=
    hE.of_equiv (subgroupOfEquivOfLe hEH).symm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H Q (S.subtype hSH)
  refine ⟨(k : G)⁻¹, H.inv_mem k.property, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hy : MulAut.conj k (⟨x, hEH hx⟩ : H) ∈ S.subtype hSH := by
    rw [← hk]
    change MulAut.conj k (⟨x, hEH hx⟩ : H) ∈
      (Q : Subgroup H).map (MulAut.conj k).toMonoidHom
    exact mem_map_of_mem _ (hQ hx)
  change (k : G) * x * (k : G)⁻¹ ∈ S at hy
  change (k : G) * x * (k : G)⁻¹ ∈ (S : Subgroup G) at hy
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv] using hy

private theorem centralizer_placement [Finite G] (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂)
    (E : Subgroup G) (hES : E ≤ (S : Subgroup G))
    (htE : g⁻¹ * a * g ∈ E) (hEC : E ≤ centralizer ({g⁻¹ * a * g} : Set G)) :
    ∃ r : G, r ∉ intersectionGenerated A₁ A₂ ∧
      conjugate E r ≤ (S : Subgroup G) ∧
      r⁻¹ * (g⁻¹ * a * g) * r ∈ (A₁ : Set G) ∪ A₂ := by
  let H := intersectionGenerated A₁ A₂
  have hEH : conjugate E g⁻¹ ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    apply h.centralizer_le_generated ha ha1
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hEC hx))
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hp : IsPGroup 2 (conjugate E g⁻¹) := (S.isPGroup'.to_le hES).map _
  obtain ⟨k, hk, hEk⟩ := into_sylow (l.sylow_le_generated h) hp hEH
  have hEr : conjugate E (g⁻¹ * k) ≤ (S : Subgroup G) := by
    rwa [conjugate_conjugate] at hEk
  have hrn : g⁻¹ * k ∉ H := by
    intro hh
    apply hg
    have hgi : g⁻¹ ∈ H := by simpa using H.mul_mem hh (H.inv_mem hk)
    exact H.inv_mem_iff.mp hgi
  refine ⟨g⁻¹ * k, hrn, hEr, ?_⟩
  have htS : (g⁻¹ * k)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * k) ∈ S :=
    hEr (mem_map.mpr ⟨_, htE, by simp [mul_assoc]⟩)
  have htS' : k⁻¹ * a * k ∈ S := by simpa [mul_assoc] using htS
  have hh := h.closed_in_generated.2 a ha k hk
    ⟨H.mul_mem (H.mul_mem (H.inv_mem hk) (h.union_subset_generated ha)) hk, htS'⟩
  simpa [mul_assoc] using hh

private theorem square_normalizes [Finite G] (l : LocalControl S A₁ A₂) {x : G} (hx : x ∈ S) :
    x ^ 2 ∈ normalizer (A₁ : Set G) := by
  apply (mem_normalizer_iff_conjugate_eq _ _).mpr
  rw [pow_two, ← conjugate_conjugate]
  rcases l.permutes_pair x hx with hn | hs
  · rw [hn.1, hn.1]
  · rw [hs.1, hs.2]

private theorem union_normalizes (h : Hypotheses S A₁ A₂) {x : G}
    (hx : x ∈ (A₁ : Set G) ∪ A₂) : x ∈ normalizer (A₁ : Set G) := by
  rcases hx with hx | hx
  · exact A₁.le_normalizer hx
  · apply Subgroup.centralizer_le_normalizer
    intro y hy
    exact (factors_commute h hy hx).eq

private theorem three_placement [Finite G] (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g x z : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hxS : x ∈ S) (hzS : z ∈ S)
    (hxC : Commute x (g⁻¹ * a * g)) (hzC : Commute z (g⁻¹ * a * g)) :
    ∃ r : G, r ∉ intersectionGenerated A₁ A₂ ∧
      r⁻¹ * x * r ∈ S ∧ r⁻¹ * z * r ∈ S ∧
      r⁻¹ * (g⁻¹ * a * g) * r ∈ (A₁ : Set G) ∪ A₂ := by
  let t := g⁻¹ * a * g
  let E := (zpowers t ⊔ zpowers x) ⊔ zpowers z
  have htE : t ∈ E := (le_sup_left : zpowers t ⊔ zpowers x ≤ E) ((le_sup_left : zpowers t ≤ zpowers t ⊔ zpowers x) (mem_zpowers t))
  have hxE : x ∈ E := (le_sup_left : zpowers t ⊔ zpowers x ≤ E) ((le_sup_right : zpowers x ≤ zpowers t ⊔ zpowers x) (mem_zpowers x))
  have hzE : z ∈ E := (le_sup_right : zpowers z ≤ E) (mem_zpowers z)
  have hES : E ≤ (S : Subgroup G) :=
    sup_le (sup_le (zpowers_le.mpr ht) (zpowers_le.mpr hxS)) (zpowers_le.mpr hzS)
  have hEC : E ≤ centralizer ({t} : Set G) :=
    sup_le (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxC.eq)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzC.eq))
  obtain ⟨r, hr, hEr, htr⟩ := centralizer_placement l h ha ha1 hg E hES htE hEC
  exact ⟨r, hr, hEr (mem_map.mpr ⟨x, hxE, by simp⟩),
    hEr (mem_map.mpr ⟨z, hzE, by simp⟩), htr⟩

private theorem square_ne_fixed_involution [Finite G] (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g x z : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hxS : x ∈ S) (hzA : z ∈ A₁) (hz1 : z ≠ 1)
    (hxC : Commute x (g⁻¹ * a * g)) (hzC : Commute z (g⁻¹ * a * g)) :
    x ^ 2 ≠ z := by
  intro he
  obtain ⟨r, hr, hxr, _, _⟩ := three_placement l h ha ha1 hg ht hxS (h.left_le hzA) hxC hzC
  have hpow : (r⁻¹ * x * r) ^ 2 = r⁻¹ * z * r := by
    have hh := map_pow (MulAut.conj r⁻¹) x 2
    simpa [MulAut.conj_apply, he] using hh.symm
  have hn := square_normalizes l hxr
  rw [hpow] at hn
  have hzS : r⁻¹ * z * r ∈ S := by
    rw [← hpow]
    exact (S : Subgroup G).pow_mem hxr 2
  exact hr (h.transporter_mem_of_left_normalizer (Or.inl hzA) hz1 ⟨hzS, hn⟩)

private theorem no_two_order_four_conjugators [Finite G] (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g x z u v : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hxS : x ∈ S) (hzA : z ∈ A₁) (hz1 : z ≠ 1)
    (hxC : Commute x (g⁻¹ * a * g)) (hzC : Commute z (g⁻¹ * a * g))
    (huA : u ∈ A₁) (hvA : v ∈ A₁) (hu4 : 2 < orderOf u) (hv4 : 2 < orderOf v)
    (heu : u⁻¹ * (g⁻¹ * a * g) * u = (g⁻¹ * a * g) * x)
    (hev : v⁻¹ * (g⁻¹ * a * g) * v = (g⁻¹ * a * g) * x * z) : False := by
  let t := g⁻¹ * a * g
  obtain ⟨r, hr, hxr, hzr, htr⟩ := three_placement l h ha ha1 hg ht hxS (h.left_le hzA) hxC hzC
  let f := MulAut.conj r⁻¹
  have hf (y : G) : f y = r⁻¹ * y * r := by simp [f]
  rw [← hf] at hxr hzr
  change r⁻¹ * t * r ∈ _ at htr
  rw [← hf] at htr
  have htn : f t ∈ normalizer (A₁ : Set G) := union_normalizes h htr
  have ht1 : f t ≠ 1 := by
    intro he
    have ht1 : t = 1 := f.injective (by simpa using he)
    apply ha1
    apply (MulAut.conj g⁻¹).injective
    simpa [t, MulAut.conj_apply] using ht1

  have bad (y : G) (hyA : y ∈ A₁) (hy4 : 2 < orderOf y)
      (hyn : f (y⁻¹ * t * y) ∈ normalizer (A₁ : Set G))
      (hyS : f (y⁻¹ * t * y) ∈ S) : False := by
    have hyH : f y ∈ intersectionGenerated A₁ A₂ :=
      h.transporter_mem_of_left_normalizer htr ht1 (by
        change _ ∈ (S : Subgroup G) at hyS
        change _ ∈ (S : Subgroup G) ∧ _ ∈ normalizer (A₁ : Set G)
        simpa only [map_mul, map_inv] using And.intro hyS hyn)
    have hsub : conjugate (zpowers y) r ≤ intersectionGenerated A₁ A₂ := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨n, rfl⟩ := hb
      change MulAut.conj r⁻¹ (y ^ n) ∈ _
      change f (y ^ n) ∈ _
      rw [map_zpow]
      exact (intersectionGenerated A₁ A₂).zpow_mem hyH n
    exact hr ((l.unique_large (zpowers y) (Or.inl (zpowers_le.mpr hyA))
      (by simpa only [Nat.card_zpowers] using hy4)).2 r |>.mp hsub)
  have hts : f t ∈ S := htr.elim (fun hh => h.left_le hh) (fun hh => h.right_le hh)
  rcases l.permutes_pair (f x) hxr with hxn | hxs
  · apply bad u huA hu4
    · rw [heu, map_mul]
      exact (normalizer (A₁ : Set G)).mul_mem htn
        ((mem_normalizer_iff_conjugate_eq _ _).mpr hxn.1)
    · rw [heu, map_mul]
      exact (S : Subgroup G).mul_mem hts hxr
  · have hzs := l.swap_of_outside_transporter h (Or.inl hzA) hz1 hr (by simpa only [hf] using hzr)
    have hxzn : f x * f z ∈ normalizer (A₁ : Set G) := by
      apply (mem_normalizer_iff_conjugate_eq _ _).mpr
      rw [← conjugate_conjugate, hxs.1, hf, hzs.2]
    apply bad v hvA hv4
    · rw [hev, map_mul, map_mul, mul_assoc]
      exact (normalizer (A₁ : Set G)).mul_mem htn hxzn
    · rw [hev, map_mul, map_mul]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hts hxr) hzr
private theorem conj_norm_identity {t y : G} (hti : t⁻¹ = t) :
    y⁻¹ * t * y = (y ^ 2)⁻¹ * (y * (t⁻¹ * y * t)) * t := by
  calc
    _ = (y ^ 2)⁻¹ * (y * (t⁻¹ * y * t)) * t⁻¹ := by
      calc
        _ = y⁻¹ * t⁻¹ * y := by rw [hti]
        _ = _ := by group
    _ = _ := by rw [hti]

private theorem order_four_of_square {y z : G} (hy : y ^ 2 = z) (hz : orderOf z = 2) :
    orderOf y = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · have hz1 : z ≠ 1 := by intro he; simp [he] at hz
    simpa only [pow_one, hy] using hz1
  · have hh : (y ^ 2) ^ 2 = 1 := by rw [hy]; exact hz ▸ pow_orderOf_eq_one z
    simpa only [← pow_mul, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] using hh

end OutsideInvolution
open OutsideInvolution DiagonalConstruction
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The contrary transporter forces an involution of the left factor outside
its intersection with the right factor. Only the standing hypotheses and
local control are needed. -/
theorem LocalControl.exists_left_involution_outside_right_of_contrary
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) :
    ∃ v : G, v ∈ A₁ ∧ v ∉ A₂ ∧ orderOf v = 2 := by
  classical
  by_contra hn
  have hall : ∀ v ∈ A₁, orderOf v = 2 → v ∈ A₂ := by
    intro v hv hv2
    by_contra hvn
    exact hn ⟨v, hv, hvn, hv2⟩
  let t := g⁻¹ * a * g
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1)
  have hs := l.swap_of_outside_transporter h ha ha1 hg ht
  change conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁ at hs
  have hnle : ¬ A₁ ≤ A₂ := by
    intro hh
    have hrev := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hh
    change conjugate A₁ t ≤ conjugate A₂ t at hrev
    rw [hs.1, hs.2] at hrev
    have he := le_antisymm hh hrev
    apply hg
    apply h.transporter_mem_of_left_normalizer ha ha1
    refine ⟨ht, (mem_normalizer_iff_conjugate_eq _ _).mpr ?_⟩
    exact hs.1.trans he.symm
  obtain ⟨z, hz2, hzC, hzt, hfix⟩ := l.exists_intersection_fixed_involution h ha ha2 hg ht hcap
  change Commute z t at hzt
  change (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) = zpowers z at hfix
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz2).1)
  have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz2).1
  obtain ⟨⟨w, hwC, hw2, hwz⟩, hCsq⟩ := four_group_step h hs ht2 hz2 hfix hall
  obtain ⟨v, hvA, hvn, hv2B⟩ := exists_square_mem (S.isPGroup'.to_le h.left_le) hnle
  let x := v * (t⁻¹ * v * t)
  have hvT : t⁻¹ * v * t ∈ A₂ := conjugate_mem hs.1 hvA
  have hxS : x ∈ S := (S : Subgroup G).mul_mem (h.left_le hvA) (h.right_le hvT)
  have hxt : Commute x t := mem_centralizer_singleton_iff.mp
    (diagonal_range_centralizes h hs.1 ht2 ⟨⟨v, hvA⟩, rfl⟩)
  have hx2 : x ^ 2 = 1 := by
    have hh := square_mem_fixed h hs ht2 hvA hv2B
    rcases mem_two_powers hz2 (hfix ▸ hh) with hh | hh
    · exact hh
    · exact (square_ne_fixed_involution l h ha ha1 hg ht hxS hzC.1 hz1 hxt hzt hh).elim
  have hv2sq : (v ^ 2) ^ 2 = 1 := hCsq _ ⟨A₁.pow_mem hvA 2, hv2B⟩
  have hv2i : (v ^ 2)⁻¹ = v ^ 2 := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using hv2sq)
  have hv2fix : v ^ 2 ∈ (A₁ ⊓ A₂) ⊓ centralizer ({t} : Set G) := by
    refine ⟨⟨A₁.pow_mem hvA 2, hv2B⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : v ^ 2 * (t⁻¹ * v ^ 2 * t) = 1 :=
      ((diagonalHom h hs.1).map_pow (⟨v, hvA⟩ : A₁) 2).trans hx2
    have hc : t⁻¹ * v ^ 2 * t = v ^ 2 := by
      rw [eq_inv_of_mul_eq_one_right he, hv2i]
    have hh := congrArg (fun y => t * y) hc
    simpa [mul_assoc] using hh
  have hv2z : v ^ 2 = z := by
    rcases mem_two_powers hz2 (hfix ▸ hv2fix) with he | he
    · have hv1 : v ≠ 1 := by intro he; exact hvn (he.symm ▸ A₂.one_mem)
      exact (hvn (hall v hvA (orderOf_eq_prime he hv1))).elim
    · exact he
  have hv4 := order_four_of_square hv2z hz2
  have hvwA : v * w ∈ A₁ := A₁.mul_mem hvA hwC.1
  have hvw2 : (v * w) ^ 2 = z := by
    rw [(factors_commute h hvA hwC.2).mul_pow, hv2z, hw2, mul_one]
  have hvw4 := order_four_of_square hvw2 hz2
  have hvwNorm : (v * w) * (t⁻¹ * (v * w) * t) = x * z := by
    have he := (diagonalHom h hs.1).map_mul (⟨v, hvA⟩ : A₁) ⟨w, hwC.1⟩
    change (v * w) * (t⁻¹ * (v * w) * t) = x * (w * (t⁻¹ * w * t)) at he
    rwa [hwz] at he
  have hzx : Commute z x :=
    ((factors_commute h hvA hzC.2).symm).mul_right (factors_commute h hzC.1 hvT)
  have hvconj : v⁻¹ * t * v = t * x * z := by
    rw [conj_norm_identity hti, hv2z, hzi]
    change z * x * t = t * x * z
    calc
      _ = x * z * t := by rw [hzx.eq]
      _ = x * t * z := by rw [mul_assoc, hzt.eq, ← mul_assoc]
      _ = _ := by rw [hxt.eq]
  have hvwconj : (v * w)⁻¹ * t * (v * w) = t * x := by
    rw [conj_norm_identity hti, hvw2, hvwNorm, hzi]
    calc
      z * (x * z) * t = x * (z * z) * t := by rw [← mul_assoc z x z, hzx.eq, mul_assoc x z z]
      _ = x * t := by rw [hzz, mul_one]
      _ = t * x := hxt.eq
  exact no_two_order_four_conjugators l h ha ha1 hg ht hxS hzC.1 hz1 hxt hzt
    hvwA hvA (by omega) (by omega) hvwconj hvconj

/-- The p.95 outside-involution choice, with the original union hypothesis. -/
theorem MinimalCounterexample.exists_left_involution_outside_right_of_contrary
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) :
    ∃ v : G, v ∈ A₁ ∧ v ∉ A₂ ∧ orderOf v = 2 :=
  l.exists_left_involution_outside_right_of_contrary m.setup ha ha2 hg ht hcap

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
