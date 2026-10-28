module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Coprime

/-!
# The full Suzuki conditions from the two Singer orbits

The Singer group acts transitively on V minus its identity and on the
nonidentity cosets of the moving factor modulo V. Nonabelianness, proved
by the centralizer-intersection argument, forces every involution into V:
one involution outside V would transport to every quotient coset and make
the entire factor have exponent two. Conjugation by the order-seven group
therefore gives an actual cyclic automorphism group transitive on involutions.

The same two orbits identify the derived subgroup and the center with V.
Thus the output retains [I,I]=Z(I), the additional clause in Definition
2.4.13 that is omitted from the reminder immediately before J.2.3.
The orbit and cubic-invariance premises remain for the Singer module
calculation; neither nonabelianness nor exact exponent four is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Definition 2.4.13, printed p.532, and Lemma J.2.3(5), printed pp.433–434
(PDF pp.444–445).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- In a central elementary extension with a transitive nonzero quotient
action, one involution outside the kernel would force exponent two. -/
private theorem square_one_mem_V (d : TypeRuSetup G)
    (M A : Subgroup G) (hMS : M ≤ d.S)
    (htrans : ∀ x ∈ M, ∀ y ∈ M, x ∉ d.V → y ∉ d.V →
      ∃ a ∈ A, (a * x * a⁻¹)⁻¹ * y ∈ d.V)
    (hnab : ¬ IsMulCommutative M) (x : M) (hx : x ^ 2 = 1) :
    (x : G) ∈ d.V := by
  by_contra hxV
  apply hnab
  have hpow (y : M) : y ^ 2 = 1 := by
    apply Subtype.ext
    change (y : G) ^ 2 = 1
    by_cases hyV : (y : G) ∈ d.V
    · exact congrArg Subtype.val (d.ru1.natural.square_eq_one_of_trivial_kernel rfl ⟨y,hyV⟩)
    obtain ⟨a,_,hv⟩ := htrans x x.property y y.property hxV hyV
    let z := a * (x : G) * a⁻¹
    let v := z⁻¹ * (y : G)
    have hv2 : v ^ 2 = 1 := congrArg Subtype.val
      (d.ru1.natural.square_eq_one_of_trivial_kernel rfl ⟨v,hv⟩)
    have hz2 : z ^ 2 = 1 := by
      change (MulAut.conj a (x : G)) ^ 2 = 1
      rw [← map_pow, show (x : G)^2 = 1 from congrArg Subtype.val hx, map_one]
    have hzS : z ∈ d.S := by
      have he : z = (y : G) * v⁻¹ := by dsimp [v]; group
      rw [he]
      exact d.S.mul_mem (hMS y.property) (d.S.inv_mem (d.ru1.steinberg.kernel_le hv))
    have hcomm : Commute z v := d.ru1.central_V hv z hzS
    calc
      (y : G)^2 = (z * v)^2 := by simp only [v,mul_inv_cancel_left]
      _ = z^2 * v^2 := hcomm.mul_pow 2
      _ = 1 := by rw [hz2,hv2,mul_one]
  exact ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun y => orderOf_dvd_of_pow_eq_one (hpow y)) a b).eq⟩⟩


/-- Singer orbits identify both the center and the derived subgroup with V.
This supplies the additional clause in source Definition 2.4.13. -/
private theorem center_derived_eq_V_of_orbits (d : TypeRuSetup G)
    (M A : Subgroup G) (hMS : M ≤ d.S) (hVM : d.V ≤ M)
    (hn : A ≤ normalizer M)
    (hVtrans : ∀ x ∈ d.V, ∀ y ∈ d.V, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ A, a * x * a⁻¹ = y)
    (hMtrans : ∀ x ∈ M, ∀ y ∈ M, x ∉ d.V → y ∉ d.V →
      ∃ a ∈ A, (a * x * a⁻¹)⁻¹ * y ∈ d.V)
    (hnab : ¬ IsMulCommutative M) :
    (_root_.commutator M).map M.subtype = d.V ∧
    (center M).map M.subtype = d.V := by
  let ZM := M ⊓ centralizer (M : Set G)
  have hVZ : d.V ≤ ZM :=
    le_inf hVM (d.ru1.central_V.trans (centralizer_le hMS))
  have hnZ : A ≤ normalizer ZM := by
    have hc : normalizer (M : Set G) ≤ normalizer (centralizer (M : Set G)) :=
      (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (normal_subgroupOf_centralizer_normalizer _)
    exact (le_inf hn (hn.trans hc)).trans inf_normalizer_le_normalizer_inf
  have hZM : ZM = d.V := by
    apply le_antisymm _ hVZ
    intro x hx
    by_contra hxV
    apply hnab
    apply le_centralizer_iff_isMulCommutative.mp
    have hMZ : M ≤ ZM := by
      intro y hy
      by_cases hyV : y ∈ d.V
      · exact hVZ hyV
      obtain ⟨a,ha,hv⟩ := hMtrans x hx.1 y hy hxV hyV
      have hx' : a * x * a⁻¹ ∈ ZM :=
        (mem_normalizer_iff.mp (hnZ ha) x).mp hx
      have hh := ZM.mul_mem hx' (hVZ hv)
      simpa only [mul_inv_cancel_left] using hh
    exact hMZ.trans inf_le_right
  have hcenter : (center M).map M.subtype = ZM := by
    apply le_antisymm
    · rintro z ⟨x,hx,rfl⟩
      exact ⟨x.property,fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)⟩
    · rintro z ⟨hz,hc⟩
      exact ⟨⟨z,hz⟩,mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)),rfl⟩
  have hderV : ⁅M,M⁆ ≤ d.V := by
    rw [← d.ru1.derived_eq,map_subtype_commutator]
    exact commutator_mono hMS hMS
  have hnder : A ≤ normalizer (⁅M,M⁆ : Subgroup G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hn ha)]
  have hderne : ⁅M,M⁆ ≠ ⊥ := fun he => hnab (commutator_self_eq_bot_iff.mp he)
  obtain ⟨x,hx,hx1⟩ := (nontrivial_iff_exists_ne_one _).mp
    ((nontrivial_iff_ne_bot _).mpr hderne)
  have hVder : d.V ≤ ⁅M,M⁆ := by
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ (⁅M,M⁆ : Subgroup G).one_mem
    obtain ⟨a,ha,rfl⟩ := hVtrans x (hderV hx) y hy hx1 hy1
    exact (mem_normalizer_iff.mp (hnder ha) x).mp hx
  exact ⟨(map_subtype_commutator M).trans (le_antisymm hderV hVder),hcenter.trans hZM⟩

/-- The Singer group supplies a literal cyclic subgroup of automorphisms
transitive on all involutions of the nonabelian moving factor. The two
orbit premises concern actual conjugation on V and on the section M/V. -/
theorem SingerChoice.movingCore_suzuki_of_orbits (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G),d.S⁆ = d.V)
    (hab : IsMulCommutative (fixedCore d c.B7))
    (hdis : Disjoint (fixedCore d c.B7) d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1)
    (hn : cubicSubgroup d B ≤ normalizer (movingCore d c.B7 s))
    (htrans : ∀ x ∈ fixedCore d c.B7, x ≠ 1 →
      ∃ b ∈ cubicSubgroup d B, b * s * b⁻¹ = x)
    (hVtrans : ∀ x ∈ d.V, ∀ y ∈ d.V, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ c.B7, a * x * a⁻¹ = y)
    (hMtrans : ∀ x ∈ movingCore d c.B7 s, ∀ y ∈ movingCore d c.B7 s,
      x ∉ d.V → y ∉ d.V → ∃ a ∈ c.B7, (a * x * a⁻¹)⁻¹ * y ∈ d.V) :
    IsPGroup 2 (movingCore d c.B7 s) ∧
    ¬ IsMulCommutative (movingCore d c.B7 s) ∧
    _root_.commutator (movingCore d c.B7 s) = center (movingCore d c.B7 s) ∧
    ∃ A : Subgroup (MulAut (movingCore d c.B7 s)), IsCyclic A ∧
      ∀ x y : movingCore d c.B7 s, orderOf x = 2 → orderOf y = 2 →
        ∃ a ∈ A, a x = y := by
  let M := movingCore d c.B7 s
  have hMS : M ≤ d.S :=
    (le_normalizer_iff_commutator_le_left.mp (c.normalizes_coreCentralizer d B s hs)).trans inf_le_left
  have hnab := c.movingCore_nonabelian d B hfull hab hdis s hs hs1 hn htrans
  have hMV := c.V_le_movingCore d B hdis s hs.1
  have hnM : c.B7 ≤ normalizer M :=
    normalizer_commutator_ge_right (d.S ⊓ centralizer ({s} : Set G)) c.B7
  have hcd := center_derived_eq_V_of_orbits d M c.B7 hMS hMV hnM hVtrans hMtrans hnab
  have hspecial : _root_.commutator M = center M :=
    map_injective M.subtype_injective (hcd.1.trans hcd.2.symm)
  refine ⟨(isPGroup_pCoreIn 2 d.L).to_le hMS, hnab, hspecial, ?_⟩
  let f : c.B7 →* MulAut M := M.normalizerMonoidHom.comp
    (inclusion (normalizer_commutator_ge_right (d.S ⊓ centralizer ({s} : Set G)) c.B7))
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : IsCyclic c.B7 := isCyclic_of_prime_card c.card_seven
  have hc : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range,hc,?_⟩
  intro x y hx hy
  have hxV := square_one_mem_V d M c.B7 hMS hMtrans hnab x
    (by simpa only [hx] using pow_orderOf_eq_one x)
  have hyV := square_one_mem_V d M c.B7 hMS hMtrans hnab y
    (by simpa only [hy] using pow_orderOf_eq_one y)
  have hx1 : (x : G) ≠ 1 := by
    intro he
    have hx' : x = 1 := Subtype.ext he
    simp only [hx',orderOf_one] at hx
    omega
  have hy1 : (y : G) ≠ 1 := by
    intro he
    have hy' : y = 1 := Subtype.ext he
    simp only [hy',orderOf_one] at hy
    omega
  obtain ⟨a,ha,he⟩ := hVtrans x hxV y hyV hx1 hy1
  exact ⟨f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,Subtype.ext he⟩
end CFSG.Quasithin.ChapterJ.SpecialCore
