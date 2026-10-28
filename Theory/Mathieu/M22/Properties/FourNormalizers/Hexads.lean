module

public import Theory.GroupTheory.FourGroupNormalizerOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Geometry
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Enumeration

/-!
# Hexad overgroups of four-group normalizers in M₂₂

A nontrivial subgroup of the pointwise hexad kernel has exactly that hexad as
its common fixed points. Its full design-group normalizer therefore preserves
the hexad. For a four-group the inner normalizer has order at most 6·384, less
than the hexad stabilizer's order 5760. This also proves strictness in the full
design group. The inner stabilizer has characteristic two; the outer one
inherits this through its normal inner subgroup of index dividing two.

These local consequences of hexad placement support Aschbacher–Smith 15.3.43,
printed p.1140, and the M₂₂ row of GLS3 Table 5.3c. Exhaustive placement is
proved separately in `FourNormalizers.FixedSylow`.
-/

public section
namespace Sporadic.Mathieu.M22FourNormalizers
open Subgroup Theory.GroupTheory M22ValueBound.Concrete
open scoped Pointwise

/-- Involution fusion transports the checked standard centralizer order. -/
theorem involution_centralizer_card (u : M22) (hu : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set M22)) = 384 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (m22_involutions_isConj m22GeneratorAInM22 u
      M22RepresentativeKernel.representative_order hu)
  let e := MulAut.conj g
  have he : e m22GeneratorAInM22 = u := hg
  have hm : (centralizer ({m22GeneratorAInM22} : Set M22)).map e.toMonoidHom =
      centralizer ({u} : Set M22) := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← e.injective.eq_iff]
    simp only [map_mul, MulEquiv.apply_symm_apply, he]
  rw [← hm, card_map_of_injective e.injective]
  exact M22RepresentativeKernel.centralizer_card

/-- A four-group's normalizer has order at most 2304: its automizer has order
at most six and its centralizer is contained in an involution centralizer. -/
theorem four_normalizer_card_le (V : Subgroup M22)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) :
    Nat.card (normalizer (V : Set M22)) ≤ 2304 := by
  let := hV
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  have hne : V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  obtain ⟨u, hu, hu1⟩ := V.bot_or_exists_ne_one.resolve_left hne
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu) hu1
  let f := V.normalizerMonoidHom
  have hk : Nat.card f.ker ≤ 384 := by
    rw [show f.ker = (centralizer (V : Set M22)).subgroupOf
      (normalizer (V : Set M22)) from normalizerMonoidHom_ker V,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (V : Set M22))).toEquiv]
    have hle : centralizer (V : Set M22) ≤ centralizer ({u} : Set M22) :=
      centralizer_le (Set.singleton_subset_iff.mpr hu)
    exact (card_le_of_le hle).trans_eq (involution_centralizer_card u hu2)
  have hi : f.ker.index ≤ 6 := by
    rw [index_ker]
    have h := Nat.card_le_card_of_injective (fun x : f.range => x.val) Subtype.val_injective
    rwa [IsKleinFour.card_mulAut V] at h
  rw [← f.ker.card_mul_index]
  exact Nat.mul_le_mul hk hi

/-- Normalizing a nontrivial subgroup of the hexad kernel preserves its
exact common fixed points, even for outer design automorphisms. -/
theorem outer_normalizer_le_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (V : Subgroup M22) (hV : V ≤ m22HexadPointwiseKernel B) (hne : V ≠ ⊥) :
    normalizer (V.map inclusion : Set m22DesignAut) ≤
      MulAction.stabilizer m22DesignAut B := by
  obtain ⟨u, hu, hu1⟩ := V.bot_or_exists_ne_one.resolve_left hne
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  apply (M22SolvableSylow.kernel_fixed_iff hB (hV hu) hu1 (g • a)).mp
  have hm : inclusion u ∈ V.map inclusion := mem_map_of_mem _ hu
  have hn := (mem_normalizer_iff.mp
    ((normalizer (V.map inclusion : Set m22DesignAut)).inv_mem hg) (inclusion u)).mp hm
  obtain ⟨v, hv, he⟩ := hn
  have hf : inclusion v • a = a := (mem_m22HexadPointwiseKernel B v).mp (hV hv) a ha
  have he' := congrArg (fun x : Fin 22 => g • x) hf
  rw [he] at he'
  change inclusion u • (g • a) = g • a
  simpa only [inv_inv, mul_smul, smul_inv_smul] using he'

private theorem comap_normalizer (V : Subgroup M22) :
    (normalizer (V.map inclusion : Set m22DesignAut)).comap inclusion =
      normalizer (V : Set M22) := by
  rw [comap_normalizer_eq_of_le_range (V.map_le_range inclusion),
    comap_map_eq_self_of_injective inclusion_injective]

/-- The full inner normalizer lies strictly inside the actual hexad stabilizer. -/
theorem normalizer_lt_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (V : Subgroup M22) (hVK : V ≤ m22HexadPointwiseKernel B)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) :
    normalizer (V : Set M22) < MulAction.stabilizer M22 B := by
  have hne : V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  have hle := Subgroup.comap_mono (f := inclusion) (outer_normalizer_le_hexad hB V hVK hne)
  rw [comap_normalizer] at hle
  change normalizer (V : Set M22) ≤ MulAction.stabilizer M22 B at hle
  apply lt_of_le_of_ne hle
  intro he
  have hb := four_normalizer_card_le V hV hc
  rw [he, m22Hexad_stabilizer_card hB] at hb
  omega

/-- Strictness persists in the full design group because its restriction to
the inner subgroup already has a strict overgroup. -/
theorem outer_normalizer_lt_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (V : Subgroup M22) (hVK : V ≤ m22HexadPointwiseKernel B)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) :
    normalizer (V.map inclusion : Set m22DesignAut) <
      MulAction.stabilizer m22DesignAut B := by
  have hne : V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  apply lt_of_le_of_ne (outer_normalizer_le_hexad hB V hVK hne)
  intro he
  have he' := congrArg (Subgroup.comap inclusion) he
  rw [comap_normalizer] at he'
  exact (normalizer_lt_hexad hB V hVK hV hc).ne he'

/-- The inner hexad stabilizer has characteristic two. -/
theorem hexad_characteristicTwo {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    generalizedFitting (MulAction.stabilizer M22 B) =
      pCore 2 (MulAction.stabilizer M22 B) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (m22Hexad_stabilizer_core_selfCentralizing hB)

private noncomputable def innerHexadEquiv (B : Finset (Fin 22)) :
    inner.subgroupOf (MulAction.stabilizer m22DesignAut B) ≃*
      MulAction.stabilizer M22 B where
  toFun x := ⟨⟨x.val.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨inclusion x.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The full design hexad stabilizer also has characteristic two. -/
theorem outer_hexad_characteristicTwo {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    generalizedFitting (MulAction.stabilizer m22DesignAut B) =
      pCore 2 (MulAction.stabilizer m22DesignAut B) := by
  let H := MulAction.stabilizer m22DesignAut B
  let N := M22ValueBound.Concrete.inner.subgroupOf H
  have hN : centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (innerHexadEquiv B)).mpr
      (m22Hexad_stabilizer_core_selfCentralizing hB)
  have he : M22ValueBound.Concrete.inner = m22EvenDesignAut := by
    ext g
    change g.val ∈ M22 ↔ g.val ∈ alternatingGroup (Fin 22)
    exact and_iff_right g.property
  have hi : M22ValueBound.Concrete.inner.index = 2 := by
    rw [he]
    exact m22EvenDesignAut_index
  have hd : Nat.card (H ⧸ N) ∣ 2 := hi ▸
    M22ValueBound.Concrete.inner.relIndex_dvd_index_of_normal H
  have hq : IsPGroup 2 (H ⧸ N) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact IsPGroup.of_card (n := 0) h
    · exact IsPGroup.of_card (n := 1) h
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_pCore_le_of_normal_pGroup_quotient N hN hq)

end Sporadic.Mathieu.M22FourNormalizers
