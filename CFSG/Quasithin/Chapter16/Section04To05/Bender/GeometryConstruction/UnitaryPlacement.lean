module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.UnitaryPlacement.Intrinsic
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.Residual
public import CFSG.Quasithin.Chapter16.Section01To02.Local

/-!
# Unitary placement for the original source conjugator

For Proposition 16.5.1, Yᵤ is O³(O²(C_L(u))) when n ≠ 3, and O²(C_L(u))
when n = 3. This differs from the modification in Notation 16.5.5.
A two-subgroup contained in O²(C_L(u)) automatically survives passage to
its three-residual. Thus only the two-residual calculation is model dependent.

An involution in Ω₁(R) has a nontrivial Ω₁(T_L) component because R acts
faithfully on L. Its other factor centralizes L, so both elements have the
same centralizer in L. This reduces the placement to the intrinsic Sylow
centralizer calculation, retaining the original conjugator throughout.

`componentSylow_le_conjugate` supplies the intrinsic calculation from the
actual PSU₃ model and obtains T_L ≤ L^g. `unitary_mover` then proves that
the same g preserves T_L and V and carries Ω₁(T_C) to Ω₁(R).
The local action, earlier trivial-center conclusion, and residual-containment
alternatives of 16.4.8 remain explicit inputs for the source assembly owner.
The fixed-field order is 2ⁿ, so n = 2 uses matrices over a field of order 16.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.8, pp.1187–1188, and Proposition 16.5.1, p.1194.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.UnitaryPlacement
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The parameter-dependent Yᵤ on p.1194; the superscript three denotes a residual. -/
noncomputable def residual (n : ℕ) (L : Subgroup G) (u : G) : Subgroup G := by
  classical
  exact if n = 3 then involutionTwoResidual L u else
    (pResidual 3 (involutionTwoResidual L u)).map (involutionTwoResidual L u).subtype

/-- The source modification only shrinks the two-residual. -/
theorem residual_le (n : ℕ) (L : Subgroup G) (u : G) :
    residual n L u ≤ involutionTwoResidual L u := by
  classical
  unfold residual
  split_ifs
  · exact le_rfl
  · exact map_subtype_le _

/-- For two-subgroups, the extra three-residual makes no difference to containment. -/
theorem twoSubgroup_le_residual_iff (n : ℕ) {P L : Subgroup G} {u : G}
    (hP : IsPGroup 2 P) :
    P ≤ residual n L u ↔ P ≤ involutionTwoResidual L u := by
  refine ⟨fun h => h.trans (residual_le n L u), fun h => ?_⟩
  classical
  unfold residual
  split_ifs
  · exact h
  · intro x hx
    refine ⟨⟨x, h hx⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    obtain ⟨k, hk⟩ := hP.exists_orderOf_dvd_pow ⟨x, hx⟩
    have hxorder : orderOf (⟨x, h hx⟩ : involutionTwoResidual L u) =
        orderOf (⟨x, hx⟩ : P) := by rw [orderOf_mk, orderOf_mk]
    rw [hxorder]
    exact ((by decide : Nat.Coprime 3 2).pow_right k).of_dvd_right hk

/-- The exact residual-containment consequence needed from 16.4.8. Its
exceptional branch is allowed only when n ≠ 3. -/
theorem residual_le_of_source_alternatives {n : ℕ} {L M : Subgroup G} {u : G}
    (hsource : involutionTwoResidual L u ≤ M ∨
      (n ≠ 3 ∧ (pResidual 3 (involutionTwoResidual L u)).map
        (involutionTwoResidual L u).subtype ≤ M)) : residual n L u ≤ M := by
  rcases hsource with h | ⟨hn, h⟩
  · exact (residual_le n L u).trans h
  · simpa only [residual, if_neg hn] using h

/-- Multiplication by an element centralizing L does not change the centralizer in L. -/
theorem centralizer_eq_of_centralizing_factor {L : Subgroup G} {c v : G}
    (hc : c ∈ centralizer (L : Set G)) :
    L ⊓ centralizer ({c * v} : Set G) = L ⊓ centralizer ({v} : Set G) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, hxcv⟩
    refine ⟨hx, ?_⟩
    have hxc := mem_centralizer_iff.mp hc x hx
    apply mul_left_cancel (a := c)
    symm
    calc
      c * (v * x) = (c * v) * x := (mul_assoc _ _ _).symm
      _ = x * (c * v) := hxcv.symm
      _ = c * (x * v) := by rw [← mul_assoc, hxc, mul_assoc]
  · rintro ⟨hx, hxv⟩
    refine ⟨hx, ?_⟩
    have hxc := mem_centralizer_iff.mp hc x hx
    symm
    calc
      (c * v) * x = c * (v * x) := mul_assoc _ _ _
      _ = c * (x * v) := by rw [hxv]
      _ = x * (c * v) := by rw [← mul_assoc, ← hxc, mul_assoc]

/-- Intrinsic centralizers in L have the expected ambient image. -/
theorem map_intrinsic_centralizer (L : Subgroup G) (v : L) :
    (centralizer ({v} : Set L)).map L.subtype =
      L ⊓ centralizer ({(v : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
  · rintro ⟨hxL, hxv⟩
    refine ⟨⟨x, hxL⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hxv)

/-- A genuine trivial-center conclusion from the earlier cover theorem lifts
its quotient model without changing the fixed-field convention. -/
theorem unitary_model_of_center_eq_bot {L : Subgroup G} {n : ℕ}
    (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n))
    (hcenter : center L = ⊥) : ClassicalGroup.IsPSU L 3 (2 ^ n) :=
  hmodel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm

variable [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}

/-- Sylow restriction identifies T_L with the image of an actual Sylow subgroup of L. -/
theorem componentSylow_image (h : StandardSetup T z L) :
    ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype = componentSylow T L := by
  obtain ⟨S, hS⟩ := h.toCentralComponentSetup.exists_component_sylow
  refine ⟨S, ?_⟩
  rw [hS]
  ext x
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨hy, y.property⟩,
    fun hx => ⟨⟨x, hx.2⟩, hx.1, rfl⟩⟩

/-- Choose a genuine involution of Ω₁(R), using its equality with Ω₁(T_C)^g. -/
theorem exists_omega_involution (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (d : LocalAction T L R n) :
    ∃ u ∈ omegaOneAmbient R, orderOf u = 2 := by
  let := d.commuting_elementary
  let := d.component_elementary
  let := space_elementary_of_factors (T := T) (L := L)
  have he := omega_conjugate (h.eq_conjugate_commutingSylow hR htransport)
  have hne : omegaOneAmbient R ≠ ⊥ := by
    rw [he]
    exact fun hb => commuting_omega_nontrivial h.toStandardSetup
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hb)
  obtain ⟨u, hu, hune⟩ := (omegaOneAmbient R).bot_or_exists_ne_one.resolve_left hne
  exact ⟨u, hu, orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian u (d.omega_le hu)) hune⟩

omit [Finite G] in
/-- Faithfulness makes the Ω₁(T_L) factor nonidentity. Its centralizer in L
is the centralizer of the original involution. -/
theorem exists_component_involution (d : LocalAction T L R n)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    {u : G} (hu : u ∈ omegaOneAmbient R) (hu2 : orderOf u = 2) :
    ∃ v ∈ omegaOneAmbient (componentSylow T L), orderOf v = 2 ∧
      L ⊓ centralizer ({u} : Set G) = L ⊓ centralizer ({v} : Set G) := by
  let A := omegaOneAmbient (commutingSylow T L)
  let B := omegaOneAmbient (componentSylow T L)
  have hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G) := by
    intro a b
    exact (mem_centralizer_iff.mp ((omegaOneAmbient_le _ a.property).2)
      b (omegaOneAmbient_le _ b.property).2).symm
  let f : A × B →* G := A.subtype.noncommCoprod B.subtype hcomm
  have hf : f.range = A ⊔ B := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm).trans
      (by rw [range_subtype, range_subtype])
  obtain ⟨⟨c, v⟩, hcv⟩ := (show u ∈ f.range by rw [hf]; exact d.omega_le hu)
  have hc : (c : G) ∈ centralizer (L : Set G) := (omegaOneAmbient_le _ c.property).2
  have hvne : (v : G) ≠ 1 := by
    intro hv
    have huC : u ∈ centralizer (L : Set G) := by
      have he : (c : G) * (v : G) = u := hcv
      rw [hv, mul_one] at he
      exact he ▸ hc
    have hu1 := disjoint_def.mp hfaith (omegaOneAmbient_le R hu) huC
    simp [hu1] at hu2
  let := d.component_elementary
  refine ⟨v, v.property, orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (v : G) v.property) hvne, ?_⟩
  have he : (c : G) * (v : G) = u := hcv
  rw [← he]
  exact centralizer_eq_of_centralizing_factor hc

/-- Transport the intrinsic unitary calculation to the ambient component,
without changing either the Sylow subgroup or the involution centralizer. -/
theorem componentSylow_le_twoResidual_of_intrinsic
    (h : StandardSetup T z L) {v : G}
    (hv : v ∈ componentSylow T L) (hv2 : orderOf v = 2)
    (hcalc : ∀ (S : Sylow 2 L) (w : L), w ∈ (S : Subgroup L) → orderOf w = 2 →
      (S : Subgroup L) ≤ (pResidual 2 (centralizer ({w} : Set L))).map
        (centralizer ({w} : Set L)).subtype) :
    componentSylow T L ≤ involutionTwoResidual L v := by
  obtain ⟨S, hS⟩ := componentSylow_image h
  obtain ⟨w, hw, rfl⟩ := (show v ∈ (S : Subgroup L).map L.subtype by rw [hS]; exact hv)
  have hw2 : orderOf w = 2 := by
    rw [← orderOf_injective L.subtype L.subtype_injective w]
    exact hv2
  have hm := map_mono (f := L.subtype) (hcalc S w hw hw2)
  rw [hS, map_embedded_pResidual, map_intrinsic_centralizer] at hm
  exact hm

/-- Complete group-theoretic assembly, conditional on the intrinsic unitary
centralizer calculation and the earlier source residual containment. -/
theorem componentSylow_le_conjugate_of_intrinsic
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (d : LocalAction T L R n)
    (hsource : ∀ u ∈ omegaOneAmbient R, orderOf u = 2 → residual n L u ≤ L.conjBy g)
    (hcalc : ∀ (S : Sylow 2 L) (w : L), w ∈ (S : Subgroup L) → orderOf w = 2 →
      (S : Subgroup L) ≤ (pResidual 2 (centralizer ({w} : Set L))).map
        (centralizer ({w} : Set L)).subtype) :
    componentSylow T L ≤ L.conjBy g := by
  obtain ⟨u, hu, hu2⟩ := exists_omega_involution h hR htransport d
  obtain ⟨v, hv, hv2, hcentralizer⟩ := exists_component_involution d hfaith hu hu2
  have htwo := componentSylow_le_twoResidual_of_intrinsic h.toStandardSetup
    (omegaOneAmbient_le _ hv) hv2 hcalc
  have he : involutionTwoResidual L u = involutionTwoResidual L v := by
    unfold involutionTwoResidual
    rw [hcentralizer]
  rw [← he] at htwo
  have hT : IsPGroup 2 (componentSylow T L) :=
    T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)
  exact ((twoSubgroup_le_residual_iff n hT).mpr htwo).trans (hsource u hu hu2)

/-- The unitary placement in 16.5.1 for the original source conjugator.
The actual unitary calculation discharges the intrinsic premise of the
general reduction. The remaining explicit inputs are the separately
constructed local action and the earlier cover and 16.4.8 conclusions. -/
theorem componentSylow_le_conjugate
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n))
    (hcenter : center L = ⊥) (d : LocalAction T L R n)
    (hsource : ∀ u ∈ R, orderOf u = 2 →
      involutionTwoResidual L u ≤ L.conjBy g ∨
        (n ≠ 3 ∧ (pResidual 3 (involutionTwoResidual L u)).map
          (involutionTwoResidual L u).subtype ≤ L.conjBy g)) :
    componentSylow T L ≤ L.conjBy g := by
  apply componentSylow_le_conjugate_of_intrinsic h hR htransport hfaith d
  · intro u hu hu2
    exact residual_le_of_source_alternatives (hsource u (omegaOneAmbient_le R hu) hu2)
  · exact Intrinsic.sylow_le_twoResidual n hn (unitary_model_of_center_eq_bot hmodel hcenter)

/-- All unitary moving-conjugator fields follow for the original g;
neither component containment nor preservation is an additional premise. -/
theorem unitary_mover
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n))
    (hcenter : center L = ⊥) (d : LocalAction T L R n)
    (hsource : ∀ u ∈ R, orderOf u = 2 →
      involutionTwoResidual L u ≤ L.conjBy g ∨
        (n ≠ 3 ∧ (pResidual 3 (involutionTwoResidual L u)).map
          (involutionTwoResidual L u).subtype ≤ L.conjBy g)) :
    g ∈ normalizer (componentSylow T L : Set G) ∧
    g ∈ normalizer (benderSpace T L : Set G) ∧
    (omegaOneAmbient (commutingSylow T L)).conjBy g = omegaOneAmbient R :=
  unitary_transport h hR htransport
    (componentSylow_le_conjugate h hR htransport hfaith hn hmodel hcenter d hsource) d.omega_le

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.UnitaryPlacement
