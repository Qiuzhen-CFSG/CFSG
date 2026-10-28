module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.PlaneKernels
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.Representation.HexacodeAction.PairCore
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Excluding outer best offenders in the hexacode action

An odd involution is semilinear for the nontrivial automorphism of `F₄`, so
its fixed space has binary codimension three.  The faithful coordinate image
of an elementary two-group embeds in `S₆`, hence has rank at most three.
Equality for a best offender would force its fixed space to equal the odd
involution's fixed space.  Semilinear descent says those fixed vectors span
the whole `F₄`-module, while every even element is `F₄`-linear; consequently
the even part of the offender is trivial, a contradiction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.3,
printed p.453 (PDF p.464).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders

private theorem fixedCodim_mono
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G} (hBA : B ≤ A) :
    fixedCodim ρ B ≤ fixedCodim ρ A := by
  have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ hBA)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private theorem fixedSpace_eq_of_fixedCodim_eq
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G} (hBA : B ≤ A)
    (hcodim : fixedCodim ρ A = fixedCodim ρ B) :
    fixedSpace ρ A = fixedSpace ρ B := by
  apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ hBA)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private noncomputable def sixToSeven : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 7) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

private theorem sixToSeven_injective : Function.Injective sixToSeven :=
  Equiv.Perm.viaEmbeddingHom_injective Fin.castSuccEmb

private theorem rank_le_three (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A) : rank A ≤ 3 := by
  let f : HexAutomorphisms →* Equiv.Perm (Fin 6) := hexCoordinateSixHom
  let E : Subgroup (Equiv.Perm (Fin 6)) := A.map f
  have hE : IsElementaryAbelian 2 E :=
    @IsElementaryAbelian.map 2 (by infer_instance) HexAutomorphisms
      (Equiv.Perm (Fin 6)) inferInstance inferInstance A hA.2 f
  let fA0 : A →* Equiv.Perm (Fin 6) := f.comp A.subtype
  let fA : A →* E := fA0.codRestrict E (by
    intro x
    exact ⟨x, x.property, rfl⟩)
  have hfA : Function.Injective fA := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val
      (Representation.Hexacode.coordinate_injective_on_two_subgroup A hA.2.isPGroup
        (congrArg Subtype.val h))
  have hfAsurj : Function.Surjective fA := by
    intro y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  have hcardE : Nat.card E = Nat.card A := by
    exact (Nat.card_congr (MulEquiv.ofBijective fA ⟨hfA, hfAsurj⟩).toEquiv).symm
  let E' : Subgroup (Equiv.Perm (Fin 7)) := E.map sixToSeven
  have hE' : IsElementaryAbelian 2 E' :=
    @IsElementaryAbelian.map 2 (by infer_instance) (Equiv.Perm (Fin 6))
      (Equiv.Perm (Fin 7)) inferInstance inferInstance E hE sixToSeven
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective sixToSeven_injective
  have hbound : Nat.card E' ≤ 8 :=
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le hE'
  have hpow : Nat.card A = 2 ^ rank A := hA.card_eq_two_pow_rank
  rw [hcardE', hcardE] at hbound
  rw [hpow] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

theorem outer_bestOffender_le_even
    (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender Hexacode.action A) :
    A ≤ hexSign.ker := by
  by_contra hle
  have hexists : ∃ g, g ∈ A ∧ g ∉ hexSign.ker := by
    by_contra h
    apply hle
    intro g hgA
    by_contra hgn
    exact h ⟨g, hgA, hgn⟩
  obtain ⟨g, hgA, hgne⟩ := hexists
  change hexSign g ≠ 1 at hgne
  have hgod : hexSign g = -1 := by
    rcases Int.units_eq_one_or (hexSign g) with h | h
    · exact (hgne h).elim
    · exact h
  have hg1 : g ≠ 1 := by
    intro hg
    rw [hg] at hgod
    simp at hgod
  have hgpow : g ^ 2 = 1 :=
    @elemPow_eq_one_of_isElementaryAbelian 2 HexAutomorphisms inferInstance A hA.1.2 g hgA
  have hgord : orderOf g = 2 := orderOf_eq_prime hgpow hg1
  have hσsq : SL2FourNatural.fieldFrobenius ^ 2 = 1 := by
    apply RingEquiv.ext
    intro c
    change SL2FourNatural.fieldFrobenius (SL2FourNatural.fieldFrobenius c) = c
    exact SL2FourNatural.fieldFrobenius_involutive c
  have hσord : orderOf SL2FourNatural.fieldFrobenius = 2 :=
    orderOf_eq_prime hσsq Hexacode.fieldFrobenius_ne_id
  have hsemi (c : Hexacode.F) (v : hexacode) :
      Hexacode.action g (c • v) = SL2FourNatural.fieldFrobenius c •
        Hexacode.action g v :=
    Hexacode.action_odd_smul g hgod c v
  have hformula :=
    Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula
      Hexacode.action (p := 2) (by decide) g hgord
      SL2FourNatural.fieldFrobenius hσord hsemi
  have hfixedg : fixedCodim Hexacode.action (Subgroup.zpowers g) = 3 := by
    rw [Hexacode.field_finrank] at hformula
    have hF : Module.finrank (ZMod 2) Hexacode.F = 2 := by
      exact QuadraticAlgebra.finrank_eq_two _ _
    rw [hF] at hformula
    omega
  have hrank : rank A = 3 := by
    have hupper : fixedCodim Hexacode.action A ≤ rank A :=
      hA.isOffender Hexacode.action |>.2
    have hlow : 3 ≤ fixedCodim Hexacode.action A := by
      calc
        3 = fixedCodim Hexacode.action (Subgroup.zpowers g) := hfixedg.symm
        _ ≤ fixedCodim Hexacode.action A :=
          fixedCodim_mono Hexacode.action (Subgroup.zpowers_le.mpr hgA)
    exact le_antisymm (rank_le_three A hA.1) (by omega)
  have hcodimA : fixedCodim Hexacode.action A = 3 := by
    have hupper : fixedCodim Hexacode.action A ≤ rank A :=
      hA.isOffender Hexacode.action |>.2
    have hlow : 3 ≤ fixedCodim Hexacode.action A := by
      calc
        3 = fixedCodim Hexacode.action (Subgroup.zpowers g) := hfixedg.symm
        _ ≤ fixedCodim Hexacode.action A :=
          fixedCodim_mono Hexacode.action (Subgroup.zpowers_le.mpr hgA)
    omega
  have hfixed : fixedSpace Hexacode.action A =
      fixedSpace Hexacode.action (Subgroup.zpowers g) :=
    fixedSpace_eq_of_fixedCodim_eq Hexacode.action
      (Subgroup.zpowers_le.mpr hgA) (hcodimA.trans hfixedg.symm)
  have hnotle : ¬ A ≤ Subgroup.zpowers g := by
    intro hleA
    have hc := Subgroup.card_le_of_le hleA
    rw [hA.1.card_eq_two_pow_rank, hrank, Nat.card_zpowers, hgord] at hc
    norm_num at hc
  have hexistsb : ∃ b, b ∈ A ∧ b ∉ Subgroup.zpowers g := by
    by_contra h
    apply hnotle
    intro b hbA
    by_contra hbnot
    exact h ⟨b, hbA, hbnot⟩
  obtain ⟨b, hbA, hbnot⟩ := hexistsb
  have hb1 : b ≠ 1 := by
    intro hb
    apply hbnot
    rw [hb]
    exact Subgroup.one_mem (Subgroup.zpowers g)
  have hginv : g⁻¹ = g := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hgpow
  have heven : ∃ a ∈ A, a ≠ 1 ∧ hexSign a = 1 := by
    rcases Int.units_eq_one_or (hexSign b) with hbEven | hbOdd
    · exact ⟨b, hbA, hb1, hbEven⟩
    · let a := b * g
      have haA : a ∈ A := A.mul_mem hbA hgA
      have haEven : hexSign a = 1 := by
        simp [a, hbOdd, hgod]
      have ha1 : a ≠ 1 := by
        intro ha
        have hbg : b = g := by
          calc
            b = g⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [a] using ha)
            _ = g := hginv
        apply hbnot
        rw [hbg]
        exact Subgroup.mem_zpowers g
      exact ⟨a, haA, ha1, haEven⟩
  obtain ⟨a, haA, ha1, haEven⟩ := heven
  let H : Subgroup HexAutomorphisms := Subgroup.zpowers g
  let γ : H := ⟨g, Subgroup.mem_zpowers g⟩
  let δ : Subgroup.zpowers SL2FourNatural.fieldFrobenius :=
    ⟨SL2FourNatural.fieldFrobenius, Subgroup.mem_zpowers _⟩
  have hγ : ∀ y : H, y ∈ Subgroup.zpowers γ := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  have hδ : ∀ y : Subgroup.zpowers SL2FourNatural.fieldFrobenius, y ∈
      Subgroup.zpowers δ := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  have hγord : orderOf γ = orderOf g := by
    rw [← Subgroup.orderOf_coe γ, ← Subgroup.orderOf_coe γ.val]
  have hδord : orderOf δ = orderOf SL2FourNatural.fieldFrobenius := by
    exact (Subgroup.orderOf_coe δ).symm
  have hord : orderOf γ = orderOf δ := by
    calc
      orderOf γ = orderOf g := hγord
      _ = orderOf SL2FourNatural.fieldFrobenius := hgord.trans hσord.symm
      _ = orderOf δ := hδord.symm
  let e : H ≃* Subgroup.zpowers SL2FourNatural.fieldFrobenius :=
    mulEquivOfOrderOfEq hγ hδ hord
  let τ : H →* (Hexacode.F ≃+* Hexacode.F) :=
    (Subgroup.zpowers SL2FourNatural.fieldFrobenius).subtype.comp e.toMonoidHom
  have hτ : Function.Injective τ := by
    exact Subtype.val_injective.comp e.injective
  have hτγ : τ γ = SL2FourNatural.fieldFrobenius := by
    change ((mulEquivOfOrderOfEq hγ hδ hord γ :
        Subgroup.zpowers SL2FourNatural.fieldFrobenius) :
        Hexacode.F ≃+* Hexacode.F) = _
    rw [mulEquivOfOrderOfEq_apply_gen]
  have hsemiH : ∀ (x : H) (c : Hexacode.F) (v : hexacode),
      Hexacode.action x.val (c • v) = τ x c • Hexacode.action x.val v := by
    intro x
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hγ x)
    subst x
    induction n with
    | zero => intro c v; simp [τ]
    | succ n ih =>
      intro c v
      simp only [pow_succ', map_mul]
      change Hexacode.action γ.val (Hexacode.action (γ ^ n).val (c • v)) =
        (τ γ) ((τ (γ ^ n)) c) •
          Hexacode.action γ.val (Hexacode.action (γ ^ n).val v)
      rw [ih, hτγ]
      exact hsemi _ _
  have hspan : Submodule.span Hexacode.F {v : hexacode |
      ∀ x : H, Hexacode.action x.val v = v} = ⊤ := by
    let : Fintype H := Fintype.ofFinite H
    exact Representation.FiniteFieldSemilinearDisplacement.Descent.span_fixed_eq_top
      (Hexacode.action.comp H.subtype) τ hτ (by
        intro x c v
        exact hsemiH x c v)
  let U : Submodule Hexacode.F hexacode :=
    { carrier := {v | Hexacode.action a v = v}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        change Hexacode.action a (v + w) = v + w
        change Hexacode.action a v = v at hv
        change Hexacode.action a w = w at hw
        rw [map_add, hv, hw]
      smul_mem' := by
        intro c v hv
        change Hexacode.action a (c • v) = c • v
        change Hexacode.action a v = v at hv
        rw [Hexacode.action_even_smul a haEven, hv] }
  have hspanU : Submodule.span Hexacode.F {v : hexacode |
      ∀ x : H, Hexacode.action x.val v = v} ≤ U := by
    apply Submodule.span_le.mpr
    intro v hv
    have hvH : v ∈ fixedSpace Hexacode.action (Subgroup.zpowers g) := by
      change ∀ x : H, Hexacode.action x.val v = v
      exact hv
    have hvA : v ∈ fixedSpace Hexacode.action A := by
      rw [hfixed]
      exact hvH
    exact hvA ⟨a, haA⟩
  have hU : U = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hspanU
  have ha_id : ∀ v : hexacode, Hexacode.action a v = v := by
    intro v
    have hvU : v ∈ U := by
      rw [hU]
      exact Submodule.mem_top
    exact hvU
  have : a = 1 := by
    apply Hexacode.action_injective
    apply LinearMap.ext
    intro v
    exact ha_id v
  exact ha1 this

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
