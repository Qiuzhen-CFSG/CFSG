module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.MarkedLine.FieldSpan
public import Theory.GroupTheory.PGroup.OmegaImage

/-!
# Complete scalar spectrum of the actual odd Hall subgroup

The literal residual intersection is its Sylow normalizer. Its diagonal
quotient and the relative Hall index show that the original Hall group has
order q-1. Its known faithful unit-group embedding is therefore onto.
Transport O³ and the omega-three subgroup through this isomorphism.
In any triangular marking the actual Cartan part has an injective diagonal
map. Uniqueness of a subgroup of each order in the cyclic unit group gives
exactly the required scalar spectrum. Together with the finite-field span,
this identifies the original flag preimage as a field line and realizes it
as an individual commutator in the original conjugate action.

Only earlier natural-action and Cartan source inputs remain, discharged by
qt-d-1222-shadow-common-action. No Hall spectrum or field-span input remains.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
private theorem cyclic_subgroup_eq_of_card {B : Type*} [CommGroup B] [Finite B]
    [IsCyclic B] (U W : Subgroup B) (hc : Nat.card U = Nat.card W) : U = W := by
  let N := (powMonoidHom (Nat.card U) : B →* B).ker
  have hU : U ≤ N := by
    intro u hu
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨u,hu⟩ : U)))
  have hW : W ≤ N := by
    intro w hw
    change w ^ Nat.card U = 1
    rw [hc]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨w,hw⟩ : W)))
  have hN : Nat.card N = Nat.card U := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right U.card_subgroup_dvd_card]
  exact (eq_of_le_of_card_ge hU hN.le).trans
    (eq_of_le_of_card_ge hW (hN.trans hc).le).symm

private theorem extract_map {B C : Type*} [Group B] [Group C] (e : B ≃* C) :
    ((pResidual 3 B) ⊔ (omega₁ (pCore 3 B) (p := 3)).map (pCore 3 B).subtype).map
      e.toMonoidHom =
    (pResidual 3 C) ⊔ (omega₁ (pCore 3 C) (p := 3)).map (pCore 3 C).subtype := by
  rw [Subgroup.map_sup,map_pResidual,Subgroup.map_map]
  congr 1
  apply map_omega_eq_of_injective_of_range_eq
    (e.toMonoidHom.comp (pCore 3 B).subtype) (pCore 3 C).subtype
    (e.injective.comp (pCore 3 B).subtype_injective) (pCore 3 C).subtype_injective
  rw [MonoidHom.range_comp,range_subtype,range_subtype,pCore_map_iso]

private theorem oddCartan_card_of_equiv {G : Type*} [Group G] (A : Subgroup G)
    (F : BinaryField) (e : A ≃* F.Carrierˣ) :
    Nat.card (oddCartanPart A) = Nat.card (torusCartanPart F) := by
  rw [oddCartanPart,card_map_of_injective A.subtype_injective]
  rw [torusCartanPart,← extract_map e,card_map_of_injective e.injective]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The actual odd Hall subgroup has the complete split-torus order. -/
theorem source_hall_card (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    Nat.card A = Nat.card S.field.Carrierˣ := by
  let B := H ⊓ normalizer (L : Set G)
  let K := outsideResidual H
  let P := residualSylow s
  let N := normalizer (P : Set K)
  let j : N →* B :=
    { toFun x := ⟨x.val.val, outsideResidual_le H x.val.property,
        (source_residual_borel s c).ge x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => (z : G)) he
  obtain ⟨f,hf,_⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal
    (quotientMap c) (quotientMap_surjective c) P
    (by rw [quotientMap_ker]; exact pCore_isPGroup.le_sylow_of_normal _)
  have hd : Nat.card S.field.Carrierˣ ∣ Nat.card B :=
    (card_dvd_of_surjective f hf).trans (card_dvd_of_injective j hj)
  have ho : Odd (Nat.card S.field.Carrierˣ) := by
    rw [Nat.card_units,S.field.card_eq]
    have hdiv : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 (by have := S.field.degree_pos; omega)
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd]
    have hpos := Nat.one_le_pow S.field.degree 2 (by decide : 0 < (2 : ℕ))
    omega
  have hcop : Nat.Coprime (Nat.card S.field.Carrierˣ) (A.subgroupOf B).index := by
    apply Nat.coprime_of_dvd
    intro p hp hpu hpi
    have hp2 : p = 2 := Classical.not_not.mp (hHall.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpi)
    subst p
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpu)
  have hlower : Nat.card S.field.Carrierˣ ∣ Nat.card A := by
    rw [← (A.subgroupOf B).card_mul_index] at hd
    have hh := hcop.dvd_of_dvd_mul_right hd
    rwa [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hh
  have hoA : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  apply Nat.dvd_antisymm _ hlower
  simpa only [Nat.card_units,S.field.card_eq] using source_card_dvd s c A hA hoA

/-- An actual Hall marking onto the full field-unit group. -/
theorem source_hall_units_equiv (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    Nonempty (A ≃* S.field.Carrierˣ) := by
  have hoA : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  obtain ⟨f,hf⟩ := source_units_embedding s c A hA hoA
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf,source_hall_card s c A hA hHall⟩)⟩

private theorem two_group_disjoint_odd {B : Type*} [Group B] [Finite B]
    (P Q : Subgroup B) (hp : IsPGroup 2 P) (hq : Odd (Nat.card Q)) :
    Disjoint P Q := by
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [hn]
  exact (Nat.coprime_two_left.mpr hq).pow_left n

private theorem odd_injective_through_two_kernel
    {B C E : Type*} [Group B] [Finite B] [Group C] [Finite C] [Group E]
    (i : B →* C) (hi : Function.Injective i) (ho : Odd (Nat.card B))
    (q : C →* E) (hq : IsPGroup 2 q.ker) : Function.Injective (q.comp i) := by
  have hd := two_group_disjoint_odd q.ker i.range hq
    (ho.of_dvd_nat (card_range_dvd i))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro b hb
  apply mem_bot.mpr
  apply hi
  exact (disjoint_def.mp hd hb ⟨b,rfl⟩).trans i.map_one.symm

private theorem odd_triangular_coefficients {B E : Type*} [Group B] [Finite B]
    [Field E] [Finite E] [CharP E 2]
    (φ : B →* SL(2,E)) (hφ : Function.Injective φ) (ho : Odd (Nat.card B))
    (htri : ∀ b, (φ b).val 1 0 = 0) :
    ∃ f : B →* Eˣ, Function.Injective f ∧ ∀ b, (f b : E) = (φ b).val 0 0 := by
  let f : B →* Eˣ :=
    { toFun d := Units.mk0 ((φ d).val 0 0) (by
        have hd : (φ d).val 0 0 * (φ d).val 1 1 = 1 := by
          simpa only [det_fin_two,htri d,mul_zero,sub_zero] using (φ d).property
        exact left_ne_zero_of_mul_eq_one hd)
      map_one' := by apply Units.ext; simp only [map_one]; rfl
      map_mul' d e := by
        apply Units.ext
        change (φ (d*e)).val 0 0 = (φ d).val 0 0 * (φ e).val 0 0
        rw [map_mul]
        simp [mul_apply,Fin.sum_univ_two,htri e] }
  have hd : Disjoint (SpecialLinearGroup.upperUnipotent E) φ.range :=
    two_group_disjoint_odd _ _ (SpecialLinearGroup.upperUnipotentSylow E 2).isPGroup'
      (ho.of_dvd_nat (card_range_dvd φ))
  refine ⟨f,?_,fun b => rfl⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro b hb
  apply mem_bot.mpr
  apply hφ
  have hu : φ b ∈ SpecialLinearGroup.upperUnipotent E :=
    by
      have h00 : (φ b).val 0 0 = 1 := congrArg Units.val hb
      have h11 : (φ b).val 1 1 = 1 := by
        simpa only [det_fin_two,h00,htri b,one_mul,mul_zero,sub_zero] using (φ b).property
      refine (SpecialLinearGroup.mem_upperUnipotent E _).mpr ⟨(φ b).val 0 1,?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe,h00,htri b,h11]
  exact (disjoint_def.mp hd hu ⟨b,rfl⟩).trans φ.map_one.symm

/-- Triangular placement of the actual odd Cartan part recovers its whole
coefficient spectrum, including the omega-three factor. -/
theorem source_torus_scalar_spectrum (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (b : SL(2,S.field.Carrier))
    (htri : ∀ k : outsideResidual H, (k : G) ∈ oddCartanPart A →
      (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 1 0 = 0) :
    torusScalarSet S.field ⊆ cartanScalarSet c b (oddCartanPart A) := by
  have hoA : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have ho : Odd (Nat.card (oddCartanPart A)) :=
    hoA.of_dvd_nat (card_dvd_of_le (oddCartanPart_le A))
  have hAK := oddCartanPart_le_residual_of_hall _ A hA hHall
  let i := inclusion hAK
  let φ := (MulAut.conj b).toMonoidHom.comp ((quotientMap c).comp i)
  have hφ : Function.Injective φ := (MulAut.conj b).injective.comp
    (odd_injective_through_two_kernel i (inclusion_injective hAK) ho (quotientMap c)
      (by rw [quotientMap_ker]; exact pCore_isPGroup))
  obtain ⟨f,hf,hcoeff⟩ := odd_triangular_coefficients φ hφ ho
    (fun d => htri (i d) d.property)
  obtain ⟨e⟩ := source_hall_units_equiv s c A hA hHall
  have hcard : Nat.card f.range = Nat.card (torusCartanPart S.field) :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans
      (oddCartan_card_of_equiv A S.field e)
  have hrange : f.range = torusCartanPart S.field :=
    cyclic_subgroup_eq_of_card _ _ hcard
  rintro a ⟨u,rfl⟩
  obtain ⟨d,hd⟩ := (hrange.symm ▸ u.property : u.val ∈ f.range)
  refine ⟨i d,d.property,?_⟩
  exact (hcoeff d).symm.trans (congrArg Units.val hd)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The genuine Hall subgroup supplies the scalar-span premise in compatible
coordinates for the original line. There is no scalar-spectrum callback. -/
theorem source_marked_line_of_hall
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (s : Hypothesis1131At D S U₁ H)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (cK : NaturalQuotientMarking T H S.field) (b : SL(2,S.field.Carrier))
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom)
      S.field cK.multiplicity)
    (he : ∀ (v : omegaClosure T H) (i : Fin cK.multiplicity),
      (n.coordinates v).toAdd i = ((cK.changeBasis b).coordinates v).toAdd i)
    (D_H : Subgroup G)
    (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆) :
    ∃ E : Submodule S.field.Carrier (Fin cK.multiplicity → Fin 2 → S.field.Carrier),
      Module.finrank S.field.Carrier E = 1 ∧ E ≤ n.fixedSpace ∧
      n.liftSpace E = D.centralQuotientPreimage U₁ ∧
      ∃ u : omegaClosure T H,
        (u : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (u : G)⁆ = D.centralQuotientPreimage U₁ := by
  have hne : D.centralQuotientPreimage U₁ ≠ ⊥ := by
    intro hz
    have hc := source_flag_line_card c f hline hfixed
    rw [hz,Subgroup.card_bot] at hc
    have := Finite.one_lt_card (α := S.field.Carrier)
    omega
  have htri := cK.cartan_lowerLeft_eq_zero b n he (D.centralQuotientPreimage U₁)
    (oddCartanPart D_H) hcontain hne hcomm
  have hspan : AddSubgroup.closure (cartanScalarSet cK b (oddCartanPart D_H)) = ⊤ := by
    apply top_unique
    rw [← torusScalarSet_additive_closure S.field]
    exact AddSubgroup.closure_mono (Hall.source_torus_scalar_spectrum s cK D_H hDH hHall b htri)
  exact source_marked_line_of_cartan_span c f hline hfixed g cK b n he D_H hcontain hcomm hspan

/-- Complete doubled-case original-line identification, retaining the full
residual intertwiner, original quotient and actual commutator witness. -/
theorem source_doubled_marked_line
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hSL : ∃ e, c = Coordinates.sl3 e)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (s : Hypothesis1131At D S U₁ H) (hcounter : ¬ Proposition1132At D S U₁ H)
    (g : G) (cK : NaturalQuotientMarking T H S.field) (hm : cK.multiplicity = 2)
    (hfixedL : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixedK : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))
    (D_H X : Subgroup G)
    (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hDKL : oddCartanPart D_H ≤ outsideResidual H ⊓ L)
    (hX : IsCartan T L X) (hDX : oddCartanPart D_H ≤ X)
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆)
 :
    ∃ (b : SL(2,S.field.Carrier))
      (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 2)
      (E : Submodule S.field.Carrier (Fin 2 → Fin 2 → S.field.Carrier)),
      Module.finrank S.field.Carrier E = 1 ∧ E ≤ n.fixedSpace ∧
      n.liftSpace E = D.centralQuotientPreimage U₁ ∧
      (∀ (k : outsideResidual H) (v : omegaClosure T H) (i : Fin 2),
        (n.coordinates (residualAction T H k v)).toAdd i =
          (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val *ᵥ
            (n.coordinates v).toAdd i) ∧
      ∃ u : omegaClosure T H,
        (u : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (u : G)⁆ = D.centralQuotientPreimage U₁ := by
  exact source_doubled_marked_line_of_hall_spectrum c f hSL hline s hcounter
    g cK hm hfixedL hfixedK hAH P hP D_H X hDH hHall hDKL hX hDX hcontain hcomm
    (Hall.source_torus_scalar_spectrum s cK D_H hDH hHall)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
