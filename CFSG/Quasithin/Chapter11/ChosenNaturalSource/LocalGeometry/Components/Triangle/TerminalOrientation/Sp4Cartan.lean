module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.Sp4ModelCartan
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.CartanJoinSp4

/-!
# The four literal cubic Cartan lines of a natural Sp₄(4) flag

The point and plane characters and the actual local quotient actions identify
all four lines in the original Cartan. Two are its residual intersections;
the other two are the full two-core quotient centralizers. The two-group
kernel transport preserves both the original residual and its complete core.
These identities permit comparison of two natural markings sharing three
of the lines without identifying their defining fields by their orders.
Source: Aschbacher--Smith, 11.1.2, printed p.764.
-/
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section
variable {A B : Type*} [Group A] [Group B] [Finite A]

omit [Finite A] in
private theorem odd_isTwoPerfect (U : Subgroup A) (ho : Odd (Nat.card U)) :
    IsPPerfect 2 U := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (U ⧸ N) = 1
  exact htwo.card_eq_or_dvd.resolve_right
    (fun hd => ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))

omit [Finite A] in
/-- An odd subgroup sees the actual residual lift, not only its image. -/
private theorem odd_inf_comap_map (q : A →* B) (hk : IsPGroup 2 q.ker)
    (R X : Subgroup A) (ho : Odd (Nat.card X))
    (hn : q.ker ≤ normalizer (R : Set A)) :
    X ⊓ (R.map q).comap q = X ⊓ R := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    apply le_of_isPPerfect_of_le_sup_of_normalizes
      (X ⊓ (R.map q).comap q) R q.ker
      (odd_isTwoPerfect _ (ho.of_dvd_nat (card_dvd_of_le inf_le_left))) hk hn
    simpa only [comap_map_eq] using
      (inf_le_right : X ⊓ (R.map q).comap q ≤ (R.map q).comap q)
  · exact inf_le_inf_left X (le_comap_map _ _)

private theorem residual_map_equiv (e : B ≃* B) [Finite B] (P : Subgroup B) :
    (solvableResidual (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype =
      ((solvableResidual P).map P.subtype).map e.toMonoidHom := by
  have hc : (P.map e.toMonoidHom).comap e.toMonoidHom = P := by
    rw [comap_map_eq, e.toMonoidHom.ker_eq_bot e.injective, sup_bot_eq]
  have h := map_solvableResidual_comap e.toMonoidHom e.surjective (P.map e.toMonoidHom)
  rw [hc] at h
  exact h.symm


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation

open Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.Sp4Cartan
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private abbrev c := Coordinates.sp4 m
private abbrev f := LocalGeometry.Sp4.flag m S
private abbrev a := MulAut.conj (LocalGeometry.Sp4.alignment m)
private abbrev r : L →* Sp S.field.Carrier := (a S m).symm.toMonoidHom.comp (c S m).quotientMap

private theorem r_ker : (r S m).ker = pCore 2 L := by
  ext x
  change (a S m).symm ((c S m).groupEquiv (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ _
  rw [(a S m).symm.map_eq_one_iff]
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
  rw [m.groupEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

private theorem residual_image (i : Fin 2) :
    (((f S m).Li i).subgroupOf L).map (r S m) =
      LocalGeometry.Sp4.standardLocal (F := S.field) i := by
  rw [r, ←map_map]
  change (((localResidual L ((c S m).preimage
    (LocalGeometry.Sp4.space m i.castSucc.succ))).subgroupOf L).map
      (c S m).quotientMap).map (a S m).symm.toMonoidHom = _
  rw [LocalGeometry.Sp4.localResidual_image,LocalGeometry.Sp4.modelStabilizer_space]
  change ((solvableResidual ((stabilizer (LocalGeometry.Sp4.ModelFlag.stage
    (F := S.field.Carrier) i.castSucc.succ)).map (a S m).toMonoidHom)).map
      ((stabilizer (LocalGeometry.Sp4.ModelFlag.stage (F := S.field.Carrier)
        i.castSucc.succ)).map (a S m).toMonoidHom).subtype).map
          (a S m).symm.toMonoidHom = _
  rw [residual_map_equiv,map_map]
  have he : (a S m).symm.toMonoidHom.comp (a S m).toMonoidHom = MonoidHom.id _ := by
    ext x : 1
    exact (a S m).symm_apply_apply x
  rw [he,map_id]
  fin_cases i
  · exact pointParabolic_solvableResidual_eq S.field.card_eq S.nonbinary
  · exact planeParabolic_solvableResidual_eq S.field.card_eq S.nonbinary

private theorem cartan_borel {X : Subgroup G} (hX : IsCartan T L X) (x : X) :
    r S m ⟨x,(hX.1 x.property).1⟩ ∈ Theory.SpecificGroups.SymplecticFour.borel := by
  have hn (i : Fin 2) : (c S m).quotientMap ⟨x,(hX.1 x.property).1⟩ ∈
      (c S m).modelStabilizer (LocalGeometry.Sp4.space m i.castSucc.succ) := by
    exact ((c S m).mem_normalizer_preimage_iff _ _).mp
      ((f S m).cartan_normalizes (LocalGeometry.Sp4.flag_inner_unique m S) hX i.castSucc x.property)
  have hh (i : Fin 2) : r S m ⟨x,(hX.1 x.property).1⟩ ∈
      stabilizer (LocalGeometry.Sp4.ModelFlag.stage (F := S.field.Carrier) i.castSucc.succ) := by
    have h := hn i
    rw [LocalGeometry.Sp4.modelStabilizer_space,mem_map_equiv] at h
    exact h
  exact ⟨hh 0,hh 1⟩

private def characters {X : Subgroup G} (hX : IsCartan T L X) :
    X →* S.field.Carrierˣ × S.field.Carrierˣ :=
  borelCharacters.comp (((r S m).comp (inclusion (hX.1.trans inf_le_left))).codRestrict
    Theory.SpecificGroups.SymplecticFour.borel (cartan_borel S m hX))

private theorem characters_injective {X : Subgroup G} (hX : IsCartan T L X) :
    Function.Injective (characters S m hX) := by
  let q := (r S m).comp (inclusion (hX.1.trans inf_le_left))
  have hkq : IsPGroup 2 q.ker := by
    change IsPGroup 2 ((r S m).ker.comap (inclusion (hX.1.trans inf_le_left)))
    rw [r_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have ho : Odd (Nat.card q.ker) := hX.odd.of_dvd_nat (card_subgroup_dvd_card _)
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    (card_eq_one.mp (hkq.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hu : q x ∈ unipotent := (borelCharacters_eq_one
    ⟨q x,cartan_borel S m hX x⟩).mp hx
  have hc : IsPGroup 2 (Subgroup.zpowers (q x)) :=
    (isPGroup_unipotent S.field.card_eq).to_le (zpowers_le.mpr hu)
  have hod : Odd (Nat.card (Subgroup.zpowers (q x))) := by
    rw [Nat.card_zpowers]
    exact hX.odd.of_dvd_nat ((orderOf_map_dvd q x).trans (orderOf_dvd_natCard (x := x)))
  have hz : q x = 1 := by
    have he : Subgroup.zpowers (q x) = ⊥ :=
      card_eq_one.mp (hc.card_eq_or_dvd.resolve_right hod.not_two_dvd_nat)
    exact he.le (mem_zpowers (q x))
  exact hq (hz.trans q.map_one.symm)

private theorem characters_membership {X : Subgroup G} (hX : IsCartan T L X)
    (i : Fin 2) (x : X) :
    (if i = 0 then (characters S m hX x).1 else (characters S m hX x).2) = 1 ↔
      (x : G) ∈ (f S m).Li i := by
  have hle : (f S m).Li i ≤ L := (localResidual_le _).trans inf_le_left
  have hkN : (r S m).ker ≤ normalizer (((f S m).Li i).subgroupOf L : Set L) := by
    rw [r_ker,← subgroupOf_normalizer_eq hle]
    have hp : pCore 2 L ≤ (T : Subgroup G).subgroupOf L := by
      rw [←(c S m).innerSylow_coe]
      exact pCore_isPGroup.le_sylow_of_normal _
    exact hp.trans (comap_mono ((f S m).sylow_normalizes_Li i))
  have he := odd_inf_comap_map (r S m)
    (by rw [r_ker]; exact pCore_isPGroup)
    (((f S m).Li i).subgroupOf L) (X.subgroupOf L)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe (hX.1.trans inf_le_left)).toEquiv]; exact hX.odd) hkN
  rw [residual_image] at he
  have hmem : r S m ⟨x,(hX.1 x.property).1⟩ ∈ LocalGeometry.Sp4.standardLocal (F := S.field) i ↔
      (x : G) ∈ (f S m).Li i := by
    constructor
    · intro hx
      exact (he.le ⟨x.property,hx⟩).2
    · intro hx
      exact (he.ge ⟨x.property,hx⟩).2
  rw [←hmem]
  fin_cases i
  · change (determinantCharacter (point S.field.Carrier) _ = 1) ↔ _ ∈ pointLocal
    rw [pointLocal,mem_determinantKernel_iff]
    exact ⟨fun h => ⟨(cartan_borel S m hX x).1,h⟩,fun h => h.choose_spec⟩
  · change (determinantCharacter (plane S.field.Carrier) _ = 1) ↔ _ ∈ planeLocal
    rw [planeLocal,mem_determinantKernel_iff]
    exact ⟨fun h => ⟨(cartan_borel S m hX x).2,h⟩,fun h => h.choose_spec⟩

private def charactersEquiv {X : Subgroup G} (hX : IsCartan T L X) :
    X ≃* S.field.Carrierˣ × S.field.Carrierˣ := by
  have hc : Nat.card X = Nat.card (S.field.Carrierˣ × S.field.Carrierˣ) := by
    rw [(c S m).cartan_card hX,Nat.card_prod,Nat.card_units,S.field.card_eq,pow_two]
  exact MulEquiv.ofBijective (characters S m hX)
    ((characters_injective S m hX).bijective_of_nat_card_le hc.ge)

private theorem kernel_characters (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) (i : Fin 2) (x : X) :
    (x:G) ∈ Closure.coreQuotientCentralizer ((f S m).Li i) ↔
      (if i = 0 then (characters S m hX x).1 = (characters S m hX x).2
       else (characters S m hX x).2 = (characters S m hX x).1^2) := by
  let B := (f S m).Li i
  have hBL : B ≤ L := (localResidual_le _).trans inf_le_left
  have hnX : X ≤ normalizer (B : Set G) :=
    ((le_inf ((hX.1.trans inf_le_left).trans L.le_normalizer)
      (((f S m).cartan_normalizes (LocalGeometry.Sp4.flag_inner_unique m S) hX i.castSucc).trans
        (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  let xL : L := ⟨x,(hX.1 x.property).1⟩
  have hn : xL ∈ normalizer (B.subgroupOf L : Set L) := by
    rw [←subgroupOf_normalizer_eq hBL]
    exact hnX x.property
  have hq := core_kernel_map_iff (r S m) (by rw [r_ker]; exact pCore_isPGroup)
    (B.subgroupOf L) hn
  have hi := core_kernel_map_iff L.subtype (by
    rw [L.subtype.ker_eq_bot L.subtype_injective]; exact IsPGroup.of_bot)
    (B.subgroupOf L) hn
  rw [map_subgroupOf_eq_of_le hBL] at hi
  change r S m xL ∈ Closure.coreQuotientCentralizer
    ((((f S m).Li i).subgroupOf L).map (r S m)) ↔ _ at hq
  rw [residual_image] at hq
  have he := hi.trans hq.symm
  change (x:G) ∈ Closure.coreQuotientCentralizer B ↔ _ at he
  rw [he]
  have hx3 : x^3 = 1 := by
    let e := (c S m).cartanTorusEquiv hX
    have hc : Nat.card S.field.Carrierˣ = 3 := by
      rw [Nat.card_units,S.field.card_eq,hd]; decide
    have hp (a : S.field.Carrierˣ) : a^3 = 1 := by rw [←hc]; exact pow_card_eq_one'
    apply e.injective
    rw [map_pow,map_one]
    exact Prod.ext (hp _) (hp _)
  let b : X →* Theory.SpecificGroups.SymplecticFour.borel (F := S.field.Carrier) :=
    (((r S m).comp (inclusion (hX.1.trans inf_le_left))).codRestrict _ (cartan_borel S m hX))
  have hb3 : (b x)^3 = 1 := by rw [←map_pow,hx3,map_one]
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  fin_cases i
  · exact Sp4Model.cubic_point_kernel_iff_characters hF (b x) hb3
  · exact Sp4Model.cubic_plane_kernel_iff_characters hF (b x) hb3

/-- The two residual intersections and both full quotient centralizers
are the four literal cubic lines in the same original Cartan. -/
theorem marked_four_lines (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) :
    ∃ e : X ≃* S.field.Carrierˣ × S.field.Carrierˣ, ∀ x : X,
      ((x:G) ∈ (LocalGeometry.Sp4.flag m S).Li 0 ↔ (e x).1 = 1) ∧
      ((x:G) ∈ (LocalGeometry.Sp4.flag m S).Li 1 ↔ (e x).2 = 1) ∧
      ((x:G) ∈ Closure.coreQuotientCentralizer ((LocalGeometry.Sp4.flag m S).Li 0) ↔ (e x).1 = (e x).2) ∧
      ((x:G) ∈ Closure.coreQuotientCentralizer ((LocalGeometry.Sp4.flag m S).Li 1) ↔ (e x).2 = (e x).1^2) := by
  refine ⟨charactersEquiv S m hX,fun x => ?_⟩
  exact ⟨(characters_membership S m hX 0 x).symm,(characters_membership S m hX 1 x).symm,
    kernel_characters S m hd hX 0 x,kernel_characters S m hd hX 1 x⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.Sp4Cartan

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- Four-line identification for any supplied original invariant flag. -/
theorem sp4_cartan_four_lines (hd : S.field.degree = 2) (f : InvariantFlag (.sp4 m))
    {X : Subgroup G} (hX : IsCartan T L X) :
    ∃ e : X ≃* S.field.Carrierˣ × S.field.Carrierˣ, ∀ x : X,
      ((x:G) ∈ f.Li 0 ↔ (e x).1 = 1) ∧
      ((x:G) ∈ f.Li 1 ↔ (e x).2 = 1) ∧
      ((x:G) ∈ Closure.coreQuotientCentralizer (f.Li 0) ↔ (e x).1 = (e x).2) ∧
      ((x:G) ∈ Closure.coreQuotientCentralizer (f.Li 1) ↔ (e x).2 = (e x).1^2) := by
  have hr (i : Fin 2) : f.Li i = (LocalGeometry.Sp4.flag m S).Li i := by
    have he := LocalGeometry.Sp4.flag_inner_unique m S i.castSucc (f.space i.castSucc)
      (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))
    exact congrArg (fun U => localResidual L ((Coordinates.sp4 m).preimage U)) he
  rw [hr 0,hr 1]
  exact Sp4Cartan.marked_four_lines S m hd hX

private theorem cubic_pair_cases {A : Type*} [Group A] (hc : Nat.card A = 3) (a b : A) :
    a = 1 ∨ b = 1 ∨ a = b ∨ b = a^2 := by
  by_cases ha : a = 1
  · exact .inl ha
  right
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n,rfl⟩ := (mem_powers_of_prime_card hc ha (g' := b))
  have ho : orderOf a = 3 := (orderOf_eq_card_of_zpowers_eq_top
    (zpowers_eq_top_of_prime_card hc ha)).trans hc
  have hp : a^n = a^(n%3) := by rw [←ho,pow_mod_orderOf]
  change a^n = 1 ∨ a = a^n ∨ a^n = a^2
  rw [hp]
  have hn : n%3 < 3 := Nat.mod_lt n (by decide)
  interval_cases h : n%3 <;> simp

private theorem diagonal_of_three_lines {X A B : Type*} [Group X] [Group A] [Group B]
    (e : X ≃* A × A) (f : X ≃* B × B) (hc : Nat.card B = 3)
    (h₀ : ∀ x, (e x).1 = 1 ↔ (f x).1 = 1)
    (h₁ : ∀ x, (e x).2 = 1 ↔ (f x).2 = 1)
    (h₂ : ∀ x, (e x).2 = (e x).1^2 ↔ (f x).2 = (f x).1^2)
    (x : X) (hx : (e x).1 = (e x).2) : (f x).1 = (f x).2 := by
  have hfinish (ha : (e x).1 = 1) : (f x).1 = (f x).2 := by
    have he : e x = 1 := Prod.ext ha (hx.symm.trans ha)
    have hone := e.map_eq_one_iff.mp he
    simp [hone]
  rcases cubic_pair_cases hc (f x).1 (f x).2 with h | h | h | h
  · exact hfinish ((h₀ x).mpr h)
  · exact hfinish (hx.trans ((h₁ x).mpr h))
  · exact h
  · have hh : (e x).1 = (e x).1^2 := hx.trans ((h₂ x).mpr h)
    apply hfinish
    simpa only [pow_two,mul_assoc,inv_mul_cancel_left,inv_mul_cancel] using
      (congrArg (fun a => (e x).1⁻¹ * a) hh).symm

/-- Two natural symplectic flags with the same plane residual and the same
point-residual intersection in X have the same point quotient kernel in X.
The identification follows from all four actual action characters. -/
theorem sp4_point_kernel_eq_of_shared_lines (hd : S.field.degree = 2)
    (f : InvariantFlag (.sp4 m)) {X : Subgroup G} (hX : IsCartan T L X)
    {I U : Subgroup G} {D_I : ChosenModule T I U} (S_I : D_I.NonbinaryNaturalInput)
    (m_I : ActionEquiv D_I.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S_I.field.Carrier) 2)))
    (hdI : S_I.field.degree = 2) (f_I : InvariantFlag (.sp4 m_I)) (hXI : IsCartan T I X)
    (hfirst : X ⊓ f.Li 0 = X ⊓ f_I.Li 0) (hsecond : f.Li 1 = f_I.Li 1) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li 0) =
      X ⊓ Closure.coreQuotientCentralizer (f_I.Li 0) := by
  obtain ⟨e,he⟩ := sp4_cartan_four_lines S m hd f hX
  obtain ⟨g,hg⟩ := sp4_cartan_four_lines S_I m_I hdI f_I hXI
  have h₀ (x : X) : (e x).1 = 1 ↔ (g x).1 = 1 := by
    rw [←(he x).1,←(hg x).1]
    exact ⟨fun h => (hfirst.le ⟨x.property,h⟩).2,
      fun h => (hfirst.ge ⟨x.property,h⟩).2⟩
  have h₁ (x : X) : (e x).2 = 1 ↔ (g x).2 = 1 := by
    rw [←(he x).2.1,←(hg x).2.1,hsecond]
  have h₂ (x : X) : (e x).2 = (e x).1^2 ↔ (g x).2 = (g x).1^2 := by
    rw [←(he x).2.2.2,←(hg x).2.2.2,hsecond]
  have hc : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,S.field.card_eq,hd]; decide
  have hcI : Nat.card S_I.field.Carrierˣ = 3 := by rw [Nat.card_units,S_I.field.card_eq,hdI]; decide
  apply le_antisymm
  · rintro x ⟨hx,hk⟩
    exact ⟨hx,(hg ⟨x,hx⟩).2.2.1.mpr (diagonal_of_three_lines e g hcI h₀ h₁ h₂ _
      ((he ⟨x,hx⟩).2.2.1.mp hk))⟩
  · rintro x ⟨hx,hk⟩
    exact ⟨hx,(he ⟨x,hx⟩).2.2.1.mpr (diagonal_of_three_lines g e hc
      (fun x => (h₀ x).symm) (fun x => (h₁ x).symm) (fun x => (h₂ x).symm) _
      ((hg ⟨x,hx⟩).2.2.1.mp hk))⟩

/-- The original point quotient kernel has order three, computed from
its actual diagonal character, not selected by subgroup order. -/
theorem sp4_point_kernel_card (hd : S.field.degree = 2) (f : InvariantFlag (.sp4 m))
    {X : Subgroup G} (hX : IsCartan T L X) :
    Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3 := by
  obtain ⟨e,he⟩ := sp4_cartan_four_lines S m hd f hX
  let C := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  let j : C →* X := inclusion inf_le_left
  let p : C →* S.field.Carrierˣ :=
    (MonoidHom.fst S.field.Carrierˣ S.field.Carrierˣ).comp (e.toMonoidHom.comp j)
  have hi : Function.Injective p := by
    intro a b hab
    change (e (j a)).1 = (e (j b)).1 at hab
    have ha := (he (j a)).2.2.1.mp a.property.2
    have hb := (he (j b)).2.2.1.mp b.property.2
    have hh : j a = j b := e.injective (Prod.ext hab (ha.symm.trans (hab.trans hb)))
    exact Subtype.ext (congrArg (fun x : X => (x:G)) hh)
  have hs : Function.Surjective p := by
    intro a
    let x := e.symm (a,a)
    have hx : (x:G) ∈ C := ⟨x.property,(he x).2.2.1.mpr (by simp [x])⟩
    refine ⟨⟨x,hx⟩,?_⟩
    change (e x).1 = a
    simp [x]
  rw [Nat.card_congr (MulEquiv.ofBijective p ⟨hi,hs⟩).toEquiv,Nat.card_units,S.field.card_eq,hd]
  decide

/-- The model at a reselected vertex selects its symplectic coordinates,
then the shared literal residuals identify the same cubic kernel. -/
theorem sp4_point_kernel_eq_of_reselected_sp4 (hd : S.field.degree = 2)
    (f : InvariantFlag (.sp4 m)) {X : Subgroup G} (hX : IsCartan T L X)
    {I U : Subgroup G} {D_I : ChosenModule T I U} (S_I : D_I.NonbinaryNaturalInput)
    (hdI : S_I.field.degree = 2) {c_I : Coordinates D_I S_I.field}
    (f_I : InvariantFlag c_I) (hXI : IsCartan T I X)
    (hmI : Source.IsSp (I ⧸ pCore 2 I) 2 4)
    (hfirst : X ⊓ f.Li 0 = X ⊓ f_I.Li 0) (hsecond : f.Li 1 = f_I.Li 1) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li 0) =
      X ⊓ Closure.coreQuotientCentralizer (f_I.Li 0) := by
  have hcard : Nat.card (I ⧸ pCore 2 I) = 979200 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmI
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF]
    norm_num
  have hF : Nat.card S_I.field.Carrier = 4 := by simpa [hdI] using S_I.field.card_eq
  cases c_I with
  | sp4 m_I => exact sp4_point_kernel_eq_of_shared_lines S m hd f hX S_I m_I hdI f_I hXI hfirst hsecond
  | sl3 m_I =>
    rw [Nat.card_congr m_I.groupEquiv.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hcard
    norm_num at hcard
  | g2 m_I =>
    rw [Nat.card_congr m_I.groupEquiv.toEquiv,Atlas.G2.card_Model,hF] at hcard
    norm_num at hcard

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
