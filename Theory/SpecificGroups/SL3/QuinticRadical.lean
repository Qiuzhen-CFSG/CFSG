module
public import Theory.SpecificGroups.PSL3.CubicBorelRigidity
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# Odd-degree linear-three radical normalizers and quintic actors

An invariant two-radical supplies an invariant Sylow subgroup, using the
five-free order of SL₃ over an odd-degree binary field. The radical normalizer
contains its full Borel. Normalization of the actor subgroup and a two-group
inner intersection force all Borel displacements into the Sylow subgroup.
The actual linear-field-graph normal form then kills the field and graph
parts; the remaining inner quintic is excluded by the same five-free order.
Transport retains the specified component, radical and automorphism group.

Source application: Aschbacher--Smith 14.6.15, printed p.1035. The imported
ATLAS models retain attribution in LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. This module covers the odd-degree model branch.
-/

public section
open Subgroup Matrix Matrix.PSL3 Theory.GroupTheory
open scoped MatrixGroups Pointwise
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
namespace Matrix.SL3.QuinticRadical
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

omit [Field F] [Finite F] in
private theorem card_mod_three (hF : Nat.card F = 2^n) (ho : Odd n) : Nat.card F % 3 = 2 := by
  obtain ⟨k,rfl⟩ := ho
  rw [hF,pow_add,pow_mul]
  simp [Nat.mul_mod,Nat.pow_mod]

private theorem units_three_free (hF : Nat.card F = 2^n) (ho : Odd n) :
    ¬3 ∣ Nat.card Fˣ := by
  rw [Nat.card_units]
  have hh := card_mod_three hF ho
  intro hd
  have hmod := Nat.mod_eq_zero_of_dvd hd
  have hp : 0 < Nat.card F := Nat.card_pos
  omega

/-- At odd binary degree the actual special linear group has order prime to five. -/
theorem five_not_dvd (hF : Nat.card F = 2^n) (ho : Odd n) :
    ¬5 ∣ Nat.card SL(3,F) := by
  rw [DefiningSylow.card_specialLinear,hF]
  intro hd
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2^n)^2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ (2^n)^3 := Nat.one_le_pow _ _ hq
  have hz := (ZMod.natCast_eq_zero_iff _ 5).mpr hd
  push_cast [Nat.cast_sub h2,Nat.cast_sub h3] at hz
  rw [pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1)] at hz
  have hm2 : n%2=1 := Nat.odd_iff.mp ho
  have hm : n%4=1 ∨ n%4=3 := by omega
  rcases hm with hm | hm <;> rw [hm] at hz <;> revert hz <;> decide

private theorem units_dvd_borel (F : Type*) [Field F] [Finite F] :
    Nat.card Fˣ ∣ Nat.card (borelSL F) := by
  rw [Nat.card_units,DefiningSylow.card_borelSL]
  exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : (2:ℕ) ≠ 0)) _

private theorem inner_quintic_eq_one {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hN : ¬ 5 ∣ Nat.card (normalizer (H : Set G)))
    (α : MulAut G) (hα : α ^ 5 = 1) (hstable : H.map α.toMonoidHom = H)
    (hinner : α ∈ MulAut.innerSubgroup G) : α = 1 := by
  obtain ⟨g,hg⟩ := hinner
  have hgN : g ∈ normalizer (H : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,hg]
    exact hstable
  let x : normalizer (H : Set G) := ⟨g,hgN⟩
  let f : normalizer (H : Set G) →* MulAut G :=
    MulAut.conj.comp (normalizer (H : Set G)).subtype
  have hx : f x = α := hg
  have hd : orderOf α ∣ Nat.card (normalizer (H : Set G)) := by
    rw [←hx]
    exact (orderOf_map_dvd f x).trans (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hN)
    (orderOf_dvd_of_pow_eq_one hα) hd)

variable (F) [CharP F 2]
private theorem standard_quintic_eq_one {e : ℕ}
    (he : 1 < e) (hF : Nat.card F = 2 ^ e)
    (ho : Odd e)
    (hB : ¬ 5 ∣ Nat.card (borelSL F))
    (α : MulAut SL(3,F)) (hα : α ^ 5 = 1)
    (hstable : (unipotentSL F).map α.toMonoidHom = unipotentSL F)
    (hfix : ∀ b ∈ borelSL F, α b * b⁻¹ ∈ unipotentSL F) : α = 1 := by
  have hcop3 : Nat.Coprime 3 (Nat.card Fˣ) :=
    (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr (units_three_free hF ho)
  have hcop : Nat.Coprime 5 (Nat.card Fˣ) :=
    (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr
      (fun h => hB (h.trans (units_dvd_borel F)))
  obtain ⟨m,σ,ε,rfl⟩ := Matrix.PSL3.CubicBorelRigidity.specialCoverage F he hF α
  have hps := centerAction_unipotent F _ hstable
  rw [centerAction_specialActor] at hps
  have hm := NormalizerForm.linearConj_upperTriangular F m
    (linear_part_unipotent F m σ ε hps)
  have hfix' (u : Fˣ) :
      projectiveActor F m σ ε (torusMap F (u,1)) * (torusMap F (u,1))⁻¹ ∈
        unipotent F := by
    have hh := mem_map_of_mem (projection F)
      (hfix (torusSL F (u,1)) (torusSL_mem_borel F (u,1)))
    rw [map_mul, map_inv] at hh
    change centerAction F (specialActor F m σ ε) (torusMap F (u,1)) * _ ∈ _ at hh
    rwa [centerAction_specialActor] at hh
  cases ε
  · have hσ : σ = 1 := by
      apply RingEquiv.ext
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · let u : Fˣ := Units.mk0 x hx
        have hh := hfix' u
        simp only [projectiveActor, Bool.false_eq_true, ↓reduceIte, mul_one,
          MulAut.mul_apply, field_torusMap, map_one] at hh
        have hp := ResidualLinear.parameters_eq_of_displacement m hm _ _ hh
        exact congrArg Units.val (ResidualParameters.projective_axis_injective hp)
    have ha : specialActor F m σ false = linearConjSL F m := by
      have hf : Atlas.fieldEquivSL 3 (1 : F ≃+* F) = 1 := by
        ext g i j
        rfl
      simp [specialActor, hσ, hf]
    rw [ha] at hα hstable ⊢
    have hi : linearConjSL F m ∈ MulAut.innerSubgroup SL(3,F) := by
      obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime
        (hcop.symm.of_dvd_right (orderOf_dvd_of_pow_eq_one hα))
      rw [← hk]
      exact (MulAut.innerSubgroup SL(3,F)).pow_mem (linearConjSL_pow_inner F m) k
    apply inner_quintic_eq_one (unipotentSL F) _ _ hα hstable hi
    rwa [normalizer_unipotentSL]
  · have hall : ∀ u : Fˣ, u = 1 := by
      intro u
      have hh := hfix' u
      simp only [projectiveActor, ↓reduceIte, MulAut.mul_apply,
        oppositionGraph_torusMap, field_torusMap, inv_one, map_one, map_inv] at hh
      have hp := ResidualLinear.parameters_eq_of_displacement m hm _ _ hh
      have hu := ResidualParameters.cube_eq_one_of_graph_field_axis σ u hp
      exact hcop3.symm.pow_left_bijective.injective (by simpa using hu)
    have : Subsingleton Fˣ := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hc := Nat.card_unique (α := Fˣ)
    rw [Nat.card_units, hF] at hc
    have hp : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
    omega


omit [Finite F] [CharP F 2] in
private theorem invariant_sylow
    {X : Type*} [Group X] [Finite X]
    (a : MulAut X) (ha : orderOf a = 5) (hX : ¬ 5 ∣ Nat.card X) :
    ∃ S : Sylow 2 X, (S : Subgroup X).map a.toMonoidHom = S := by
  let A := zpowers a
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ha,pow_one])
  have hd : Nat.card (Sylow 2 X) ∣ Nat.card X :=
    (Sylow.card_dvd_index (Classical.choice (inferInstance : Nonempty (Sylow 2 X)))).trans
      (index_dvd_card _)
  obtain ⟨S,hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 X)
    (fun hh => hX (hh.trans hd))
  exact ⟨S,congrArg Sylow.toSubgroup (hS ⟨a,mem_zpowers a⟩)⟩

private theorem aut_normalizes_normalizer {X : Type*} [Group X]
    (Q : Subgroup X) (a : MulAut X) (hQ : Q.map a.toMonoidHom = Q) :
    (normalizer (Q : Set X)).map a.toMonoidHom = normalizer (Q : Set X) := by
  rw [map_equiv_normalizer_eq,hQ]


/-- A linear-three radical normalizer contains a full Sylow normalizer. -/
theorem exists_sylow_normalizer_le (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R : Subgroup SL(3,F)) (hR : R.IsPRadical 2) :
    ∃ S : Sylow 2 SL(3,F), normalizer (S : Set SL(3,F)) ≤ normalizer (R : Set SL(3,F)) := by
  rcases RadicalNormalizer.radical_normalizer_parabolic_or_sylow R hR hn hF with
    ⟨e,he⟩ | ⟨S,hS⟩
  · let a := Matrix.HigherLinear.SubspaceTransport.slConj e
    let S := (unipotentSLSylow F (by omega) hF).mapSurjective
      (f := a.symm.toMonoidHom) a.symm.surjective
    refine ⟨S,?_⟩
    have hs : (S : Subgroup SL(3,F)).map a.toMonoidHom = unipotentSL F := by
      change ((unipotentSL F).map a.symm.toMonoidHom).map a.toMonoidHom = _
      have hc : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id SL(3,F) := by
        ext x : 1
        exact a.apply_symm_apply x
      rw [Subgroup.map_map,hc,Subgroup.map_id]
    apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    change (normalizer ((S : Subgroup SL(3,F)) : Set SL(3,F))).map a.toMonoidHom ≤ _
    rw [map_equiv_normalizer_eq,hs,normalizer_unipotentSL]
    rcases he with he | he
    · rw [he]; exact inf_le_left
    · rw [he]; exact inf_le_right
  · exact ⟨S,hS ▸ le_rfl⟩

omit [Finite F] [CharP F 2] in
private theorem normalizer_le_of_common_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S Q : Sylow p G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hQP : (Q : Subgroup G) ≤ P)
    (hN : normalizer (S : Set G) ≤ P) : normalizer (Q : Set G) ≤ P := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P (S.subtype hSP) (Q.subtype hQP)
  have he : (g : G) • S = Q :=
    Sylow.subtype_injective ((S.smul_subtype hSP g).symm.trans hg)
  have hm : (S : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup he
  have hn : (normalizer (S : Set G)).map (MulAut.conj (g : G)).toMonoidHom =
      normalizer (Q : Set G) := by
    change (normalizer ((S : Subgroup G) : Set G)).map _ = _
    rw [map_equiv_normalizer_eq,hm]
    rfl
  rw [←hn]
  rintro x ⟨y,hy,rfl⟩
  exact P.mul_mem (P.mul_mem g.property (hN hy)) (P.inv_mem g.property)

theorem invariant_sylow_in_radical_normalizer
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (Q : Subgroup (SL(3,F))) (hQ : Q.IsPRadical 2)
    (a : MulAut (SL(3,F))) (ha : orderOf a = 5)
    (hfix : Q.map a.toMonoidHom = Q) (hfive : ¬5 ∣ Nat.card (SL(3,F))) :
    ∃ S : Sylow 2 (SL(3,F)), (S : Subgroup (SL(3,F))).map a.toMonoidHom = S ∧
      normalizer (S : Set (SL(3,F))) ≤ normalizer (Q : Set (SL(3,F))) := by
  let N := normalizer (Q : Set (SL(3,F)))
  have hN := aut_normalizes_normalizer Q a hfix
  let b : MulAut N := (a.subgroupMap N).trans (MulEquiv.subgroupCongr hN)
  have hb5 : b^5=1 := by
    have hh : a^5=1 := ha ▸ pow_orderOf_eq_one a
    ext x : 1
    apply Subtype.ext
    exact congrArg (fun t : MulAut (SL(3,F)) => t x) hh
  have hbX : ¬5 ∣ Nat.card N := fun hd => hfive (hd.trans N.card_subgroup_dvd_card)
  have hs : ∃ P : Sylow 2 N, (P : Subgroup N).map b.toMonoidHom = P := by
    by_cases hb : b = 1
    · refine ⟨Classical.choice Sylow.nonempty,?_⟩
      rw [hb]
      exact Subgroup.map_id _
    · apply invariant_sylow b (orderOf_eq_prime (by simpa using hb5) hb) hbX
  obtain ⟨P,hP⟩ := hs
  obtain ⟨S,hPS⟩ := P.exists_comap_subtype_eq
  obtain ⟨S0,hS0⟩ := exists_sylow_normalizer_le F hn hF Q hQ
  have hS0N : (S0 : Subgroup (SL(3,F))) ≤ N := S0.toSubgroup.le_normalizer.trans hS0
  have hmap : (P : Subgroup N).map N.subtype = (S : Subgroup (SL(3,F))) := by
    have hcard : Nat.card P = Nat.card S := by
      rw [Nat.card_congr (P.equiv (S0.subtype hS0N)).toEquiv]
      change Nat.card ((S0 : Subgroup (SL(3,F))).subgroupOf N) = Nat.card S
      rw [Nat.card_congr (subgroupOfEquivOfLe hS0N).toEquiv,
        Nat.card_congr (S0.equiv S).toEquiv]
    apply eq_of_le_of_card_ge
    · rw [←hPS]; exact map_comap_le _ _
    · rw [card_map_of_injective N.subtype_injective,hcard]
  have hSN : (S : Subgroup (SL(3,F))) ≤ N := hmap ▸ map_subtype_le _
  refine ⟨S,?_,normalizer_le_of_common_sylow S0 S N hS0N hSN hS0⟩
  rw [←hmap,Subgroup.map_map]
  have he : a.toMonoidHom.comp N.subtype = N.subtype.comp b.toMonoidHom := rfl
  rw [he,←Subgroup.map_map,hP]
theorem no_outer_borel_actor (hn : 1 < n) (hF : Nat.card F = 2^n) (ho : Odd n)
    (A : Subgroup (MulAut (SL(3,F))))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup (SL(3,F)) : Subgroup _))
    (hN : (borelSL F).map (MulAut.conj : SL(3,F) →* MulAut (SL(3,F))) ≤ normalizer (A : Set _))
    (a : MulAut (SL(3,F))) (ha : a ∈ A)
    (hfix : (unipotentSL F).map a.toMonoidHom = unipotentSL F)
    (ha5 : orderOf a = 5) : False := by
  let D := (A ⊓ MulAut.innerSubgroup (SL(3,F))).comap MulAut.conj
  have hD : IsPGroup 2 D := hi.comap_of_injective _
    (MulAut.conj_injective_of_center_eq_bot ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [card_mod_three hF ho]; decide)))
  have hbfix (b : zpowers a) : (unipotentSL F).map b.val.toMonoidHom = unipotentSL F :=
    (zpowers_le.mpr hfix : zpowers a ≤ MulAction.stabilizer (MulAut (SL(3,F))) (unipotentSL F)) b.property
  have hbA (b : zpowers a) : b.val ∈ A := (zpowers_le.mpr ha) b.property
  have dd (b : zpowers a) (x : SL(3,F)) (hx : x ∈ borelSL F) :
      x⁻¹ * b.val x ∈ unipotentSL F := by
    have hn := hN (mem_map_of_mem MulAut.conj hx)
    have ha' : (MulAut.conj x)⁻¹ * b.val * MulAut.conj x ∈ A :=
      (mem_normalizer_iff.mp (inv_mem hn) b.val).mp (hbA b)
    have he : MulAut.conj (x⁻¹ * b.val x) =
        ((MulAut.conj x)⁻¹ * b.val * MulAut.conj x) * b.val⁻¹ := by
      ext y : 1
      change (x⁻¹ * b.val x) * y * (x⁻¹ * b.val x)⁻¹ =
        x⁻¹ * b.val (x * b.val.symm y * x⁻¹) * x
      simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    have hm : x⁻¹ * b.val x ∈ D :=
      ⟨he ▸ A.mul_mem ha' (A.inv_mem (hbA b)),⟨_,rfl⟩⟩
    have hb : (borelSL F).map b.val.toMonoidHom = borelSL F := by
      rw [←normalizer_unipotentSL]
      exact aut_normalizes_normalizer _ _ (hbfix b)
    have hx' : b.val x ∈ borelSL F := hb ▸ mem_map_of_mem b.val.toMonoidHom hx
    have hh : x⁻¹ * b.val x ∈ D ⊓ normalizer (unipotentSLSylow F (by omega) hF : Set (SL(3,F))) :=
      ⟨hm,by
        change x⁻¹ * b.val x ∈ normalizer (unipotentSL F : Set (SL(3,F)))
        rw [normalizer_unipotentSL]
        exact (borelSL F).mul_mem ((borelSL F).inv_mem hx) hx'⟩
    rw [hD.inf_normalizer_sylow (unipotentSLSylow F (by omega) hF)] at hh
    exact hh.2
  have hB : ¬5 ∣ Nat.card (borelSL F) :=
    fun h => five_not_dvd hF ho (h.trans (card_subgroup_dvd_card _))
  have he := standard_quintic_eq_one F hn hF ho hB a
    (ha5 ▸ pow_orderOf_eq_one a) hfix (fun x hx => by
      have hh := dd ⟨a,mem_zpowers a⟩ x hx
      have hxN : x ∈ normalizer (unipotentSL F : Set SL(3,F)) := by
        rw [normalizer_unipotentSL]; exact hx
      have hc := (mem_normalizer_iff.mp hxN (x⁻¹*a x)).mp hh
      simpa only [mul_inv_cancel_left,mul_assoc] using hc)
  rw [he,orderOf_one] at ha5
  omega

theorem no_outer_marked_sylow_actor
    {C : Type*} [Group C] [Finite C] (e : C ≃* SL(3,F))
    (hn : 1 < n) (hF : Nat.card F = 2^n) (ho : Odd n) (S : Sylow 2 C)
    (hS : (S : Subgroup C).map e.toMonoidHom = unipotentSL F)
    (A : Subgroup (MulAut C))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup C : Subgroup _))
    (hN : (normalizer (S : Set C)).map (MulAut.conj : C →* MulAut C) ≤
      normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A)
    (hfix : (S : Subgroup C).map a.toMonoidHom = S)
    (ha5 : orderOf a = 5) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  have hB : (normalizer (S : Set C)).map e.toMonoidHom = borelSL F := by
    change (normalizer ((S : Subgroup C) : Set C)).map e.toMonoidHom = borelSL F
    rw [map_equiv_normalizer_eq,hS,normalizer_unipotentSL]
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup (SL(3,F)) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup C).map f = D ⊓ MulAut.innerSubgroup (SL(3,F)) := by
      rw [map_inf _ _ f (MulAut.congr e).injective,MulAut.map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hND : (borelSL F).map (MulAut.conj : SL(3,F) →* MulAut (SL(3,F))) ≤
      normalizer (D : Set (MulAut (SL(3,F)))) := by
    have hc : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : SL(3,F) →* MulAut (SL(3,F))).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rwa [Subgroup.map_map,hc,←Subgroup.map_map,hB] at hh
  have hfixD : (unipotentSL F).map (MulAut.congr e a).toMonoidHom = unipotentSL F := by
    rw [←hS,Subgroup.map_map]
    have hc : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x : 1
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [hc,←Subgroup.map_map,hfix]
  exact no_outer_borel_actor F hn hF ho D hiD hND _ (mem_map_of_mem f ha) hfixD
    ((MulAut.congr e).orderOf_eq a |>.trans ha5)

theorem no_radical_quintic_actor (hn : 1 < n) (hF : Nat.card F = 2^n) (ho : Odd n)
    (Q : Subgroup (SL(3,F))) (hQ : Q.IsPRadical 2)
    (A : Subgroup (MulAut (SL(3,F))))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup (SL(3,F)) : Subgroup _))
    (hN : (normalizer (Q : Set (SL(3,F)))).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut (SL(3,F))) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : Q.map a.toMonoidHom = Q) : False := by
  obtain ⟨S,hS,hSN⟩ := invariant_sylow_in_radical_normalizer F hn hF Q hQ a ha5 hfix (five_not_dvd hF ho)
  obtain ⟨g,hg,_⟩ := sylowSL_normalizer_conjugate F (by omega) hF S
  let e := (MulAut.conj g).symm
  have he : (S : Subgroup (SL(3,F))).map e.toMonoidHom = unipotentSL F := by
    rw [←hg,Subgroup.map_map]
    have hc : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id (SL(3,F)) := by
      ext x : 1
      exact e.apply_symm_apply x
    rw [hc,Subgroup.map_id]
  exact no_outer_marked_sylow_actor F e hn hF ho S he A hi ((map_mono hSN).trans hN) a ha hS
    ha5

theorem no_radical_quintic_actor_of_equiv
    {C : Type*} [Group C] [Finite C] (e : C ≃* SL(3,F))
    (hn : 1 < n) (hF : Nat.card F = 2^n) (ho : Odd n)
    (Q : Subgroup C) (hQ : Q.IsPRadical 2) (A : Subgroup (MulAut C))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup C : Subgroup _))
    (hN : (normalizer (Q : Set C)).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : Q.map a.toMonoidHom = Q) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup (SL(3,F)) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup C).map f = D ⊓ MulAut.innerSubgroup (SL(3,F)) := by
      rw [map_inf _ _ f (MulAut.congr e).injective,MulAut.map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hND : (normalizer (Q.map e.toMonoidHom : Set (SL(3,F)))).map MulAut.conj ≤
      normalizer (D : Set _) := by
    have hc : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : SL(3,F) →* MulAut (SL(3,F))).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rwa [Subgroup.map_map,hc,←Subgroup.map_map,map_equiv_normalizer_eq] at hh
  have hfixD : (Q.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = Q.map e.toMonoidHom := by
    rw [Subgroup.map_map]
    have hc : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x : 1
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [hc,←Subgroup.map_map,hfix]
  exact no_radical_quintic_actor F hn hF ho _ (hQ.map_equiv e) D hiD hND _
    (mem_map_of_mem f ha) ((MulAut.congr e).orderOf_eq a |>.trans ha5) hfixD


omit [CharP F 2] in
/-- The binary model has no automorphism of order five. -/
theorem no_binary_actor (hF : Nat.card F = 2)
    {C : Type*} [Group C] [Finite C] (e : C ≃* SL(3,F))
    (a : MulAut C) (ha : orderOf a = 5) : False := by
  let : Fintype F := Fintype.ofFinite F
  let t : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 2)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let b := e.trans ((Atlas.fieldEquivSL 3 t).trans
    (Matrix.SL3.equivProjectiveOfCenterEqBot (ZMod 2) Matrix.PSL3Two.center_eq_bot))
  have hd := ha ▸ orderOf_dvd_natCard a
  rw [Nat.card_congr (MulAut.congr b).toEquiv, Matrix.PSL3Two.Automorphisms.card_aut] at hd
  norm_num at hd

end Matrix.SL3.QuinticRadical
