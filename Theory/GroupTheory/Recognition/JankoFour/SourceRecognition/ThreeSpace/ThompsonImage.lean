module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.NaturalTensor
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearOrbits
public import Theory.Representation.SL2FourNaturalOrbits.FixedBound

/-!
# The original alternating Sylow image of the Thompson subgroup

Let A be the elementary subgroup of order 2^11 inside S, containing Z and
normalized by the original K. The shear and swap formulas on R/Z isolate
all three coordinates of every K-invariant subgroup. Hence the image of
A intersect R has order c^3, where c is the order of its intersection with
the ORIGINAL pair section W. Since |Z|=8 and an elementary subgroup of
S5 has order at most four, |A|=2^11 forces c=4, |A intersect R|=2^9 and
|AR/R|=4.

This image fixes that same plane in W pointwise. In natural F4 coordinates,
a nonidentity element of A5 fixing a binary plane forces it to be an F4
line. An outer involution cannot fix an F4 line pointwise. The order-four
image therefore lies in the ORIGINAL marked A5 and is Sylow there. The
export retains the literal map S -> S/R -> S5, as required by the earlier
geometry's E_quotient field; the original Mathieu application supplies A=J(U).

This proves the alternating Sylow assertion in the proof of AS91 (4.7).
The split point group, the other overlap clauses, general/native local
geometry and unconditional recognition remain separate obligations.
Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.6)--(4.7), printed p.598, DOI 10.1007/BF01232280.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Representation.SL2FourNatural Representation.SL2FourNatural.PlaneGeometry

private theorem fieldLine_of_nonidentity_fixer (U : Plane) (a : SL) (ha : a ≠ 1)
    (hfix : ∀ v ∈ U.val, action a v = v) : IsFieldLine U.val := by
  have hn : action a ∈ SemilinearNormalizer.normalizer := action.range.le_normalizer ⟨a,rfl⟩
  have hne : action a ≠ 1 := fun he => ha (action_faithful (he.trans action.map_one.symm))
  have hb := normalizer_nonidentity_fixed_card_le_four (action a) hn hne
  have hl : U.val ≤ (action a).toLinearMap.fixedSubmodule := hfix
  have hc := Nat.card_le_card_of_injective (Submodule.inclusion hl) (Submodule.inclusion_injective hl)
  have he : U.val = (action a).toLinearMap.fixedSubmodule := submodule_eq_of_card _ _ hl (by omega)
  let W : Submodule F V := {
    carrier := U.val
    zero_mem' := U.val.zero_mem
    add_mem' := U.val.add_mem
    smul_mem' := by
      intro c v hv
      rw [he] at hv ⊢
      change action a (c • v) = c • v
      have hv' : action a v = v := hv
      rw [action_smul,hv'] }
  have hw : Nat.card W = 4 := U.property
  have hr : Module.finrank F W = 1 := by
    have hh := Module.natCard_eq_pow_finrank (K := F) (V := W)
    rw [hw,Nat.card_eq_fintype_card,card_field] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (4 : ℕ))
      (show (4 : ℕ)^1 = 4^Module.finrank F W from hh)).symm
  exact ⟨W,hr,rfl⟩

/-- A four-group fixing a binary plane in a marked natural S5 lies in its original A5. -/
theorem elementary_four_le_alternating_of_fixed_plane
    (ρ : Equiv.Perm (Fin 5) →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (q : alternatingGroup (Fin 5) ≃* SL)
    (hq : ∀ a : alternatingGroup (Fin 5), ρ a.val = action (q a))
    (A : Subgroup (Equiv.Perm (Fin 5))) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (U : Plane)
    (hfix : ∀ a ∈ A, ∀ v ∈ U.val, ρ a v = v) : A ≤ alternatingGroup (Fin 5) := by
  have hr : (alternatingGroup (Fin 5)).map ρ = action.range := by
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨q ⟨a,ha⟩,(hq ⟨a,ha⟩).symm⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨b,rfl⟩ := q.surjective a
      exact ⟨b.val,b.property,hq b⟩
  have hn (a : Equiv.Perm (Fin 5)) : ρ a ∈ SemilinearNormalizer.normalizer := by
    rw [SemilinearNormalizer.normalizer,←hr]
    exact (alternatingGroup (Fin 5)).le_normalizer_map ρ
      (mem_map_of_mem ρ (by rw [normalizer_eq_top]; trivial))
  have hmem (a : Equiv.Perm (Fin 5)) : ρ a ∈ action.range ↔ a ∈ alternatingGroup (Fin 5) := by
    rw [←hr]
    constructor
    · rintro ⟨b,hb,he⟩
      exact hρ he ▸ hb
    · exact mem_map_of_mem ρ
  let B := (alternatingGroup (Fin 5)).subgroupOf A
  have hi : B.index ≤ 2 := by
    have hd := (alternatingGroup (Fin 5)).relIndex_dvd_index_of_normal (K := A)
    rw [alternatingGroup.index_eq_two] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hc := B.card_mul_index
  rw [hA] at hc
  have hb : 1 < Nat.card B := by
    have hp := Nat.card_pos (α := B)
    nlinarith
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp hb
  obtain ⟨b,hb⟩ := exists_ne (1 : B)
  let b' : alternatingGroup (Fin 5) := ⟨b.val.val,b.property⟩
  have hb' : q b' ≠ 1 := by
    intro he
    apply hb
    have hb0 := q.injective (he.trans q.map_one.symm)
    exact Subtype.ext (Subtype.ext (congrArg (fun x : alternatingGroup (Fin 5) => x.val) hb0))
  have hline : IsFieldLine U.val := fieldLine_of_nonidentity_fixer U (q b') hb' (by
    intro v hv
    rw [←hq b']
    exact hfix b.val.val b.val.property v hv)
  intro a ha
  by_contra he
  have hp : a^2=1 := by
    exact congrArg (fun x : A => x.val) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a,ha⟩)
  have ht : IsFieldType SemilinearNormalizer.normalizer U :=
    ⟨ρ a,hn a,by rw [←map_pow,hp,map_one],fun hh => he ((hmem a).mp hh),hfix a ha⟩
  exact (fieldType_normalizer_iff U).mp ht hline


private theorem triple_invariant_card {W : Type*} [CommGroup W] [Finite W]
    (H : Subgroup (W × (W × W)))
    (ha : ∀ u v w, (u,v,w) ∈ H → (u,v,v*w) ∈ H)
    (hp : ∀ u v w, (u,v,w) ∈ H → (u,w,v) ∈ H)
    (hq : ∀ u v w, (u,v,w) ∈ H → (v,u,w) ∈ H) :
    Nat.card H = Nat.card (H.comap (MonoidHom.inl W (W × W))) ^ 3 := by
  let C := H.comap (MonoidHom.inl W (W × W))
  have hsecond (u v w : W) (hv : (u,v,w) ∈ H) : (v,1,1) ∈ H := by
    have hh := H.mul_mem (ha u v w hv) (H.inv_mem hv)
    have he : (u,v,v*w) * (u,v,w)⁻¹ = (1,1,v) := by
      ext <;> simp
    rw [he] at hh
    exact hq 1 v 1 (hp 1 1 v hh)
  have he : H = C.prod (C.prod C) := by
    ext ⟨u,v,w⟩
    constructor
    · intro hx
      exact ⟨hsecond v u w (hq u v w hx),hsecond u v w hx,
        hsecond u w v (hp u v w hx)⟩
    · rintro ⟨hu,hv,hw⟩
      change (u,1,1) ∈ H at hu
      change (v,1,1) ∈ H at hv
      change (w,1,1) ∈ H at hw
      have hv' := hq v 1 1 hv
      have hw' := hp 1 w 1 (hq w 1 1 hw)
      simpa only [Prod.mk_mul_mk,one_mul,mul_one] using H.mul_mem hu (H.mul_mem hv' hw')
  change Nat.card H = Nat.card C ^ 3
  conv_lhs => rw [he]
  rw [Nat.card_congr (prodEquiv C (C.prod C)).toEquiv,Nat.card_prod,
    Nat.card_congr (prodEquiv C C).toEquiv,Nat.card_prod]
  ring

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic R_normal_in_normalizer

/-- The literal image of A intersect R in R/Z(R). -/
def radicalIntersectionImage (A : Subgroup G) : Subgroup (d.R ⧸ center d.R) :=
  (A.subgroupOf d.R).map (QuotientGroup.mk' (center d.R))

/-- Its intersection with the original pair section W. -/
def radicalIntersectionMultiplicity (A : Subgroup G) : Subgroup d.multiplicitySpace :=
  (d.radicalIntersectionImage A).subgroupOf d.multiplicitySpace

theorem radicalIntersectionImage_invariant (h : IsTypeJ4 z) (A : Subgroup G)
    (hA : d.K ≤ normalizer (A : Set G)) (a : MulAut d.space)
    (v : d.R ⧸ center d.R) (hv : v ∈ d.radicalIntersectionImage A) :
    d.linearRadicalAction h a v ∈ d.radicalIntersectionImage A := by
  obtain ⟨k,rfl⟩ := d.KAction_surjective h a
  obtain ⟨r,hr,rfl⟩ := hv
  rw [d.linearRadicalAction_KAction,d.radicalAction_mk]
  apply mem_map_of_mem
  exact (mem_normalizer_iff.mp (hA k.property) r.val).mp hr

theorem radicalIntersectionImage_card_cube (h : IsTypeJ4 z) (A : Subgroup G)
    (hA : d.K ≤ normalizer (A : Set G)) :
    Nat.card (d.radicalIntersectionImage A) =
      Nat.card (d.radicalIntersectionMultiplicity A) ^ 3 := by
  let := d.multiplicitySpace_elementary h
  obtain ⟨f,hf,_,ha,hp,hq⟩ := d.exists_multiplicity_coordinates_root_actions h
  let H := (d.radicalIntersectionImage A).comap f.toMonoidHom
  have hstable (a : MulAut d.space) (v : d.R ⧸ center d.R)
      (hv : v ∈ d.radicalIntersectionImage A) := d.radicalIntersectionImage_invariant h A hA a v hv
  have hcard := triple_invariant_card H
    (fun u v w hv => by change f (u,v,v*w) ∈ d.radicalIntersectionImage A; rw [←ha]; exact hstable _ _ hv)
    (fun u v w hv => by change f (u,w,v) ∈ d.radicalIntersectionImage A; rw [←hp]; exact hstable _ _ hv)
    (fun u v w hv => by change f (v,u,w) ∈ d.radicalIntersectionImage A; rw [←hq]; exact hstable _ _ hv)
  have he : H.comap (MonoidHom.inl d.multiplicitySpace (d.multiplicitySpace × d.multiplicitySpace)) =
      d.radicalIntersectionMultiplicity A := by
    ext w
    change f (w,1,1) ∈ d.radicalIntersectionImage A ↔ _
    rw [hf]
    rfl
  rw [he] at hcard
  have hc := card_map_of_injective (K := H) (f := f.toMonoidHom) f.injective
  rw [map_comap_eq_self_of_surjective f.surjective] at hc
  exact hc.trans hcard

/-- The original symmetric-five quotient projection on S. -/
noncomputable def symmetricProjection (h : IsTypeJ4 z) : d.S →* Equiv.Perm (Fin 5) :=
  (d.SQuotientEquiv h).toMonoidHom.comp (QuotientGroup.mk' (d.R.subgroupOf d.S))

theorem symmetricProjection_ker (h : IsTypeJ4 z) :
    (d.symmetricProjection h).ker = d.R.subgroupOf d.S := by
  rw [symmetricProjection,MonoidHom.ker_comp_of_injective _ _ (d.SQuotientEquiv h).injective,
    QuotientGroup.ker_mk']

/-- The image of the same A in the original S/R marking. -/
noncomputable def symmetricImage (h : IsTypeJ4 z) (A : Subgroup G) : Subgroup (Equiv.Perm (Fin 5)) :=
  (A.subgroupOf d.S).map (d.symmetricProjection h)

theorem symmetricImage_card_le_four (h : IsTypeJ4 z) (A : Subgroup G)
    [IsElementaryAbelian 2 A] : Nat.card (d.symmetricImage h A) ≤ 4 := by
  let f : A.subgroupOf d.S →* A := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let : IsElementaryAbelian 2 (A.subgroupOf d.S) := IsElementaryAbelian.of_injective f
    (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun a : A => a.val) he)))
  let : IsElementaryAbelian 2 (d.symmetricImage h A) := IsElementaryAbelian.map (d.symmetricProjection h)
  exact (primeRank_le_iff_elementary_card_le _).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    (d.symmetricImage h A) inferInstance

theorem radicalIntersection_card (h : IsTypeJ4 z) (A : Subgroup G)
    (hZA : d.space ≤ A) :
    Nat.card (A ⊓ d.R : Subgroup G) = 8 * Nat.card (d.radicalIntersectionImage A) := by
  let f := QuotientGroup.mk' (center d.R)
  have hker : f.ker ≤ A.subgroupOf d.R := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hZA ((d.R_center_eq_space h) ▸ mem_map_of_mem d.R.subtype hx)
  have hc := (f.ker.subgroupOf (A.subgroupOf d.R)).card_mul_index
  change Nat.card (f.ker.subgroupOf (A.subgroupOf d.R)) * f.ker.relIndex (A.subgroupOf d.R) = _ at hc
  rw [Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv,relIndex_ker,
    QuotientGroup.ker_mk'] at hc
  have hz : Nat.card (center d.R) = 8 := by
    rw [←card_map_of_injective d.R.subtype_injective,d.R_center_eq_space h]
    exact d.card
  rw [hz,←card_map_of_injective d.R.subtype_injective,subgroupOf_map_subtype] at hc
  exact hc.symm

theorem symmetricImage_card_mul_intersection (h : IsTypeJ4 z) (A : Subgroup G)
    (hAS : A ≤ d.S) :
    Nat.card (A ⊓ d.R : Subgroup G) * Nat.card (d.symmetricImage h A) = Nat.card A := by
  have hc := ((d.symmetricProjection h).ker.subgroupOf (A.subgroupOf d.S)).card_mul_index
  change Nat.card ((d.symmetricProjection h).ker.subgroupOf (A.subgroupOf d.S)) *
    (d.symmetricProjection h).ker.relIndex (A.subgroupOf d.S) = _ at hc
  rw [relIndex_ker,d.symmetricProjection_ker h] at hc
  have hk : Nat.card ((d.R.subgroupOf d.S).subgroupOf (A.subgroupOf d.S)) =
      Nat.card (A ⊓ d.R : Subgroup G) := by
    rw [←card_map_of_injective (A.subgroupOf d.S).subtype_injective,subgroupOf_map_subtype,
      ←card_map_of_injective d.S.subtype_injective,
      map_inf _ _ _ d.S.subtype_injective,
      map_subgroupOf_eq_of_le (show d.R ≤ d.S from inf_le_right),map_subgroupOf_eq_of_le hAS,
      inf_comm]
  rw [hk,Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv] at hc
  exact hc

private theorem cube_arithmetic (c a : ℕ) (h : 8 * c^3 * a = 2048) (ha : a ≤ 4) :
    c = 4 ∧ a = 4 := by
  have ha0 : 1 ≤ a := by
    by_contra! hn
    have hz : a = 0 := by omega
    simp [hz] at h
  have hc0 : 4 ≤ c := by
    by_contra! hc
    have hb : c^3 ≤ 3^3 := Nat.pow_le_pow_left (by omega : c ≤ 3) 3
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hb) ha
    omega
  have hc1 : c ≤ 6 := by
    by_contra! hc
    have hb : 7^3 ≤ c^3 := Nat.pow_le_pow_left hc 3
    have hh := Nat.mul_le_mul_left (8*c^3) ha0
    nlinarith
  interval_cases c <;> norm_num at h ⊢ <;> omega

/-- The actual elementary rank-eleven subgroup has image four in the SAME symmetric quotient. -/
theorem elementary_eleven_symmetric_image (h : IsTypeJ4 z) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 2048)
    (hZA : d.space ≤ A) (hAS : A ≤ d.S) (hKA : d.K ≤ normalizer (A : Set G)) :
    Nat.card (d.radicalIntersectionMultiplicity A) = 4 ∧
    Nat.card (d.radicalIntersectionImage A) = 64 ∧
    Nat.card (A ⊓ d.R : Subgroup G) = 512 ∧
    Nat.card (d.symmetricImage h A) = 4 := by
  have hcube := d.radicalIntersectionImage_card_cube h A hKA
  have hcard := d.radicalIntersection_card h A hZA
  have hprod := d.symmetricImage_card_mul_intersection h A hAS
  rw [hcard,hcube,hc] at hprod
  obtain ⟨hm,hi⟩ := cube_arithmetic _ _ hprod (d.symmetricImage_card_le_four h A)
  rw [hm] at hcube
  rw [hcube] at hcard
  exact ⟨hm,hcube,hcard,hi⟩

theorem symmetricImage_elementary (h : IsTypeJ4 z) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAS : A ≤ d.S) : IsElementaryAbelian 2 (d.symmetricImage h A) := by
  let := IsElementaryAbelian.subgroupOf (p := 2) hAS
  exact IsElementaryAbelian.map (d.symmetricProjection h)

/-- The same four-group fixes the actual pair section of its radical intersection pointwise. -/
theorem symmetricImage_fixes_multiplicity (h : IsTypeJ4 z) (A : Subgroup G)
    [IsMulCommutative A] (b : Equiv.Perm (Fin 5)) (hb : b ∈ d.symmetricImage h A)
    (w : d.multiplicitySpace) (hw : w ∈ d.radicalIntersectionMultiplicity A) :
    d.markedMultiplicityAction h b w = w := by
  obtain ⟨s,hs,rfl⟩ := hb
  apply Subtype.ext
  rw [symmetricProjection,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    d.markedMultiplicityAction_mk]
  obtain ⟨r,hr,he⟩ := hw
  change d.radicalAction (⟨s.val,(centralizer_le_normalizer _) s.property⟩ :
    normalizer (d.space : Set G)) w.val = w.val
  change QuotientGroup.mk' (center d.R) r = w.val at he
  rw [←he,d.radicalAction_mk]
  apply congrArg (QuotientGroup.mk' (center d.R))
  apply Subtype.ext
  change s.val*r.val*s.val⁻¹ = r.val
  have hc : s.val*r.val = r.val*s.val :=
    congrArg (fun x : A => x.val) (mul_comm (⟨s.val,hs⟩ : A) ⟨r.val,hr⟩)
  rw [hc,mul_inv_cancel_right]

theorem naturalMarkedAction_injective (h : IsTypeJ4 z) :
    Function.Injective (d.naturalMarkedAction h) := by
  let := d.multiplicitySpace_elementary h
  intro a b he
  apply d.markedMultiplicityAction_injective h
  apply MulEquiv.ext
  intro w
  apply Additive.ofMul.injective
  apply (d.multiplicityNaturalEquiv h).injective
  change d.multiplicityNaturalEquiv h (binaryLinearAut (d.markedMultiplicityAction h a) (Additive.ofMul w)) =
    d.multiplicityNaturalEquiv h (binaryLinearAut (d.markedMultiplicityAction h b) (Additive.ofMul w))
  rw [d.multiplicityNaturalEquiv_marked,d.multiplicityNaturalEquiv_marked,he]

/-- The image of the actual rank-eleven subgroup lies in the original marked A5. -/
theorem elementary_eleven_image_le_alternating (h : IsTypeJ4 z) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 2048)
    (hZA : d.space ≤ A) (hAS : A ≤ d.S) (hKA : d.K ≤ normalizer (A : Set G)) :
    d.symmetricImage h A ≤ alternatingGroup (Fin 5) := by
  let := d.multiplicitySpace_elementary h
  let := d.symmetricImage_elementary h A hAS
  obtain ⟨hC,_,_,hI⟩ := d.elementary_eleven_symmetric_image h A hc hZA hAS hKA
  let C := AddSubgroup.toZModSubmodule 2 (d.radicalIntersectionMultiplicity A).toAddSubgroup
  let F := d.multiplicityNaturalEquiv h
  let U := C.map F.toLinearMap
  have hU : Nat.card U = 4 :=
    (Nat.card_congr (Submodule.equivMapOfInjective F.toLinearMap F.injective C).toEquiv).symm.trans hC
  apply elementary_four_le_alternating_of_fixed_plane (d.naturalMarkedAction h)
    (d.naturalMarkedAction_injective h) (d.markedNaturalActorEquiv h)
    (d.naturalMarkedAction_alternating h) (d.symmetricImage h A) hI ⟨U,hU⟩
  intro b hb v hv
  obtain ⟨w,hw,rfl⟩ := hv
  change d.naturalMarkedAction h b (F w) = F w
  have heq := d.multiplicityNaturalEquiv_marked h b w
  change F (binaryLinearAut (d.markedMultiplicityAction h b) w) =
    d.naturalMarkedAction h b (F w) at heq
  rw [←heq]
  exact congrArg F (congrArg Additive.ofMul (d.symmetricImage_fixes_multiplicity h A b hb w.toMul hw))

/-- AS91 (4.7)'s actual alternating Sylow image, without changing the S/R marking. -/
theorem elementary_eleven_alternating_sylow (h : IsTypeJ4 z) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 2048)
    (hZA : d.space ≤ A) (hAS : A ≤ d.S) (hKA : d.K ≤ normalizer (A : Set G)) :
    ∃ P : Sylow 2 (alternatingGroup (Fin 5)),
      (A.subgroupOf d.S).map
        ((d.SQuotientEquiv h).toMonoidHom.comp (QuotientGroup.mk' (d.R.subgroupOf d.S))) =
      (P : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype := by
  have hI := (d.elementary_eleven_symmetric_image h A hc hZA hAS hKA).2.2.2
  have hle := d.elementary_eleven_image_le_alternating h A hc hZA hAS hKA
  let B := (d.symmetricImage h A).subgroupOf (alternatingGroup (Fin 5))
  have hB : Nat.card B = 4 := (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hI
  let P : Sylow 2 (alternatingGroup (Fin 5)) := Sylow.ofCard B (by
    rw [hB,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel)
  exact ⟨P,(map_subgroupOf_eq_of_le hle).symm⟩

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
