module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.InnerEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Radicals
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# Comparing the characteristic replacement with the original radical

Write D for the replacement image under the original symplectic marking,
R₀ for the original radical image, and B = O₂(N(D)). Positive-distance
inner control and MS3 prove D is nontrivial. The ORIGINAL odd-index witness
normalizes D; hence N(D) has odd index and D ≤ B ≤ R₀. Its odd index also
makes B radical. The concrete symplectic radical classification identifies
B as a point core, plane core, or Sylow subgroup. Cardinalities give B = R₀
unless R₀ is Sylow.

The constructed projection from the literal replacement overgroup has
kernel exactly O₂ and agrees with the supplied component quotient marking.
It sends the actual replacement radical to D and transports its full
normalizer core to B. Thus the comparison retains the original odd-index
witness and every kernel; it does not assert an odd-index witness for the
replacement. The remaining saturation D = B and the field restriction
are not consequences claimed by this module.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7), printed pp.872--877;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

/-- The replacement has nontrivial component image: otherwise inner control
would make it the normal two-core, contrary to MS3. -/
theorem replacement_marked_radical_ne_bot
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    (d.ambient.subgroupOf K).map (componentProjection h) ≠ ⊥ := by
  intro hz
  have hk : d.ambient.subgroupOf K ≤ pCore 2 K := by
    rw [←componentProjection_kernel h]
    intro k hk
    exact hz.le (mem_map_of_mem (componentProjection h) hk)
  have hDQ : d.radical ≤ pCore 2 d.overgroup := by
    intro x hx
    have hx' : x ∈ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup :=
      (replacement_inner_of_positive h d g hb).symm ▸ mem_top x
    obtain ⟨k,hkK,q,hq,he⟩ := mem_sup_of_normal_right.mp hx'
    have hkD : k ∈ d.radical := by
      have hh := d.radical.mul_mem hx (d.radical.inv_mem (replacement_core_le h d hq))
      simpa only [←he,mul_inv_cancel_right] using hh
    have hkQ : k ∈ pCore 2 d.overgroup := by
      have hk' : (⟨k.val,hkK⟩ : K) ∈ pCore 2 K := hk hkD
      have hm : k.val ∈ K.pCoreIn 2 := mem_map_of_mem K.subtype hk'
      have hc : K.pCoreIn 2 ≤ pCore 2 H := by
        let := h.component_normal
        rw [pCoreIn,pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal,
          map_comap_eq,range_subtype]
        exact inf_le_right
      let := h.component_normal
      rw [d.core_eq_of_sup (original_sup h)]
      exact hc hm
    exact he ▸ (pCore 2 d.overgroup).mul_mem hkQ hq
  have hD : d.radical = pCore 2 d.overgroup :=
    le_antisymm hDQ (replacement_core_le h d)
  have hn : d.radical.Normal := hD ▸ inferInstance
  have htop : (⊤ : Subgroup d.radical) = ⊥ :=
    (replacement_characteristic h d).eq_bot_of_normal ⊤ (by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hn)
  apply replacement_ne_bot h d
  have hh := congrArg (fun A : Subgroup d.radical => A.map d.radical.subtype) htop
  simpa only [←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hh

private theorem core_normalizer_of_odd_index {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hodd : Odd A.index) :
    (normalizer (A.pCoreIn 2 : Set G)).pCoreIn 2 = A.pCoreIn 2 := by
  let N := normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hi : Odd (A.subgroupOf N).index :=
    hodd.of_dvd_nat (relIndex_dvd_index_of_le hAN)
  have hm := map_mono (f := N.subtype)
    (pCore_le_map_pCore_of_prime_not_dvd_index (A.subgroupOf N) hi.not_two_dvd_nat)
  change N.pCoreIn 2 ≤ ((A.subgroupOf N).pCoreIn 2).map N.subtype at hm
  rw [pCoreIn_subgroupOf 2 A N hAN,
    map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans hAN)] at hm
  apply le_antisymm hm
  have hl : (A.pCoreIn 2).subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance,(isPGroup_pCoreIn 2 A).of_equiv
      (subgroupOfEquivOfLe (A.pCoreIn 2).le_normalizer).symm⟩
  have hl' := map_mono (f := N.subtype) hl
  rwa [map_subgroupOf_eq_of_le (A.pCoreIn 2).le_normalizer] at hl'

omit [CharP F 2] in
/-- The original witness gives odd index to the full normalizer of D. -/
theorem replacement_marked_normalizer_odd :
    Odd (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
      Set (Sp F))).index := by
  obtain ⟨A,_,hodd,_,hnorm⟩ := original_marked_witness h d
  exact hodd.of_dvd_nat (index_dvd_of_le hnorm)

omit [CharP F 2] in
/-- The full normalizer core lies between the replacement and original images. -/
theorem replacement_marked_normalizer_core_bounds :
    let D := (d.ambient.subgroupOf K).map (componentProjection h)
    D ≤ (normalizer (D : Set (Sp F))).pCoreIn 2 ∧
      (normalizer (D : Set (Sp F))).pCoreIn 2 ≤
        (R.subgroupOf K).map (componentProjection h) := by
  dsimp only
  let D := (d.ambient.subgroupOf K).map (componentProjection h)
  let N := normalizer (D : Set (Sp F))
  have hp : IsPGroup 2 D := by
    apply IsPGroup.map
    exact (h.radical.isPGroup.to_subgroup d.subgroup).map R.subtype |>.comap_subtype
  constructor
  · exact le_map_pCore_normalizer hp
  · obtain ⟨A,_,hodd,hcore,hAN⟩ := original_marked_witness h d
    have hi : Odd (A.subgroupOf N).index :=
      hodd.of_dvd_nat (relIndex_dvd_index_of_le hAN)
    have hh := map_mono (f := N.subtype)
      (pCore_le_map_pCore_of_prime_not_dvd_index (A.subgroupOf N) hi.not_two_dvd_nat)
    change N.pCoreIn 2 ≤ ((A.subgroupOf N).pCoreIn 2).map N.subtype at hh
    rw [pCoreIn_subgroupOf 2 A N hAN,
      map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans hAN),hcore] at hh
    exact hh

/-- The nontrivial normalizer core is itself radical, using its odd-index witness. -/
theorem replacement_marked_normalizer_core_isPRadical
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    ((normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
      Set (Sp F))).pCoreIn 2).IsPRadical 2 := by
  refine ⟨?_,core_normalizer_of_odd_index _ (replacement_marked_normalizer_odd h d)⟩
  intro hz
  exact replacement_marked_radical_ne_bot h d g hb
    (le_bot_iff.mp ((replacement_marked_normalizer_core_bounds h d).1.trans_eq hz))

include h in
omit [Finite H] in
private theorem radical_alternatives (B : Subgroup (Sp F)) (hB : B.IsPRadical 2) :
    (∃ u : Sp F,
      (B.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∧
        (normalizer (B : Set (Sp F))).map (MulAut.conj u).toMonoidHom = pointParabolic) ∨
      (B.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient ∧
        (normalizer (B : Set (Sp F))).map (MulAut.conj u).toMonoidHom = planeParabolic)) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = B := by
  rcases radical_normalizer_parabolic_or_sylow B hB h.field_card
    (by have := h.nonbinary; omega) with ⟨u,hu⟩ | hs
  · left
    refine ⟨u,?_⟩
    have hc := map_pCoreIn_of_injective 2 (normalizer (B : Set (Sp F)))
      (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
    change ((normalizer (B : Set (Sp F))).pCoreIn 2).map _ = _ at hc
    have hcB : (normalizer (B : Set (Sp F))).pCoreIn 2 = B := hB.2
    rw [hcB] at hc
    rcases hu with hu | hu
    · refine Or.inl ⟨?_,hu⟩
      rw [hu] at hc
      exact hc.trans (pointParabolic_core_map_eq_radical h.field_card h.nonbinary)
    · refine Or.inr ⟨?_,hu⟩
      rw [hu] at hc
      exact hc.trans (planeParabolic_core_map_eq_radical h.field_card h.nonbinary)
  · exact Or.inr hs

/-- The exact symplectic alternatives apply to B = O₂(N(D)), with its marking. -/
theorem replacement_marked_normalizer_core_alternatives
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    let B := (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
      Set (Sp F))).pCoreIn 2
    (∃ u : Sp F,
      (B.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∧
        (normalizer (B : Set (Sp F))).map (MulAut.conj u).toMonoidHom = pointParabolic) ∨
      (B.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient ∧
        (normalizer (B : Set (Sp F))).map (MulAut.conj u).toMonoidHom = planeParabolic)) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = B :=
  radical_alternatives h _ (replacement_marked_normalizer_core_isPRadical h d g hb)

private theorem parabolic_radical_card (B : Subgroup (Sp F))
    (hB : ∃ u : Sp F, B.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∨
      B.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient) :
    Nat.card B = Nat.card F^3 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨u,hu⟩ := hB
  have hc : Nat.card (B.map (MulAut.conj u).toMonoidHom) = Nat.card B :=
    card_map_of_injective (MulAut.conj u).injective
  rw [←hc]
  rcases hu with hu | hu
  · rw [hu]
    exact SymplecticConjugatePair.card_pointRadical
  · rw [hu]
    exact SymplecticConjugatePair.card_planeRadical

include h in
omit [Finite H] [CharP F 2] in
private theorem sylow_card (S : Sylow 2 (Sp F)) : Nat.card S = Nat.card F^4 := by
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq (Sp F) S
    (unipotentSylow h.field_card (by have := h.nonbinary; omega))
  have he : (S : Subgroup (Sp F)).map (MulAut.conj u).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hu
  have hc := congrArg (fun A : Subgroup (Sp F) => Nat.card A) he
  rw [card_map_of_injective (MulAut.conj u).injective] at hc
  exact hc.trans card_unipotent

include h in
omit [Finite H] in
private theorem radical_card_ge_cube (B : Subgroup (Sp F)) (hB : B.IsPRadical 2) :
    Nat.card F^3 ≤ Nat.card B := by
  rcases radical_alternatives h B hB with ⟨u,hu⟩ | ⟨S,hS⟩
  · exact (parabolic_radical_card B ⟨u,hu.elim (Or.inl ∘ And.left)
      (Or.inr ∘ And.left)⟩).ge
  · rw [←hS,sylow_card h S]
    exact Nat.pow_le_pow_right (Nat.card_pos (α := F)) (by decide)

/-- If the original image is parabolic, its order forces B to equal it.
The original Sylow case remains an explicit alternative. -/
theorem replacement_marked_normalizer_core_eq_original_or_sylow
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
      Set (Sp F))).pCoreIn 2 = (R.subgroupOf K).map (componentProjection h) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h) := by
  rcases original_marked_radical_alternatives h d with ⟨u,hu⟩ | hS
  · left
    apply eq_of_le_of_card_ge (replacement_marked_normalizer_core_bounds h d).2
    rw [parabolic_radical_card _ ⟨u,hu.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left)⟩]
    exact radical_card_ge_cube h _ (replacement_marked_normalizer_core_isPRadical h d g hb)
  · exact Or.inr hS

/-- The whole replacement maps onto the specified symplectic model.
On the component this is the original marking, and the radical image is D. -/
theorem exists_replacement_marked_projection
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    ∃ f : d.overgroup →* Sp F, Function.Surjective f ∧ f.ker = pCore 2 d.overgroup ∧
      (∀ k : K.subgroupOf d.overgroup,
        f k = componentProjection h (subgroupOfEquivOfLe le_sup_left k)) ∧
      d.radical.map f = (d.ambient.subgroupOf K).map (componentProjection h) := by
  let π := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map π
  have hinner := replacement_inner_of_positive h d g hb
  have htop : C = ⊤ := by
    have hpre : C.comap π = ⊤ := by
      rw [show C = (K.subgroupOf d.overgroup).map π from rfl,comap_map_eq,
        QuotientGroup.ker_mk']
      exact hinner
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    exact map_top_of_surjective π (QuotientGroup.mk'_surjective _)
  let q := π.codRestrict C (fun x => htop ▸ mem_top (π x))
  have hq : Function.Surjective q := by
    intro c
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 d.overgroup) c.val
    exact ⟨x,Subtype.ext hx⟩
  let e : C ≃* Sp F :=
    (cComponentTwoCoreQuotientEquiv (replacement_component h d)).symm.trans
      (replacementQuotientEquiv h d)
  let f := e.toMonoidHom.comp q
  have hfk : f.ker = pCore 2 d.overgroup := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    have he : q.ker = π.ker := by
      ext x
      exact Subtype.ext_iff
    rw [he,QuotientGroup.ker_mk']
  have hmark (k : K.subgroupOf d.overgroup) :
      f k = componentProjection h (subgroupOfEquivOfLe le_sup_left k) := by
    change replacementQuotientEquiv h d
      ((cComponentTwoCoreQuotientEquiv (replacement_component h d)).symm
        (π.subgroupMap (K.subgroupOf d.overgroup) k)) = _
    exact congrArg (replacementQuotientEquiv h d)
      ((cComponentTwoCoreQuotientEquiv (replacement_component h d)).symm_apply_apply
        (QuotientGroup.mk' _ k))
  refine ⟨f,e.surjective.comp hq,hfk,hmark,?_⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hx' : x ∈ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup :=
      hinner.symm ▸ mem_top x
    obtain ⟨k,hk,y,hy,he⟩ := mem_sup_of_normal_right.mp hx'
    have hkD : k ∈ d.radical := by
      have hh := d.radical.mul_mem hx (d.radical.inv_mem (replacement_core_le h d hy))
      simpa only [←he,mul_inv_cancel_right] using hh
    refine ⟨⟨k.val,hk⟩,hkD,?_⟩
    have hyf : f y = 1 := by
      change y ∈ f.ker
      rwa [hfk]
    rw [←he,map_mul,hyf,mul_one]
    exact (hmark ⟨k,hk⟩).symm
  · rintro _ ⟨k,hk,rfl⟩
    let k' : K.subgroupOf d.overgroup := ⟨⟨k.val,mem_sup_left k.property⟩,k.property⟩
    exact ⟨k'.val,hk,hmark k'⟩

/-- Apply the odd-index comparison to the actual replacement projection,
retaining its kernel and its agreement with the original component marking. -/
theorem replacement_radical_normalizer_core_comparison
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    ∃ f : d.overgroup →* Sp F, Function.Surjective f ∧ f.ker = pCore 2 d.overgroup ∧
      (∀ k : K.subgroupOf d.overgroup,
        f k = componentProjection h (subgroupOfEquivOfLe le_sup_left k)) ∧
      d.radical.map f ≠ ⊥ ∧
      Odd (normalizer (d.radical.map f : Set (Sp F))).index ∧
      ((normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2).IsPRadical 2 ∧
      d.radical.map f ≤ (normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2 ∧
      (normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2 ≤
        (R.subgroupOf K).map (componentProjection h) ∧
      ((normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2 =
          (R.subgroupOf K).map (componentProjection h) ∨
        ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
          (R.subgroupOf K).map (componentProjection h)) := by
  obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g hb
  refine ⟨f,hf,hk,hm,?_⟩
  rw [he]
  exact ⟨replacement_marked_radical_ne_bot h d g hb,replacement_marked_normalizer_odd h d,
    replacement_marked_normalizer_core_isPRadical h d g hb,
    (replacement_marked_normalizer_core_bounds h d).1,
    (replacement_marked_normalizer_core_bounds h d).2,
    replacement_marked_normalizer_core_eq_original_or_sylow h d g hb⟩

include h in
omit [Finite F] [CharP F 2] in
/-- Before projection, the normalizer core is bounded by the original radical
restricted to the replacement overgroup; no replacement radicality is assumed. -/
theorem replacement_normalizer_core_bounds :
    d.radical ≤ (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 ∧
      (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 ≤ R.subgroupOf d.overgroup := by
  refine ⟨le_map_pCore_normalizer (replacement_isPGroup h d),?_⟩
  obtain ⟨A,_,_,_,_,hodd,hcore,_,hAN⟩ := original_witness_restricted h d
  let N := normalizer (d.radical : Set d.overgroup)
  let A' := A.subgroupOf d.overgroup
  have hi : Odd (A'.subgroupOf N).index :=
    hodd.of_dvd_nat (relIndex_dvd_index_of_le hAN)
  have hh := map_mono (f := N.subtype)
    (pCore_le_map_pCore_of_prime_not_dvd_index (A'.subgroupOf N) hi.not_two_dvd_nat)
  change N.pCoreIn 2 ≤ ((A'.subgroupOf N).pCoreIn 2).map N.subtype at hh
  rw [pCoreIn_subgroupOf 2 A' N hAN,
    map_subgroupOf_eq_of_le ((A'.pCoreIn_le 2).trans hAN),hcore] at hh
  exact hh

include h in
omit [Finite F] [CharP F 2] in
/-- The full relative normalizer core maps to B through the exact O₂ kernel. -/
theorem replacement_normalizer_core_map
    (f : d.overgroup →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 d.overgroup) :
    ((normalizer (d.radical : Set d.overgroup)).pCoreIn 2).map f =
      (normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2 := by
  let : Finite (Sp F) := Finite.of_surjective f hf
  have hN : (normalizer (d.radical : Set d.overgroup)).map f =
      normalizer (d.radical.map f : Set (Sp F)) := by
    have he : (normalizer (d.radical.map f : Set (Sp F))).comap f =
        normalizer (d.radical : Set d.overgroup) := by
      rw [comap_normalizer_eq_of_surjective _ hf,
        comap_map_eq_self (hk.trans_le (replacement_core_le h d))]
    rw [←he,map_comap_eq_self_of_surjective hf]
  rw [map_pCoreIn_of_ker_isPGroup f (hk ▸ pCore_isPGroup),hN]

include h in
omit [Finite F] [CharP F 2] in
/-- The still-needed radicality equality is equivalent on the literal quotient.
This is a transport criterion, not an assertion of either equality. -/
theorem replacement_radical_saturation_iff
    (f : d.overgroup →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 d.overgroup) :
    (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical ↔
      (normalizer (d.radical.map f : Set (Sp F))).pCoreIn 2 = d.radical.map f := by
  rw [←replacement_normalizer_core_map h d f hf hk]
  constructor
  · exact congrArg (fun A : Subgroup d.overgroup => A.map f)
  · intro he
    have hh := congrArg (fun A : Subgroup (Sp F) => A.comap f) he
    rw [comap_map_eq_self ((hk.trans_le (replacement_core_le h d)).trans
        (replacement_normalizer_core_bounds h d).1),
      comap_map_eq_self (hk.trans_le (replacement_core_le h d))] at hh
    exact hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
